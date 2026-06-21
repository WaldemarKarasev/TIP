package tip.analysis

import tip.ast._
import tip.solvers._
import tip.types._
import tip.ast.AstNodeData._
import tip.util.{Log, TipProgramException}
import AstOps._

import scala.collection.mutable

/**
  * Unification-based type analysis.
  * The analysis associates a [[tip.types.Type]] with each variable declaration and expression node in the AST.
  * It is implemented using [[tip.solvers.UnionFindSolver]].
  *
  * To novice Scala programmers:
  * The parameter `declData` is declared as "implicit", which means that invocations of `TypeAnalysis` obtain its value implicitly:
  * The call to `new TypeAnalysis` in Tip.scala does not explicitly provide this parameter, but it is in scope of
  * `implicit val declData: TypeData = new DeclarationAnalysis(programNode).analyze()`.
  * The TIP implementation uses implicit parameters many places to provide easy access to the declaration information produced
  * by `DeclarationAnalysis` and the type information produced by `TypeAnalysis`.
  * For more information about implicit parameters in Scala, see [[https://docs.scala-lang.org/tour/implicit-parameters.html]].
  */
class TypeAnalysis(program: AProgram)(implicit declData: DeclarationData) extends DepthFirstAstVisitor[Unit] with Analysis[TypeData] {

  val log = Log.logger[this.type]()

  val solver = new UnionFindSolver[Type]

  implicit val allFieldNames: List[String] = program.appearingFields.toList.sorted

  log.info(allFieldNames.toString() + "size:" + allFieldNames.size)
  log.info("program.funcs.size:" + program.funs.size)
  /**
    * @inheritdoc
    */
  def analyze(): TypeData = {

    // generate the constraints by traversing the AST and solve them on-the-fly
    try {
      visit(program, ())
    } catch {
      case e: UnificationFailure =>
        throw new TipProgramException(s"Type error: ${e.getMessage}")
    }

    // check for accesses to absent record fields
    new DepthFirstAstVisitor[Unit] {
      visit(program, ())

      override def visit(node: AstNode, arg: Unit): Unit = {
        node match {
          case ac: AFieldAccess =>
            if (solver.find(node).isInstanceOf[AbsentFieldType.type])
              throw new TipProgramException(s"Type error: Reading from absent field ${ac.field} ${ac.loc.toStringLong}")
          case as: AAssignStmt =>
            as.left match {
              case dfw: ADirectFieldWrite =>
                if (solver.find(as.right).isInstanceOf[AbsentFieldType.type])
                  throw new TipProgramException(s"Type error: Writing to absent field ${dfw.field} ${dfw.loc.toStringLong}")
              case ifw: AIndirectFieldWrite =>
                if (solver.find(as.right).isInstanceOf[AbsentFieldType.type])
                  throw new TipProgramException(s"Type error: Writing to absent field ${ifw.field} ${ifw.loc.toStringLong}")
              case _ =>
            }
          case _ =>
        }
        visitChildren(node, ())
      }
    }

    var ret: TypeData = Map()

    // close the terms and create the TypeData
    new DepthFirstAstVisitor[Unit] {
      val sol: Map[Var[Type], Term[Type]] = solver.solution()
      log.info(s"Solution (not yet closed):\n${sol.map { case (k, v) => s"  \u27E6$k\u27E7 = $v" }.mkString("\n")}")
      val freshvars: mutable.Map[Var[Type], Var[Type]] = mutable.Map()
      visit(program, ())

      // extract the type for each identifier declaration and each non-identifier expression
      override def visit(node: AstNode, arg: Unit): Unit = {
        node match {
          case _: AIdentifier =>
          case _: ADeclaration | _: AExpr =>
            ret += node -> Some(TipTypeOps.close(VarType(node), sol, freshvars).asInstanceOf[Type])
          case _ =>
        }
        visitChildren(node, ())
      }
    }

    log.info(s"Inferred types:\n${ret.map { case (k, v) => s"  \u27E6$k\u27E7 = ${v.get}" }.mkString("\n")}")
    // log.info(s"Classes:\n${solver.unifications()}")
    ret
  }

  /**
    * Generates the constraints for the given sub-AST.
    * @param node the node for which it generates the constraints
    * @param arg unused for this visitor
    */
  def visit(node: AstNode, arg: Unit): Unit = {
    log.verb(s"Visiting ${node.getClass.getSimpleName} at ${node.loc}")
    node match {
      case program: AProgram =>        
      case _: ANumber => unify(VarType(node), IntType())
      case _: AInput => unify(VarType(node), IntType())
      case is: AIfStmt => unify(VarType(is.guard), IntType())
      case os: AOutputStmt => unify(VarType(os.exp), IntType())
      case ws: AWhileStmt => unify(VarType(ws.guard), IntType())
      case as: AAssignStmt =>
        as.left match {
          case id: AIdentifier => 
            log.warn(s"id:$id")
            unify(id, as.right)
          case dw: ADerefWrite => unify(dw.exp, PointerType(as.right))
          case dfw: ADirectFieldWrite => 
            log.warn(s"Unify ADirectFieldWrite:$dfw\n " +
              s"l:${as.left}, r:${as.right}\n" +
              s"id:${dfw.id}, field:${dfw.field}\n" +
              s"as:$as")
              unify(dfw.id, RecordType(allFieldNames.map { f =>
                if (f == dfw.field) Type.ast2typevar(as.right) else FreshVarType()
              }))

          case ifw: AIndirectFieldWrite => 
            log.warn(s"Unify AIndirectFieldWrite:$ifw\n " +
              s"l:${as.left}, r:${as.right}\n" +
              s"expr:${ifw.exp}, field:${ifw.field}\n" +
              s"as:$as")
              var r_t = RecordType(allFieldNames.map { f =>
                if (f == ifw.field) Type.ast2typevar(as.right) else FreshVarType()
              })
              unify(ifw.exp, PointerType(r_t))

        }
      case bin: ABinaryOp =>
        bin.operator match {
          case Eqq => 
            unify(bin.left, bin.right)
            unify(VarType(node), IntType())
          case _ =>
            unify(bin.left, bin.right)
            unify(bin.left, node)
            unify(VarType(node), IntType())
        }
      case un: AUnaryOp =>
        un.operator match {
          case DerefOp => unify(un.subexp, PointerType(VarType(un)))
        }
      case alloc: AAlloc => unify(VarType(alloc), PointerType(alloc.exp))
      case ref: AVarRef => unify(VarType(ref), PointerType(VarType(ref.id)))
      case _: ANull => unify(VarType(node), PointerType(FreshVarType()))
      case fun: AFunDeclaration =>
          if (fun.name == "main") {
            unify(fun.stmts.ret.exp, IntType())
            fun.params.map(p => unify(VarType(p), IntType()))
          }
          unify(VarType(fun), FunctionType(fun.params.map(p => VarType(p)), fun.stmts.ret.exp))

      case call: ACallFuncExpr => 
        unify(call.targetFun, FunctionType(call.args.map(arg => arg), VarType(call)))

      case _: AReturnStmt => 
      
      case rec: ARecord =>
        val fieldmap = rec.fields.foldLeft(Map[String, Term[Type]]()) { (a, b) =>
          a + (b.field -> b.exp)
        }
        unify(rec, RecordType(allFieldNames.map { f =>
          fieldmap.getOrElse(f, AbsentFieldType)
        }))
      case ac: AFieldAccess =>
        unify(ac.record, RecordType(allFieldNames.map { f =>
          if (f == ac.field) VarType(ac) else FreshVarType()
        }))
      case _ =>
    }
    visitChildren(node, ())
  }

  private def unify(t1: Term[Type], t2: Term[Type]): Unit = {
    log.info(s"Generating constraint $t1 = $t2")
    solver.unify(t1, t2)
    // log.info(s"unifications after unify()\n${solver.unifications()
    //                                         .map { case (rep, terms) => s"$rep: ${terms.mkString(", ")}" }
    //                                         .mkString("\n")}")
  }
}
