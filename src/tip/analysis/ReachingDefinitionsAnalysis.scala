package tip.analysis

import tip.ast._
import tip.ast.AstNodeData.{AstNodeWithDeclaration, DeclarationData}
import tip.cfg._
import tip.lattices._
import tip.solvers._

import scala.collection.immutable.Set

/**
  * Base class for reaching definitions analysis.
  */
abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends FlowSensitiveAnalysis(true) {

  case class Definition(variable: ADeclaration, node: AstNode) {
    override def toString: String =
      node match {
        case d: AIdentifierDeclaration => s"var ${d.name}"
        case s => s.toString
      }
  }

  val lattice: MapLattice[CfgNode, PowersetLattice[Definition]] =
    new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  private def removeDefs(
      s: lattice.sublattice.Element,
      x: ADeclaration
  ): lattice.sublattice.Element =
    s.filterNot(_.variable == x)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunEntryNode =>
        lattice.sublattice.bottom

      case r: CfgStmtNode =>
        r.data match {
          case varr: AVarStmt =>
            s union varr.declIds.map(d => Definition(d, d)).toSet

          case as @ AAssignStmt(id: AIdentifier, _, _) =>
            removeDefs(s, id.declaration) + Definition(id.declaration, as)

          case as: AAssignStmt =>
            NoPointers.LanguageRestrictionViolation(s"$as not allowed", as.loc)

          case _ =>
            s
        }

      case _ =>
        s
    }
}

// fixpoint solver
class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

// worklist solver
class ReachingDefAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies