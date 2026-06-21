package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.cfg.IntraproceduralProgramCfg
import tip.lattices.LatticeWithOps

// var size analysis lattice
object VariableSizeLattice extends LatticeWithOps {

  sealed trait Size

  case object Bot extends Size {
    override def toString: String = "Bot"
  }

  case object BoolSize extends Size {
    override def toString: String = "bool"
  }

  case object ByteSize extends Size {
    override def toString: String = "byte"
  }

  case object CharSize extends Size {
    override def toString: String = "char"
  }

  case object IntSize extends Size {
    override def toString: String = "int"
  }

  case object BigIntSize extends Size {
    override def toString: String = "bigint"
  }

  case object AnySize extends Size {
    override def toString: String = "any"
  }

  type Element = Size

  val bottom: Element = Bot

  override val top: Element = AnySize

  private val ByteMin = BigInt(-128)
  private val ByteMax = BigInt(127)

  private val CharMin = BigInt(0)
  private val CharMax = BigInt(65535)

  private val IntMin = BigInt(Int.MinValue)
  private val IntMax = BigInt(Int.MaxValue)

  def lub(x: Element, y: Element): Element =
    (x, y) match {
      case (a, b) if a == b => a

      case (Bot, a) => a
      case (a, Bot) => a

      case (AnySize, _) => AnySize
      case (_, AnySize) => AnySize

      case (BigIntSize, _) => BigIntSize
      case (_, BigIntSize) => BigIntSize

      case (BoolSize, a) => a
      case (a, BoolSize) => a

      case (ByteSize, CharSize) => IntSize
      case (CharSize, ByteSize) => IntSize

      case (ByteSize, IntSize) => IntSize
      case (IntSize, ByteSize) => IntSize

      case (CharSize, IntSize) => IntSize
      case (IntSize, CharSize) => IntSize
    }

  private def rangeOf(x: Element): Option[(BigInt, BigInt)] =
    x match {
      case BoolSize => Some((BigInt(0), BigInt(1)))
      case ByteSize => Some((ByteMin, ByteMax))
      case CharSize => Some((CharMin, CharMax))
      case IntSize => Some((IntMin, IntMax))
      case _ => None
    }

  private def sizeOfRange(low: BigInt, high: BigInt): Element =
    if (low >= 0 && high <= 1)
      BoolSize
    else if (low >= ByteMin && high <= ByteMax)
      ByteSize
    else if (low >= CharMin && high <= CharMax)
      CharSize
    else if (low >= IntMin && high <= IntMax)
      IntSize
    else
      BigIntSize

  private def numericBinOp(
      a: Element,
      b: Element
  )(op: ((BigInt, BigInt), (BigInt, BigInt)) => (BigInt, BigInt)): Element =
    (a, b) match {
      case (Bot, _) => Bot
      case (_, Bot) => Bot

      case (AnySize, _) => AnySize
      case (_, AnySize) => AnySize

      case (BigIntSize, _) => BigIntSize
      case (_, BigIntSize) => BigIntSize

      case _ =>
        val r1 = rangeOf(a).get
        val r2 = rangeOf(b).get
        val (low, high) = op(r1, r2)
        sizeOfRange(low, high)
    }

  def num(i: Int): Element =
    sizeOfRange(BigInt(i), BigInt(i))

  def plus(a: Element, b: Element): Element =
    numericBinOp(a, b) {
      case ((l1, h1), (l2, h2)) =>
        (l1 + l2, h1 + h2)
    }

  def minus(a: Element, b: Element): Element =
    numericBinOp(a, b) {
      case ((l1, h1), (l2, h2)) =>
        (l1 - h2, h1 - l2)
    }

  def times(a: Element, b: Element): Element =
    numericBinOp(a, b) {
      case ((l1, h1), (l2, h2)) =>
        val values = List(
          l1 * l2,
          l1 * h2,
          h1 * l2,
          h1 * h2
        )
        (values.min, values.max)
    }

  def div(a: Element, b: Element): Element =
    (a, b) match {
      case (Bot, _) => Bot
      case (_, Bot) => Bot

      case (AnySize, _) => AnySize
      case (_, AnySize) => AnySize

      case (BigIntSize, _) => BigIntSize
      case (_, BigIntSize) => BigIntSize

      case _ =>
        val r2 = rangeOf(b).get
        val (l2, h2) = r2

        if (l2 == 0 && h2 == 0) {
          Bot
        } else if (l2 <= 0 && h2 >= 0) {
          BigIntSize
        } else {
          numericBinOp(a, b) {
            case ((l1, h1), (l2, h2)) =>
              val values = List(
                l1 / l2,
                l1 / h2,
                h1 / l2,
                h1 / h2
              )
              (values.min, values.max)
          }
        }
    }

  def eqq(a: Element, b: Element): Element =
    (a, b) match {
      case (Bot, _) => Bot
      case (_, Bot) => Bot
      case _ => BoolSize
    }

  def gt(a: Element, b: Element): Element =
    (a, b) match {
      case (Bot, _) => Bot
      case (_, Bot) => Bot
      case _ => BoolSize
    }
}

// var size analysis
object VariableSizeAnalysis {

  object Intraprocedural {

    class SimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisSimpleSolver(cfg, VariableSizeLattice)

    class WorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolver(cfg, VariableSizeLattice)

    class WorklistSolverWithReachability(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VariableSizeLattice)
  }
}