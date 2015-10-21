import scala.util.parsing.combinator._
import java.io.FileReader


object VCGen {

  var cnt = 0
  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp

  /* Assertions */
  type Assertion = BoolExp
  type PreCondition = BoolExp
  type PostCondition = BoolExp

  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, invs: List[Assertion], body: Block) extends Statement


  /* Complete programs. */
  type Program = Product4[String, List[PreCondition], List[PostCondition], Block]

  object ImpParser extends RegexParsers {
    /* General helpers. */
    def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }
    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for BoolExp. */
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" | comp ^^ { BCmp(_) } | "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> (bexp ~ rep("inv" ~> assn) ) <~ "do") ~ (block <~ "end") ^^ {
        case c ~ a ~ b => While(c, a, b)
      }

    /* Parsing for Assertion. */
    def assn : Parser[Assertion] = bexp
    def pre : Parser[PreCondition] = bexp
    def post : Parser[PostCondition] = bexp

    /* Parsing for Program. */
    def prog   : Parser[Program] =
      ("program" ~> pvar ~ rep("pre" ~> pre) ~ rep("post" ~> post)<~ "is") ~ (block <~ "end") ^^ {
        case n ~ pr ~ po ~ b => (n, pr, po, b)
      }
  }

  /*************** Gaurded Command Language ****************/

  /* Comamnds */
  trait Command

  case class Assume(b: BoolExp) extends Command
  case class Assert(b: BoolExp) extends Command
  case class Havoc(x: Var) extends Command
  case class Compose(c1: Command, c2: Command) extends Command
  case class Or(c1: Command, c2: Command) extends Command

  def translate(p: Program): Command = {
    return translateBlock(p._4)
  }

  def translateBlock(b: Block): Command = {
    //GC(c1; c2) =GC(c1) ; GC(c2)
    //allVars(b).contains(Var("fresh_"i+*)
    if(b.isEmpty){
      return Assume(BCmp(Num(42),"=",Num(42)))
    }
    else {
      val listCmds = b.map (x => translateStatement(x))
      return composeL(listCmds)
    }
  }

  def composeL(cs: List[Command]) : Command = {
    return (cs.tail).foldLeft (cs.head) (Compose)
  }

  def replace(f: Var, old: Var, e:ArithExp): ArithExp = {
    e match {
      case Num(v) => Num(v)
      case Var(name) => if (name == old){ f } else Var(name)
      case Add(l,r) => Add(replace(f,old,l),replace(f,old,r))
      case Sub(l,r) => Sub(replace(f,old,l),replace(f,old,r))
      case Mul(l,r) => Mul(replace(f,old,l),replace(f,old,r))
      case Div(l,r) => Div(replace(f,old,l),replace(f,old,r))
      case Mod(l,r) => Mod(replace(f,old,l),replace(f,old,r))
      case Parens(a) => Parens(replace(f,old,a))
    }
  }

  def allVars_Statement(s: Statement) : List[Var] = {
    s match {
      case Assign(x,e) =>
        return List(Var(x))
      case If(c,th,el) =>
        return allVars(th) ++ allVars(el)
      case While(c,i,b) =>
        return allVars(b)
    }
  }

  def allVars(b: Block) : List[Var] = {
    return (b.map (allVars_Statement)).flatten.distinct
  }

  def translateStatement(s : Statement) : Command = {
    s match {
      //GC(x:=e) = assume tmp = x; havoc x; assume (x = e[tmp/x]) where temp is fresh
      case Assign(x,e) =>
        var freshVar = Var("fresh_"+cnt)
        cnt=cnt+1
        var xVar = Var(x)
        var c1 = Assume(BCmp((freshVar,"=",xVar)))
        var c2 = Havoc(xVar)
        var c3 = Assume(BCmp((xVar,"=",replace(freshVar,xVar,e))))
        return composeL(List(c1,c2,c3))

      //GC(if b then c1 else c2) =(assume b; GC(c1)) [] (assume :b; GC(c2))
      case If(c,th,el) =>
        var l = Compose(Assume (c),translateBlock(th))
        var r = Compose(Assume (BNot (c)),translateBlock(el))
        return Or(l, r)

      //GC({I} while b do c) = ?
      case While(c,i,b) =>
        var c1 =
          if (i.isEmpty) Assert(BCmp((Num(43),"=",Num(43))))
          else composeL (i.map (x => Assert(x)))
        //var c2 = allVars b
        var c3 = composeL ((allVars(b).map (x => Havoc(x))))
        if (i.isEmpty) {c1 = Assume(BCmp((Num(43),"=",Num(43))))}
        else c3 = composeL (i.map (x => Assume(x)))
        var c4p1 = composeL (List(Assume(c),translateBlock(b),c1,Assume(BCmp(Num(44),"=",Num(45)))))
        var c4p2 = Assume(BNot(c))
        var c4 = Or(c4p1,c4p2)
        return composeL (List(c1,c3,c4))
    }
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    var progAST = parseAll(prog, reader)
    var gaurdedCmd = translate(progAST.get) 
    println(gaurdedCmd)

  }
}
