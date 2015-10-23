import scala.util.parsing.combinator._
import java.io.FileReader

object VCGen {
 
  var ctr = 0

  /**************** LOGIC *******************/
  case class Implies(asmp: BoolExp, impl: BoolExp) extends BoolExp

  def wp(cmd:Command, post:PostCondition) : BoolExp = {
    cmd match {
      case Assume(b) => Implies(b,post)
      case Assert(b) => BConj(b,post)
      case Havoc(x) => 
        var f = Var("fresh"+x+ctr)
        ctr = ctr+1
        replaceB(x,f,post)
      case Compose(c1,c2) => BParens(wp(c1, BParens(wp(c2,post))))
      case Box(c1,c2) => BConj(BParens(wp(c1,post)),BParens(wp(c2,post)))
    }
  }
  
  def conjL(cs: List[BoolExp]) : BoolExp = {
    var t = BVal(true):BoolExp
    return cs.foldLeft (t) (BConj)
  }
  
  def replaceB(x:Var, y: Var, b:BoolExp) : BoolExp = {
    b match {
      case BCmp((e1,c,e2)) => BCmp((replaceA(x,y,e1),c,replaceA(x,y,e2)))
      case BVal(v) => BVal(v)
      case BNot(e) => BNot(replaceB(x,y,e))
      case BDisj(l,r) => BDisj(replaceB(x,y,l),replaceB(x,y,r))
      case BConj(l,r) => BConj(replaceB(x,y,l),replaceB(x,y,r))
      case BParens(e) => BParens(replaceB(x,y,e))
      case Implies(a, i) => Implies(replaceB(x,y,a),replaceB(x,y,i))
    }
  }

  def allVars_B(b:BoolExp): List[String] = {
    b match {
      case BCmp((e1,c,e2)) => allVars_A(e1)++allVars_A(e2)
      case BVal(v) => return List() 
      case BNot(e) => allVars_B(e)
      case BDisj(l,r) => allVars_B(l)++allVars_B(r)
      case BConj(l,r) => allVars_B(l)++allVars_B(r)
      case BParens(e) => allVars_B(e)
      case Implies(a, i) => allVars_B(a)++allVars_B(i)
    }
  }
 
  def allVars_A(e: ArithExp): List[String] = {
    e match {
      case Num(v) => return List()
      case Var(name) => return List(name)
      case Parens(a) => allVars_A(a)
      case Add(l,r) => allVars_A(l)++allVars_A(r)
      case Sub(l,r) => allVars_A(l)++allVars_A(r)
      case Mul(l,r) => allVars_A(l)++allVars_A(r)
      case Div(l,r) => allVars_A(l)++allVars_A(r)
      case Mod(l,r) => allVars_A(l)++allVars_A(r)
    }
  }

  /******************* IMP ******************/
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
  case class BVal(v: Boolean) extends BoolExp


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

  /******************* LFGC ****************/
  /* Comamnds */
  trait Command

  case class Assume(b: BoolExp) extends Command
  case class Assert(b: BoolExp) extends Command
  case class Havoc(x: Var) extends Command
  case class Compose(c1: Command, c2: Command) extends Command
  case class Box(c1: Command, c2: Command) extends Command


  def translate(p: Program): Command = {
    var pres = Assume(conjL(p._2))
    return Compose(pres,translateBlock(p._4))
  }

  def translateBlock(b: Block): Command = {
    //GC(c1; c2) =GC(c1) ; GC(c2)
    //allVars(b).contains(Var("fresh_"i+*)
    if(b.isEmpty){
      return Assume(BVal(true))
    }
    else {
      val listCmds = b.map (x => translateStatement(x))
      return composeL(listCmds)
    }
  }

  def composeL(cs: List[Command]) : Command = {
    return (cs.tail).foldLeft (cs.head) (Compose)
  }
  
  def replaceA(f: Var, old: Var, e:ArithExp): ArithExp = {
    e match {
      case Num(v) => Num(v)
      case Var(name) => if (name == old){ f } else Var(name)
      case Parens(a) => Parens(replaceA(f,old,a))
      case Add(l,r) => Add(replaceA(f,old,l),replaceA(f,old,r))
      case Sub(l,r) => Sub(replaceA(f,old,l),replaceA(f,old,r))
      case Mul(l,r) => Mul(replaceA(f,old,l),replaceA(f,old,r))
      case Div(l,r) => Div(replaceA(f,old,l),replaceA(f,old,r))
      case Mod(l,r) => Mod(replaceA(f,old,l),replaceA(f,old,r))
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
        var freshVar = Var("fresh"+x+ctr)
        ctr=ctr+1
        var xVar = Var(x)
        var c1 = Assume(BCmp((freshVar,"=",xVar)))
        var c2 = Havoc(xVar)
        var c3 = Assume(BCmp((xVar,"=",replaceA(freshVar,xVar,e))))
        return composeL(List(c1,c2,c3))

      //GC(if b then c1 else c2) =(assume b; GC(c1)) [] (assume :b; GC(c2))
      case If(c,th,el) =>
        var l = Compose(Assume (c),translateBlock(th))
        var r = Compose(Assume (BNot (c)),translateBlock(el))
        return Box(l, r)

      //GC({I} while b do c) = ?
      case While(c,i,b) =>
        var c1 =
          if (i.isEmpty) Assert(BVal(false))
          else composeL (i.map (Assert))
        //var c2 = allVars b
        var c3 = composeL ((allVars(b).map (Havoc)))
        if (i.isEmpty) {c1 = Assume(BVal(true))}
        else c3 = composeL (i.map (Assume))
        var c4p1 = composeL (List(Assume(c),translateBlock(b),c1,Assume(BVal(false))))
        var c4p2 = Assume(BNot(c))
        var c4 = Box(c4p1,c4p2)
        return composeL (List(c1,c3,c4))
    }
  } 


  def bToString(f: BoolExp): String = {
    f match {
      case Implies(a, i) => "(=> \n "+bToString(a)+" "+bToString(i)+")" 
      case BCmp((e1,c,e2)) => "("+c+" "+aToString(e1)+" "+aToString(e2)+")"
      case BNot(b) => "(not \n"+bToString(b)+")"
      case BDisj(l,r) => "(or \n"+bToString(l)+" "+bToString(r)+")"
      case BConj(l,r) => "(and \n"+bToString(l)+" "+bToString(r)+")"
      //case BParens(b) => "("+bToString(b)+")"
      case BParens(b) => bToString(b)
      case BVal(v) => if (v) {"true"} else "false"
    }
  } 
 
  def aToString(e:ArithExp): String = {
    e match {
      case Num(v) => v.toString
      case Var(name) => name
      case Parens(a) => "("+aToString(a)+")"
      case Add(l,r) => "(+ "+aToString(l)+" "+aToString(r)+")"
      case Sub(l,r) => "(- "+aToString(l)+" "+aToString(r)+")"
      case Mul(l,r) => "(* "+aToString(l)+" "+aToString(r)+")"
      case Div(l,r) => "(/ "+aToString(l)+" "+aToString(r)+")"
      case Mod(l,r) => "(% "+aToString(l)+" "+aToString(r)+")"
    }
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    var progAST = parseAll(prog, reader)
    var gaurdedCmd = translate(progAST.get)
    var formula = wp(gaurdedCmd, conjL(progAST.get._3))
    var vars = (allVars_B(formula).distinct).map (x => println("(declare-const "+x+" Real)"))
    println("(assert "+bToString(BNot(formula))+")")

  }
}
