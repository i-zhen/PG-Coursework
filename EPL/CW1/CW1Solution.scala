import scala.collection.immutable.Set

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

object CW1Solution {
  type Variable = String
  type Env[A] = Map[Variable,A]

  // Arithmetic expressions

  abstract class Expr
  case class Num(n: Integer) extends Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
  case class Minus(e1: Expr, e2: Expr) extends Expr
  case class Times(e1: Expr, e2: Expr) extends Expr

  // Booleans
  case class Bool(n: Boolean) extends Expr
  case class Eq(e1: Expr, e2:Expr) extends Expr
  case class IfThenElse(e: Expr, e1: Expr, e2: Expr) extends Expr

   // Strings
  case class Str(s: String) extends Expr
  case class Length(e: Expr) extends Expr
  case class Index(e1: Expr, e2: Expr) extends Expr
  case class Concat(e1: Expr, e2: Expr) extends Expr

  // Variables and let-binding
  case class Var(x: Variable) extends Expr
  case class Let(x: Variable, e1: Expr, e2: Expr) extends Expr
  case class LetFun(f: Variable, arg: Variable, ty: Type, e1:Expr, e2:Expr)
      extends Expr
  case class LetRec(f: Variable, arg: Variable, xty: Type, ty: Type, e1:Expr, e2:Expr)
      extends Expr
  case class LetPair(x: Variable,y: Variable, e1:Expr, e2:Expr) extends Expr

  // Pairing
  case class Pair(e1: Expr, e2: Expr) extends Expr
  case class First(e: Expr) extends Expr
  case class Second(e: Expr) extends Expr

  // Functions
  case class Lambda(x: Variable, ty: Type, e: Expr) extends Expr
  case class Apply(e1: Expr, e2: Expr) extends Expr
  case class Rec(f: Variable, x: Variable, tyx:Type, ty: Type, e: Expr) extends Expr

  // Values
  abstract class Value
  case class NumV(n: Integer) extends Value
  case class BoolV(n: Boolean) extends Value
  case class StringV(s: String) extends Value
  case class PairV(v1: Value, v2: Value) extends Value
  case class ClosureV(env: Env[Value], x: Variable, e: Expr) extends Value
  case class RecV(env: Env[Value], f:Variable, x: Variable, e: Expr) extends Value

  // Types
  abstract class Type
  case object IntTy extends Type
  case object BoolTy extends Type
  case object StringTy extends Type
  case class PairTy(ty1: Type, ty2: Type) extends Type
  case class FunTy(ty1: Type, ty2: Type) extends Type

  // ======================================================================
  // Part 1: Syntactic transformation
  // ======================================================================

  // ======================================================================
  // Exercise 1: Capture-avoiding substitution
  // ======================================================================

  // This object provides a method to generate a "fresh" variable name
  object Gensym {

    private var id = 0
    def gensym(s: Variable): Variable = {
      val fresh_s = s + "_" + id
      id = id + 1
      fresh_s
    }
  }

  def free(e:Expr): Set[Variable] = e match {
      case Num(e) => Set.empty
      case Plus(t1,t2) => free(t1).union(free(t2))
      case Minus(t1,t2) => free(t1).union(free(t2))
      case Times(t1,t2) => free(t1).union(free(t2))

      // Booleans
      case Bool(b) => Set.empty
      case Eq(t1,t2) => free(t1).union(free(t2))
      case IfThenElse(t,t1,t2) => free(t).union(free(t1).union(free(t2)))

      // Strings
      case Str(s) => Set.empty
      case Length(e) => free(e)
      case Index(t1,t2) => free(t1).union(free(t2))
      case Concat(t1,t2) => free(t1).union(free(t2))


      // Variables + let
      case Var(y) => Set(y)
      case Let(y,t1,t2) => free(t1).union(free(t2) - y)

      // Pairs
      case Pair(t1,t2) => free(t1).union(free(t2))
      case First(e) => free(e)
      case Second(e) => free(e)

      // Functions
      case Lambda(y,a,e) => free(e) - y
      case Rec(f,y,a,b,e) => free(e) - f - y
      case Apply(t1,t2) => free(t1).union(free(t2))
  }

  def subst(e1:Expr, e2:Expr, x: Variable): Expr =
    e1 match {
      case Num(e) => Num(e)
      case Plus(t1,t2) => Plus(subst(t1,e2,x),subst(t2,e2,x))
      case Minus(t1,t2) => Minus(subst(t1,e2,x),subst(t2,e2,x))
      case Times(t1,t2) => Times(subst(t1,e2,x),subst(t2,e2,x))

      // Booleans
      case Bool(b) => Bool(b)
      case Eq(t1,t2) => Eq(subst(t1,e2,x),subst(t2,e2,x))
      case IfThenElse(t,t1,t2) =>
        IfThenElse(subst(t,e2,x),subst(t1,e2,x),subst(t2,e2,x))

      // Strings
      case Str(s) => Str(s)
      case Length(e) => Length(subst(e,e2,x))
      case Index(t1,t2) => Index(subst(t1,e2,x),subst(t2,e2,x))
      case Concat(t1,t2) => Concat(subst(t1,e2,x),subst(t2,e2,x))


      // Variables + let
      case Var(y) => if(x == y) {
        e2
      } else {
        Var(y)
      }
      case Let(y,t1,t2) => if(x == y) {
        Let(y,subst(t1,e2,x),t2)
      } else {
        if(free(e2).contains(y)) {
          val z = Gensym.gensym(y)
          Let(z,subst(t1,e2,x),subst(subst(t2,Var(z),y),e2,x))
        } else {
          Let(y,subst(t1,e2,x),subst(t2,e2,x))
        }
      }

      // Pairs
      case Pair(t1,t2) => Pair(subst(t1,e2,x),subst(t2,e2,x))
      case First(e) => First(subst(e,e2,x))
      case Second(e) => Second(subst(e,e2,x))

      // Functions
      case Lambda(y,a,e) => if(x == y) {
        Lambda(y,a,e)
      } else {
        if(free(e2).contains(y)) {
          val z = Gensym.gensym(y)
          Lambda(z,a,subst(subst(e,Var(z),y),e2,x))
        } else {
          Lambda(y,a,subst(e,e2,x))
        }
      }

      case Rec(f,y,a,b,e) =>
        if (x == f || x == y) {
          Rec(f,y,a,b,e)
        } else {
          val fvs = free(e2);
          if (fvs.contains(y) || fvs.contains(f)) {
            // for simplicity just rename both
            val yz = Gensym.gensym(y);
            val fz = Gensym.gensym(f);
            Rec(fz,yz,a,b,subst(subst(subst(e,Var(yz),y),Var(fz),f),e2,x))
          } else {
            Rec(f,y,a,b,subst(e,e2,x))
          }
        }

      case LetPair(y1,y2,t1,t2) => {
        val y1z = Gensym.gensym(y1);
        val y2z = Gensym.gensym(y2);
        LetPair(y1z,y2z,subst(t1,e2,x),
          subst(subst(subst(t2,Var(y1z),y1), Var(y2z), y2), e2,x))
      }

      case LetFun(f,y,ty,t1,t2) => {
        val fz = Gensym.gensym(f);
        val yz = Gensym.gensym(y);
        LetFun(fz,yz,ty,subst(subst(t1,Var(yz),y),e2,x),
          subst(subst(t2,Var(fz),f), e2,x))
      }

      case LetRec(f,y,ty1,ty2,t1,t2) => {
        val fz = Gensym.gensym(f);
        val yz = Gensym.gensym(y);
        LetRec(fz,yz,ty1,ty2,subst(subst(subst(t1,Var(fz),f),Var(yz),y),e2,x),
          subst(subst(t2,Var(fz),f), e2,x))
      }

      /*case Rec(f,y,a,b,e) => (x == f,x == y) match {
        case(true,true) => Rec(f,y,a,b,e)
        case(true,false) =>
          if(free(e2).contains(y)) {
            val z = Gensym.gensym(y)
            Rec(f,z,a,b,subst(subst(e,Var(z),y),e2,x))
          } else {
            Rec(f,y,a,b,subst(e,e2,x))
          }
        case(false,true) =>
          if(free(e2).contains(f)) {
            val z = Gensym.gensym(f)
            Rec(z,y,a,b,subst(subst(e,Var(z),f),e2,x))
          } else {
            Rec(f,y,a,b,subst(e,e2,x))
          }
        case(false,false) =>
          if(free(e2).contains(y)) {
            val yz = Gensym.gensym(y)
            if(free(e2).contains(f)) {
              val fz = Gensym.gensym(f)
              Rec(fz,yz,a,b,subst(subst(subst(e,Var(yz),y),Var(fz),f),e2,x))
            } else {
              Rec(f,yz,a,b,subst(subst(e,Var(yz),y),e2,x))
            }
          } else {
            if(free(e2).contains(f)) {
              val fz = Gensym.gensym(f)
              Rec(fz,y,a,b,subst(subst(e,Var(fz),f),e2,x))
            } else {
              Rec(f,y,a,b,subst(e,e2,x))
            }
          }
      }
       */
      case Apply(t1,t2) => Apply(subst(t1,e2,x),subst(t2,e2,x))
    }



  // ======================================================================
  // Exercise 2: Desugaring let fun, let rec and let pair
  // ======================================================================

  def desugar(e: Expr): Expr = e match {

    case Plus(e1,e2) => Plus(desugar(e1),desugar(e2))
    case Minus(e1,e2) => Minus(desugar(e1),desugar(e2))
    case Times(e1,e2) => Times(desugar(e1),desugar(e2))

    case Eq(e1,e2) => Eq(desugar(e1),desugar(e2))
    case IfThenElse(cond,e1,e2) => {
      IfThenElse(desugar(cond),desugar(e1),desugar(e2))
    }

    case Length(e) => Length(desugar(e))
    case Index(e1,e2) => Index(desugar(e1),desugar(e2))
    case Concat(e1,e2) => Concat(desugar(e1),desugar(e2))

    case Let(x,e1,e2) => Let(x,desugar(e1),desugar(e2))
    case LetFun(f,arg,ty,e1,e2) =>
      Let(f,Lambda(arg,ty,desugar(e1)),desugar(e2))
    case LetRec(f,arg,xty,ty,e1,e2) => {
      Let(f,
        Rec(f,arg,xty,ty,desugar(e1)),
        desugar(e2))
    }
    case LetPair(x,y,e1,e2) => {
      val p = Gensym.gensym("p")
      Let(p,desugar(e1),subst(subst(desugar(e2),First(Var(p)),x),Second(Var(p)),y))
    }

    case Pair(e1,e2) => Pair(desugar(e1),desugar(e2))
    case First(e) => First(desugar(e))
    case Second(e) => Second(desugar(e))

    case Lambda(x,ty,e) => Lambda(x,ty,desugar(e))
    case Apply(e1,e2) => Apply(desugar(e1),desugar(e2))
    case Rec(f,x,tyx,ty,e) => Rec(f,x,tyx,ty,desugar(e))

    case e => e // Num, bool, str, var

  }


  // ======================================================================
  // Part 2: Interpretation
  // ======================================================================

  // ======================================================================
  // Exercise 3: Primitive operations
  // ======================================================================


  object Value {
    // utility methods for operating on values
    def add(v1: Value, v2: Value): Value = (v1,v2) match {
      case (NumV(v1), NumV(v2)) => NumV (v1 + v2)
      case _ => sys.error("arguments to addition are non-numeric")
    }

    def subtract(v1: Value, v2: Value): Value = (v1,v2) match {
      case (NumV(v1), NumV(v2)) => NumV (v1 - v2)
      case _ => sys.error("arguments to addition are non-numeric")
    }

    def multiply(v1: Value, v2: Value): Value = (v1,v2) match {
      case (NumV(v1), NumV(v2)) => NumV (v1 * v2)
      case _ => sys.error("arguments to multiplication are non-numeric")
    }

    def eq(v1: Value, v2: Value): Value = (v1,v2) match {
      case (BoolV(b1),BoolV(b2)) => BoolV(b1 == b2)
      case (NumV(n1),NumV(n2)) => BoolV(n1 == n2)
      case (StringV(s1),StringV(s2)) => BoolV(s1 == s2)
      case _ => sys.error("Only equality for base types is supported")
    }

    def length(v: Value): Value = v match {
      case StringV(s) => NumV(s.length)
      case _ => sys.error("argument to length is not of string type")
    }

    def index(v1: Value, v2: Value): Value = (v1,v2) match {
      case (StringV(s),NumV(n)) => StringV((s.apply(n)).toString)
      case _ => sys.error("type mismatch in index function")
    }

    def concat(v1: Value, v2: Value): Value = (v1,v2) match {
      case (StringV(s1),StringV(s2)) => StringV(s1.concat(s2))
      case _ => sys.error("type mismatch in concat function")
    }
 }




  // ======================================================================
  // Exercise 4: Evaluation
  // ======================================================================

  def eval (env: Env[Value], e: Expr): Value = e match {
    // Arithmetic
    case Num(n) => NumV(n)
    case Plus(e1,e2) =>
      Value.add(eval(env,e1),eval(env,e2))
    case Minus(e1,e2) =>
      Value.subtract(eval(env,e1),eval(env,e2))
    case Times(e1,e2) =>
      Value.multiply(eval(env,e1),eval(env,e2))

    // Booleans
    case Bool(b) => BoolV(b)
    case Eq(e1,e2) =>
      Value.eq(eval(env,e1),eval(env,e2))
    case IfThenElse(e,e1,e2) =>
      eval(env,e) match {
        case BoolV(true) => eval(env,e1)
        case BoolV(false) => eval(env,e2)
        case _ =>  sys.error("conditional must evaluate to a boolean")
      }

    // Strings
    case Str(s) => StringV(s)
    case Length(e) =>
      Value.length(eval(env,e))
    case Index(e1,e2) =>
      Value.index(eval(env,e1),eval(env,e2))
    case Concat(e1,e2) =>
      Value.concat(eval(env,e1),eval(env,e2))

    // Variables + let
    case Var(x) =>
      env(x)
    case Let(x,e1,e2) =>
      eval(env + (x -> eval(env,e1)),e2)

    // Pairs
    case Pair(e1,e2) =>
      PairV(eval(env,e1),eval(env,e2))
    case First(e) => eval(env,e) match {
      case PairV(x,_) => x
      case _ => sys.error("first must be applied to a pair")
    }
    case Second(e) => eval(env,e) match {
      case PairV(_,y) => y
      case _ => sys.error("second must be applied to a pair")
    }

    // Functions
    case Lambda(x,_,e) =>
      ClosureV(env,x,e)
    case Rec(f,x,_,_,e) =>
      RecV(env,f,x,e)
    case Apply(e1,e2) =>
      eval(env,e1) match {
        case ClosureV(lamEnv,x,lamBody) =>
          eval(lamEnv + (x -> eval(env,e2)),lamBody)
        case RecV(recEnv,f,x,recBody) =>
          eval(recEnv
            + (f -> RecV(recEnv,f,x,recBody))
            + (x -> eval(env,e2)),
            recBody)
        case _ => sys.error("first argument of application must be a function")
      }
  }


  // ======================================================================
  // Part 3: Typechecking
  // ======================================================================

  // ======================================================================
  // Exercise 5: Typechecker
  // ======================================================================

  // typing: calculate the return type of e, or throw an error
  def tyOf(ctx: Env[Type], e: Expr): Type = e match {
    // Arithmetic
    case Num(n) => IntTy
    case Plus(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("non-integer arguments to -")
    }
    case Minus(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("non-integer arguments to +")
    }
    case Times(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("non-integer arguments to *")
    }

    //  Booleans
    case Bool(b) => BoolTy
    case Eq(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (a, b) => if (a == b) {
        BoolTy
      } else {
        sys.error("types of eq must be equal")
      }
    }
    case IfThenElse(e,e1,e2) =>
      (tyOf(ctx,e),tyOf(ctx,e1),tyOf(ctx,e2)) match {
        case (BoolTy,a,b) => if (a == b) {
          a
        }
        else {
          sys.error("types of branches must be equal")
        }
        case (_,a,b) => sys.error("type of conditional must be boolean")
      }

    // Strings
    case Str(s) => StringTy
    case Length(e) => tyOf(ctx,e) match {
      case StringTy => IntTy
      case _ => sys.error("Length must be applied to a string")
    }
    case Index(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (StringTy,IntTy) => StringTy
      case (a,b) => sys.error("Index must be applied to string and int" +
      ". Types are " + a.toString + " " + b.toString)
    }
    case Concat(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (StringTy,StringTy) => StringTy
      case _ => sys.error("Concat takes two strings")
    }

    // Variables and let-binding
    case Var(x) => ctx(x)
    case Let(x,e1,e2) => tyOf(ctx + (x -> (tyOf(ctx,e1))), e2)
    case LetPair(x,y,e1,e2) => tyOf(ctx, e1) match {
      case PairTy(a,b) => tyOf(ctx + (x -> a) + (y -> b), e2)
      case _ => sys.error("Let pair's first argument must be a pair")
    }
    case LetFun(f,x,ty,e1,e2) => {
      val ty2 = tyOf(ctx + (x -> ty), e1);
      tyOf(ctx + (f -> FunTy(ty,ty2)), e2)
    }
    case LetRec(f,x,ty1,ty2,e1,e2) => {
      val fty = FunTy(ty1,ty2);
      if (tyOf(ctx + (x -> ty1) + (f -> fty), e1) == ty2) {
        tyOf(ctx + (f -> fty), e2)
      } else {
        sys.error("Type of recursive function does not match specification")
      }
    }


    //  Pairs
    case Pair(e1,e2) => PairTy(tyOf(ctx,e1),tyOf(ctx,e2))
    case First(e) => tyOf(ctx,e) match {
      case PairTy(a,b) => a
      case _ => sys.error("First must be applied to a pair")
    }
    case Second(e) => tyOf(ctx,e) match {
      case PairTy(a,b) => b
      case _ => sys.error("Second must be applied to a pair")
    }

    // Functions
    case Lambda(x,ty,e) => FunTy(ty,tyOf(ctx + (x -> ty),e))
    case Rec(f,x,xty,ty,e) => tyOf(ctx + (f -> FunTy(xty,ty)) + (x -> xty),e) match {
      case body => if (ty == body) {
        FunTy(xty,ty)
      } else {
        sys.error("Function body type does not match that specified")
      }
    }

    case Apply(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (FunTy(a,b),c) => if (a == c) {
        b
      } else {
        sys.error("Argument type does not match fuction input")
      }
      case (a,c) => sys.error("Function type not found!\n" +
          "Typing " + e1.toString + "type is: " + a.toString + "\n" +
          "Typing " + e2.toString + "type is: " + c.toString + "\n")

    }
  }


  // ======================================================================
  // Part 4: Some simple programs
  // ======================================================================

  // The following examples illustrate how to embed Giraffe source code into
  // Scala using multi-line comments, and parse it using parser.parseStr.

    // Example 1: the swap function
  def example1: Expr = parser.parseStr("""
    let fun swap(x:int * int) = (snd(x), fst(x)) in
    swap(42,17)
    """)

  // Example 2: the factorial function, yet again
  def example2: Expr = parser.parseStr("""
    let rec fact(n:int):int =
      if (n == 0) then 1 else n * fact(n - 1) in
    fact(5)
    """)

  // Example 3: exponentiation
  def example3: Expr = parser.parseStr("""
    let rec power(input: int * int):int =
          let (x,n) = input in
          if (n == 0) then 1 else
          x * power(x,n-1)
        in
        power(2,10)
    """)

  // Example 4: check whether two strings have the same last character
  def example4: Expr = parser.parseStr("""
    let fun sameLastChar(input: str * str) =
      let (s1,s2) = input in
      index(s1,length(s1)-1) == index(s2,length(s2)-1)
    in sameLastChar("abcz","abcdefghijklmnopqrstuvwxyz")
    """)

  // Example 5: String slice
  def example5: Expr = parser.parseStr("""
    let rec slice(input: str * (int * int)) : str =
      let (s,p) = input in
      let (base,len) = p in
      if (len == 0) then ""
      else concat(index(s,base), slice (s,(base + 1, len - 1)))
    in slice("abcdefghijklmnopqrstuvwxyz", (10, 10))""")

  // Example 6: Integer comparison
  def example6: Expr = parser.parseStr("""
    let comment = "Assumes nonnegative arguments" in
    let rec lessthanorequal(nm: int * int) : bool =
      let (n,m) = nm in
      if (n == 0) then true
      else if (m == 0) then false
      else lessthanorequal(n-1,m-1)
    in (lessthanorequal (5,6), lessthanorequal(6,5))""")

  // ======================================================================
  // Exercise 6: Fibonacci sequence
  // ======================================================================

  def fib: Expr =
    Let("fib",
      Lambda("n",IntTy,
        IfThenElse(Eq(Var("n"),Num(0)),
          Num(0),
          IfThenElse(Eq(Var("n"),Num(1)),
            Num(1),
            IfThenElse(Eq(Var("n"),Num(2)),
              Num(1),
              Let("fibInner",
                Rec("fibInner","args",PairTy(IntTy,PairTy(IntTy,IntTy)),IntTy,
                  Let("p_0",Var("args"),
                    Let("p_1",Second(Var("p_0")),
                      IfThenElse(Eq(First(Var("p_0")),Var("n")),
                        Plus(First(Var("p_1")),Second(Var("p_1"))),
                        Apply(Var("fibInner"),
                          Pair(Plus(First(Var("p_0")),Num(1)),
                            Pair(Second(Var("p_1")),Plus(First(Var("p_1")),
                              Second(Var("p_1")))))))))),
                Apply(Var("fibInner"),
                  Pair(Num(3),Pair(Num(1),Num(1))))))))),
      Apply(Var("fib"),Num(70)))

  // ======================================================================
  // Exercise 7: Substrings
  // ======================================================================

  def substring: Expr =
    Let("substring",
      Lambda("input",PairTy(StringTy,StringTy),
        Let("p_0",Var("input"),
          Let("substringInner",
            Rec("substringInner","args",PairTy(IntTy,PairTy(IntTy,IntTy)),BoolTy,
              Let("p_1",Var("args"),
                Let("p_2",Second(Var("p_1")),
                  IfThenElse(
                    Eq(First(Var("p_2")),Length(First(Var("p_0")))),
                    Bool(true),
                    IfThenElse(
                      Eq(Plus(Second(Var("p_2")),
                        First(Var("p_1"))),
                        Length(Second(Var("p_0")))),
                      Bool(false),
                      IfThenElse(
                        Eq(Index(First(Var("p_0")),First(Var("p_2"))),
                          Index(Second(Var("p_0")),
                            Plus(Second(Var("p_2")),First(Var("p_1"))))),
                        Apply(Var("substringInner"),
                          Pair(First(Var("p_1")),
                            Pair(Plus(First(Var("p_2")),Num(1)),
                              Plus(Second(Var("p_2")),Num(1))))),
                        Apply(Var("substringInner"),
                          Pair(Plus(First(Var("p_1")),Num(1)),
                            Pair(Num(0),Num(0)))))))))),
            Apply(Var("substringInner"),
              Pair(Num(0),Pair(Num(0),Num(0))))))),
      Apply(Var("substring"),Pair(Str("needle"),Str("haystackneedlehaystack"))))


  /*======================================================================
   The rest of this file is support code, which you should not (and do not
   need to) change.
   ====================================================================== */

  class CWParser extends StandardTokenParsers with PackratParsers {

    type P[+A] = PackratParser[A]

    def parseStr(input: String): Expr = {
      phrase(expression)(new lexical.Scanner(input)) match {
        case Success(ast, _) => ast
        case e: NoSuccess => sys.error(e.msg)
      }
    }

    def parse(input: String): Expr = {
      val source = scala.io.Source.fromFile(input)
      val lines = try source.mkString finally source.close()
      parseStr(lines)
    }

    lexical.reserved += ("let", "in", "rec", "if", "then", "else",
      "int","str","bool","true","false","fst","snd","concat",
      "index","length","fun"
    )
    lexical.delimiters += ("=","*", "\\", "+", "-", "(", ")", "==", ":", ".",
      "->", ","
    )

    lazy val expression: P[Expr] =
      simpleExpr

    lazy val lambda: P[Expr] =
      ("\\" ~> ident) ~ (":" ~> typ) ~ ("." ~> expression) ^^ {
        case arg~ty~body => Lambda(arg,ty,body)
      }

    lazy val rec: P[Expr] =
      ("rec" ~> ident) ~
        ("(" ~> ident) ~ (":" ~> typ) ~ ((")" ~ ":") ~> typ) ~
        ("." ~> expression) ^^ {
          case recArg~funArg~funType~recType~body =>
            Rec(recArg,funArg,funType,recType,body)
        }

    lazy val ifExpr: P[Expr] =
      ("if" ~> expression) ~
        ("then" ~> expression) ~
        ("else" ~> expression) ^^ {
          case cond~e1~e2 => IfThenElse(cond,e1,e2)
        }

    lazy val letExpr: P[Expr] =
      ("let" ~> ident) ~ ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case binder~e1~e2 => Let(binder,e1,e2)
      }

    lazy val letFun: P[Expr] =
      ("let" ~ "fun" ~> ident) ~ ("(" ~> ident) ~
        (":" ~> typ <~ ")") ~ ("=" ~> expression) ~
        ("in" ~> expression) ^^ {
          case fun~binder~ty~e1~e2 => LetFun(fun,binder,ty,e1,e2)
        }

    lazy val letRec: P[Expr] =
      ("let" ~ "rec" ~> ident) ~ ("(" ~> ident) ~
        (":" ~> typ <~ ")") ~ (":" ~> typ) ~ ("=" ~> expression) ~
        ("in" ~> expression) ^^ {
          case fun~binder~xty~ty~e1~e2 => LetRec(fun,binder,xty,ty,e1,e2)
        }

    lazy val letPair: P[Expr] =
      ("let" ~ "(") ~> ident ~ ("," ~> ident <~ ")") ~
        ("=" ~> expression) ~ ("in" ~> expression) ^^ {
          case x~y~e1~e2 => LetPair(x,y,e1,e2)
        }

    lazy val typ: P[Type] =
      funTyp

    lazy val funTyp: P[Type] =
      pairTyp ~ "->" ~ funTyp ^^ {
        case t1~"->"~t2 => FunTy(t1,t2)
      } | pairTyp

    lazy val pairTyp: P[Type] =
      primitiveType ~ "*" ~ pairTyp ^^ {
        case t1~"*"~t2 => PairTy(t1,t2)
      } | primitiveType

    lazy val primitiveType: P[Type] =
      "bool" ^^^ BoolTy | "int" ^^^ IntTy | "str" ^^^ StringTy |  "("~>typ<~")"

    lazy val operations: P[Expr] =
      application |
      ("fst" ~ "(") ~> expression <~ ")" ^^ (x => First(x)) |
        ("snd" ~ "(") ~> expression <~ ")" ^^ (x => Second(x)) |
        ("length" ~ "(") ~> expression <~ ")" ^^ (x => Length(x)) |
        ("concat"  ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
          case e1~e2 => Concat(e1,e2)
        } |
        ("index" ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
          case e1~e2 => Index(e1,e2)
        }

    lazy val arith: P[Expr] =
      eq

    lazy val prod: P[Expr] =
      prod ~ "*" ~ fact ^^ {
        case e1~"*"~e2 => Times(e1,e2)
      } | fact

    lazy val summation: P[Expr] =
      summation ~ "+" ~ prod ^^ {
        case e1~"+"~e2 => Plus(e1,e2)
      } | summation ~ "-" ~ prod ^^ {
        case e1~"-"~e2 => Minus(e1,e2)
      } | prod

    lazy val eq: P[Expr] =
      simpleExpr ~ "==" ~ summation ^^ {
        case e1~"=="~e2 => Eq(e1,e2)
      } | summation

    lazy val application: P[Expr] =
      fact ~ fact ^^ {
        case e1~e2 => Apply(e1,e2)
      }

    lazy val simpleExpr: P[Expr] = (
      lambda |
        rec |
        letExpr |
        letFun |
        letRec |
        letPair |
        ifExpr |
        arith |
        fact
    )

    lazy val pairLit: P[Expr] =
      "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
        case t1~","~t2 => Pair(t1,t2)
      }

    lazy val fact: P[Expr] = (
      operations |
        pairLit |
        (ident ^^ Var) |
        (numericLit ^^ { x => Num(x.toInt) }) |
        (stringLit ^^ Str) |
        ("true" ^^^ Bool(true)) |
        ("false" ^^^ Bool(false)) |
        "("~>expression<~")"
    )

  }


  val parser = new CWParser


  object Main {
    def typecheck(ast: Expr):Type =
      tyOf(Map.empty,ast);

    def evaluate(ast: Expr):Value =
      eval(Map.empty,ast)



    def showResult(ast: Expr) {
      println("AST:  " + ast.toString + "\n")

      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n") ;
      } catch {
          case e:Throwable => println("Error: " + e)
      }
      println("Desugaring...");
      val core_ast = desugar(ast);
      println("Done!");
      println("Desugared AST: " + core_ast.toString + "\n") ;

      println("Evaluating...");
      println("Result: " + evaluate(core_ast))


    }

    def start(): Unit = {
      println("Welcome to Giraffe! (V1.10, October 18, 2015)");
      println("Enter expressions to evaluate, :load <filename.gir> to load a file, or :quit to quit.");
      println("This REPL can only read one line at a time, use :load to load larger expressions.");
      repl()
    }

    def repl(): Unit = {
      print("Giraffe> ");
      val input = scala.io.StdIn.readLine();
      if(input == ":quit") {
        println("Goodbye!")
      }
      else if (input.startsWith(":load")) {
        try {
          val ast = parser.parse(input.substring(6));
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      } else {
        try {
          val ast = parser.parseStr(input);
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      }
    }

  }
  def main( args:Array[String] ):Unit = {
    if(args.length == 0) {
      Main.start()
    } else {
      try {
        print("Parsing...");
        val ast = parser.parse(args.head)
        println("Done!");
        Main.showResult(ast)
      } catch {
        case e:Throwable => println("Error: " + e)
      }
    }
  }
}
