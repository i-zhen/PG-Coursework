// Version 1.10

/*
 * NAME : ZHEN YI
 */

import scala.collection.immutable.Set //可以做自由变量检查器

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

object CW1 {
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


  def subst(e1:Expr, e2:Expr, x: Variable): Expr = //产生free variables时需要替换，否则可以不用替换直接求值
    e1 match {
      case Num(e) => Num(e)
      case Plus(t1,t2) => Plus(subst(t1,e2,x),subst(t2,e2,x))
      case Minus(t1,t2) => Minus(subst(t1,e2,x),subst(t2,e2,x))
      case Times(t1,t2) => Times(subst(t1,e2,x),subst(t2,e2,x))

      case Bool(n) => Bool(n)
      case Eq(t1,t2) => Eq(subst(t1,e2,x),subst(	t2,e2,x))
      case IfThenElse(t0,t1,t2) =>
        IfThenElse(subst(t0,e2,x),subst(t1,e2,x),subst(t2,e2,x))

      case Str(s) => Str(s)
      case Length(t0) => Length(subst(t0,e2,x))
      case Index(t1,t2) => Index(subst(t1,e2,x),subst(t2,e2,x))
      case Concat(t1,t2) => Concat(subst(t1,e2,x),subst(t2,e2,x))

      case Var(y) =>
        if (x == y) {
          e2
        } else {
          Var(y)
        }

      case Let(y,t1,t2) =>  //let语句，如果不是rec函数的情况下，y只绑定了t2，没有绑定t1
        if (x == y) { // we can stop early since x is re-bound here
          Let(y,subst(t1,e2,x),t2) //这里不是 Let(y,e2,t2)的原因是不能破坏原始绑定
          /*
           let y = 10 in
           let y = y + 1 in
           y + 9
           如果我们直接替换，显然与原意不符
          */
          //这里没有subst(t2)是因为，t2被y绑定，不被x绑定
          //没有rename的原因是：首先，rename没有错，可以rename。
          //但是因为x==y，所以我们不需要rename，因为我们改变的仅仅是t1中的y，不影响绑定本身。
          //例子： (\x:int.x+y)[x/y] 需要rename为(\z:int.z+y)[x/y]
          //(\x:int.x+y)[y+1/y][9/y] 会变成 (\x:int.x+y)[9+1/y]
          //更进一步说：当x!=y时，我们要把t1,t2都做替换；反之，t2被y绑定，相当于被重新绑定了。
          /*
            let y = 10 in
            let y = 9 in
            y + 1
            本来，y = 10, 后来，y=9，也就是被重新绑定了，所以不可以把t2也替换掉。因为，这时的t2中的y是被
            y = 9 时的y所绑定的
          */
          //总结，当变量被重绑定时(比如x)，要么什么都不做(新的绑定中没出现x)；要么只替换新的绑定中的变量。
          // y = 10 -> y = 9 什么都不做
          // y = 10 -> y = y + 1 只替换 y+1 中的 y
        } else { // otherwise, we freshen y
          val z = Gensym.gensym(y);
          val fresh_t2 = subst(t2,Var(z),y);
          Let(z,subst(t1,e2,x),subst(fresh_t2,e2,x))
        }

      case LetFun(f, y, ty, t1, t2) => {
          val zf = Gensym.gensym(f);
          val zy = Gensym.gensym(y);
          val fresh_t1 = subst(t1,Var(zy),y);
          val fresh_t2 = subst(t2,Var(zf),f);
          LetFun(zf, zy, ty, subst(fresh_t1,e2,x), subst(fresh_t2,e2,x))
        }

      case LetRec(f, y, xty, ty, t1, t2)=> {
          val zf = Gensym.gensym(f);
          val zy = Gensym.gensym(y);
          val fresh_t1 = subst(t1,Var(zf),f);
          val fresh_t11 = subst(fresh_t1,Var(zy),y);
          val fresh_t2 = subst(t2,Var(zf),f);
          LetRec(zf, zy, xty, ty, subst(fresh_t11,e2,x), subst(fresh_t2,e2,x))
        }

      case LetPair(v1, v2, t1, t2) => {
          val z1 = Gensym.gensym(v1);
          val z2 = Gensym.gensym(v2);
          val fresh_t2 = subst(t2,Var(z1),v1);
          val fresh_t3 = subst(fresh_t2,Var(z2),v2);
          LetPair(z1, z2, subst(t1,e2,x), subst(fresh_t3,e2,x))
        }

      case Pair(t1, t2) => Pair(subst(t1,e2,x),subst(t2,e2,x))

      case First(t1) => First(subst(t1,e2,x))
      /* e2 match {
        case Pair(pe1, pe2) => subst(t1,pe1,x)

        We cannot do this because if the Var in t1 isn't equal to x, we
        will destroy the structure of First(t1) from First(t1) to t1 without
        any other changing

        so we can only do this in the "eval"

      }*/

      case Second(t2) => Second(subst(t2,e2,x))

      case Lambda(y, ty, t0) =>
        if (x == y) Lambda(y, ty, t0) //不能替换，内部绑定不能改变
        else {
          val z = Gensym.gensym(y);
          val fresh_t0 = subst(t0,Var(z),y);
          Lambda(z, ty, subst(fresh_t0,e2,x))
        }

      case Apply(t1, t2) => Apply(subst(t1,e2,x), subst(t2,e2,x))

      case Rec(f, y, tyx, ty, t0) => {
        if(x == y) Rec(f, y, tyx, ty, t0 )
        //函数内部的绑定与外界没有关联，所以不能被改变：let x=14 in（let rec f(x:int):int = x+1 in f 12）
        else if(x == f) Rec(f, y, tyx, ty, t0)
        //同上，不能被替换：let x = 26 in（let rec x(y:int):int = if y == 12 then x (y+1) else (y+1) in x 12）
        else {
          val zf = Gensym.gensym(f);
          val zy = Gensym.gensym(y);
          val fresh_t0 = subst(t0,Var(zf),f);
          val fresh_t1 = subst(fresh_t0,Var(zy),y);
          Rec(zf, zy, tyx, ty, subst(fresh_t1,e2,x))
        }
      }
      case _ => sys.error("Error: Subst : Wrong Expression")
    }


  // ======================================================================
  // Exercise 2: Desugaring let fun, let rec and let pair
  // ======================================================================

  def desugar(e: Expr): Expr = e match {

    case Num(n) => Num(n)
    case Plus(e1,e2) => Plus(desugar(e1),desugar(e2))
    case Minus(e1,e2) => Minus(desugar(e1),desugar(e2))
    case Times(e1,e2) => Times(desugar(e1),desugar(e2))

    case Bool(n) => Bool(n)
    case Eq(e1, e2) => Eq(desugar(e1), desugar(e2))
    case IfThenElse(e,e1,e2) => IfThenElse(desugar(e),desugar(e1),desugar(e2))

    case Str(s) => Str(s)
    case Length(e) => Length(desugar(e))
    case Index(e1, e2) => Index(desugar(e1),desugar(e2))
    case Concat(e1,e2) => Concat(desugar(e1),desugar(e2))

    case Var(x) => Var(x)
    case Let(x, e1, e2) => {
      Let(x, desugar(e1), desugar(e2))  //可以进一步替换，直到没有自由变量
    }
    case LetFun(f, y, ty, e1, e2) =>{
      Let(f,Lambda(y, ty, desugar(e1)), desugar(e2)) //可以进一步替换
    }

    case LetRec(f, y, xty, ty, e1, e2) => {
      Let(f,Rec(f, y, xty, ty, desugar(e1)), desugar(e2))
    }


    case LetPair(x, y, e1, e2) => {  //可以进一步替换
      val z = Gensym.gensym(x+y);
      Let(z,desugar(e1),subst(subst(desugar(e2),Second(Var(z)),y),First(Var(z)), x))
    }

    case Pair(e1, e2) => Pair(desugar(e1), desugar(e2))
    case First(e) => First(desugar(e))
    case Second(e) => Second(desugar(e))

    case Lambda(x, ty, e) => Lambda(x, ty, desugar(e))
    case Apply(e1, e2) => Apply(desugar(e1), desugar(e2))
    case Rec(f, x, tyx, ty, e) => Rec(f,x,tyx,ty,desugar(e))

    case _ => sys.error("Error: Desugar: Imposiible Expression")

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
      case _ => sys.error("arguments to subtract are non-numeric")
    }

    def multiply(v1: Value, v2: Value): Value = (v1, v2) match {
      case (NumV(v1),NumV(v2)) => NumV(v1 * v2)
      case _ => sys.error("arguments to multiply are non-numeric")
    }

    def eq(v1: Value, v2: Value): Value = (v1, v2) match{
      case (NumV(v1), NumV(v2)) => BoolV(v1 == v2)
      case (StringV(v1), StringV(v2)) => BoolV(v1 == v2)
      case (BoolV(v1), BoolV(v2)) => BoolV(v1 == v2)
      case _ =>
        sys.error("arguments should have the same type for: str, int, bool")
    }


    def length(v: Value): Value = v match {
      case StringV(v) => NumV(v.length())
      case _ => sys.error("Required type String")
    }


    //Need check
    def index(v1: Value, v2: Value): Value = (v1, v2) match {
      case (StringV(v1),NumV(v2)) => {
        if (v2 >= v1.length() || v2 < 0)
          sys.error("Out of range")
        else
          StringV(v1(v2).toString())
      }
      case _ => sys.error("Wrong arguments type, shoud be: (str, int)")
    }


    def concat(v1: Value, v2: Value): Value = (v1,v2) match {
      case (StringV(v1),StringV(v2)) => StringV(v1 + v2)
      case _ => sys.error("Wrong arguments type, shoud be: (str, str)")
    }
  }

  // ======================================================================
  // Exercise 4: Evaluation
  // ======================================================================

  def eval (env: Env[Value], e: Expr): Value =e match {
    // Arithmetic
    case Num(n) => NumV(n)
    case Plus(e1,e2) =>
      Value.add(eval(env,e1),eval(env,e2))
    case Minus(e1,e2) =>
      Value.subtract(eval(env,e1),eval(env,e2))
    case Times(e1,e2) =>
      Value.multiply(eval(env,e1),eval(env,e2))

    case Bool(n) => BoolV(n)

    case Str(str) => StringV(str)

    case Eq(e1,e2) =>
      Value.eq(eval(env,e1),eval(env,e2))

    case Length(e1) =>
      Value.length(eval(env,e1))

    case Index(e1, e2) =>
      Value.index(eval(env,e1),eval(env,e2))

    case Concat(e1,e2) =>
      Value.concat(eval(env,e1),eval(env,e2))

    //Var(x) => env(x)
    case Var(x) => env.get(x) match {
      case Some(v) => v
      case None =>  sys.error("Failed to find the value of " + x + " in env")
    }

    //very important!
    /*
    case IfThenElse(e,e1,e2) => eval(env, e) match {
      case BoolV(n) =>
        if (n) eval(env, e1) else eval(env, e2)
      case _ => sys.error("Not an legal boolean value")
    }
    */
    case IfThenElse(e,e1,e2) => eval(env, e) match {
      case BoolV(true) => eval(env, e1)
      case BoolV(false) => eval(env, e2)
      case _ => sys.error("Not an legal boolean value")
    }

    case Let(x,e1,e2) => eval(env + (x -> eval(env, e1)), e2)

    case Pair(e1,e2) => PairV(eval(env,e1),eval(env,e2))

    case First(e) => eval(env, e) match {
      case PairV(v1, v2) => v1
      case _ => sys.error("Eval: First: Cannot match such pattern")
    }

    case Second(e) => eval(env, e) match {
      case PairV(v1, v2) => v2
      case _ => sys.error("Eval: Second :Cannot match such pattern")
    }
    //Function

    case Lambda(x, ty, e) => ClosureV(env, x, e)

    case Rec(f, x, tyx, ty, e) => RecV(env, f, x, e)
/*
    case Apply(e1, e2) => e1 match {
      case Lambda(x, ty, e) => eval(env, subst(e, e2, x))

      //e1 会指向一个闭包或者lambda
      case Rec(f, x, tyx, ty, e) => {
        val ne = subst(e,e1,f)
        eval(env, subst(ne,e2,x))
        //to avoid infinite loop we need to evaluate the expression of Rec(not the Rec itself)when the subst done every time
        //当一个递归函数嵌套另一个递归函数的时候，要把另一个递归函数的值先求出来。否则会陷入无限循环，但是因为递归中存在递归，两个递归函数使用不同规则会导致混乱
        //这个时候我们要用到闭包，闭包中存储了当时环境信息（也可以解释为递归函数的堆栈信息，与外界隔离开，避免变量混乱）
      }
    }
      case Var(varx) => env(varx) match {
        case ClosureV(envc, x, e) =>
          eval(envc + (x -> eval(env, e2)), e)
        case RecV(envr, f, x, e) => {
          eval(envr + (x -> eval(env,e2)) + (f -> env(f)), e)
          Very Important Key! 首先，我们要在外部环境中求e2的值，Apply(e1,e2)；所以相对于e1来讲，e2在外部环境中
          然后呢，我们要在envr中加入e2的值，注意不是加入e2，而仅仅是他的值；再然后要注意，f本身是属于外部环境的，闭包
          只是指代f内部的body，所以这是个很有意思的问题。即便body中可能含有f（递归函数），我们仍然要视其为外部来操作。
          已经是闭包了，不需要再做替换了，无需使用f替换e里面的f
        }
      }
      case _ => {
        println(e1)
        sys.error("Oh my")
      }
    }
    */
    case Apply(e1, e2) => eval(env, e1) match {
      case ClosureV(envc, x, e) =>
        eval(envc + (x -> eval(env, e2)), e)
      case RecV(envr, f, x, e)  =>
        eval(envr + (x -> eval(env,e2)) + (f -> RecV(envr, f, x, e)), e)
    }

    case _ => sys.error("Eval: Cannot match such pattern")
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
      case _ => sys.error("Plus: non-integer arguments to add")
    }

    case Minus(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("Minus: non-integer arguments to minus")
    }
    case Times(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("Times: non-integer arguments to times")
    }


    //Booleans
    case Bool(n) => BoolTy

    case IfThenElse(e,e1,e2) => (tyOf(ctx,e),tyOf(ctx,e1),tyOf(ctx,e2)) match{
      case (BoolTy, t1, t2) =>
        if (t1 == t2) t1 else sys.error("Types of branches must be equal")
      case _ => sys.error("IfThenElse: Type in the first expression mush be boolean")
    }

    case Eq(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => BoolTy
      case (StringTy, StringTy) => BoolTy
      case (BoolTy, BoolTy) => BoolTy
      case _ => sys.error("Eq: Types in the Eq must be Int, String or Bool")
    }

    //Strings

    case Str(s) => StringTy

    case Length(e) => tyOf(ctx,e) match {
      case StringTy => IntTy
      case _ => sys.error("Length: cannot find string here")
    }

    case Index(e1, e2) => (tyOf(ctx, e1),tyOf(ctx, e2)) match {
      case (StringTy, IntTy) => StringTy
      case _ => sys.error("Index : cannot find string or int")
    }

    case Concat(e1, e2) => (tyOf(ctx, e1),tyOf(ctx, e2)) match {
      case (StringTy, StringTy) => StringTy
      case _ => sys.error("Concat : must be two strings")
    }


    // Variables and let-binding
    case Var(x) => ctx(x)

    case Let(x,e1,e2) => tyOf(ctx + (x -> (tyOf(ctx,e1))), e2)

    case LetPair(x, y, e1, e2) =>  tyOf(ctx, e1) match{ //可以检查e1是否为Pair类型
      case PairTy(t1, t2) => tyOf(ctx + (x -> t1) + (y -> t2), e2)
      case _ => sys.error("Let pair's first argument must be a pair")
    }

    case LetFun(f, arg, ty, e1, e2) => {    //不能检查返回值，因为没有设定，参数类型检查要丢给e2中的Apply
      val ty2 = tyOf(ctx + (arg -> ty), e1)
      tyOf(ctx + (f -> FunTy(ty, ty2)), e2)
    }

    case LetRec(f, arg, xty, ty, e1, e2) => { //可以检查返回值，参数类型检查要丢给后面e2中的Apply
      val te1 = tyOf(ctx + (f -> FunTy(xty, ty)) + (arg -> xty), e1)
      if (te1 == ty) 
        tyOf(ctx + (f -> FunTy(xty, ty)), e2)
      else
        sys.error("Wrong return type!")
    }


    //Pairing

    case Pair(e1,e2) => PairTy(tyOf(ctx,e1),tyOf(ctx,e2))

    case First(e) => tyOf(ctx,e) match {
      case PairTy(t1, t2) => t1
    }

    case Second(e) => tyOf(ctx,e) match {
      case PairTy(t1, t2) => t2
    }

    //Functions

    case Lambda(x, ty, e) => FunTy(ty, tyOf(ctx + (x -> ty), e))

    case Apply(e1,e2) => tyOf(ctx, e1) match {
      case FunTy(t1, t2) =>
        if (t1 == tyOf(ctx, e2))
          t2
        else
          sys.error("Apply: type doesn't match of input")
      case _ =>
         sys.error("Apply: not a function")
    }

    case Rec(f, x, tyx, ty, e) => {
      if (tyOf(ctx + (f -> FunTy(tyx, ty)) + (x -> tyx),e) == ty)
        FunTy(tyx,ty )
      else
        sys.error("Wrong reture type")
    }

    case _ => sys.error("Amazing Error : No such type")
  }


  // ======================================================================
  // Part 4: Some simple programs
  // ======================================================================

  // The following examples illustrate how to embed L_CW1 source code into
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

  def fib: Expr = parser.parseStr("""
    rec fib(n:int):int.
      if (n == 0) then 0 else
      if (n == 1) then 1 else
        fib(n-1) + fib(n-2)""")


  // ======================================================================
  // Exercise 7: Substrings
  // ======================================================================

  def substring: Expr = parser.parseStr("""
    let comments = "lessorequal must be positive numbers" in
let comments2 = "check the suffix of the second string" in
let rec lessorequal(input: int*int):bool =
  let (a,b) = input in
  if (a==0) then true
  else if (b==0) then false
  else lessorequal(a-1,b-1) in
let rec slice(input: str *(int*int)):str =
  let (s,p) = input in
  let (pos,len) = p in
  if (len == 0) then ""
  else if (pos==length(s)) then ""
  else concat(index(s,pos),slice(s,(pos+1,len-1))) in
rec suffixcheck(input: str * str) : bool.
  let (s1,s2) = input in
  if lessorequal(length(s1),length(s2)) then
    if (s1 == slice(s2, (0, length(s1))))
    then true
    else suffixcheck(s1,slice(s2,(1, length(s2))))
  else false """)


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
        case e: Throwable => println("Error: " + e)
      }
    }
  }
}
