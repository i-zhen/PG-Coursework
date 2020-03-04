import CW1._

object CW1Marker {

  val rnd = scala.util.Random

  case class Test[A](
    description: String,
    test: A => Boolean,
    sample: A)

  case class Batch[A](
    description: String,
    tests: List[Test[A]])


  def runTest[A](test: Test[A]): Boolean = {
    test match {
      case Test(description,test,sample) => {
        try {
          val res = test(sample);
          if(res) {
            System.out.printf("* %-50s%s%n",description,"[Passed] *");
          } else {
            System.out.printf("* %-50s%s%n",description,"[Failed] *");
          }
          res;
        } catch{
          case e: Throwable => {
            System.out.printf("* %-50s%s%n",description,"[Failed] *");
            false;
          }
        }
      }
    }
  }

  def runBatch[A](batch: Batch[A]): (Integer,Integer) = {
    batch match {
      case Batch(desc,tests) =>{
        val stars = 62 - (desc.length + 2);
        val l = if ((stars % 2) == 0) {
          "*" * (stars / 2)
        } else {
          "*" * ((stars + 1) / 2)
        }

        val r = if ((stars % 2) == 0) {
          "*" * (stars / 2)
        } else {
          "*" * ((stars - 1) / 2)
        }

        println(l + " " + desc + " " + r)
        val results = tests.map(runTest).filter(x => x)
        println("**************************************************************\n")
        return (new Integer(results.length),new Integer(tests.length))
      }
    }
  }

  def aequiv(e1: Expr, e2:Expr): Boolean = {
    def equivVar(l: List[(Variable,Variable)], v1: Variable, v2: Variable): Boolean = l match {
      case Nil => v1 == v2
      case (x1,x2)::xs =>
        if (v1 == x1 || v2 == x2) {
          v1 == x1 && v2 == x2
        } else {
          equivVar(xs,v1,v2)
        }
    };
    def go(l: List[(Variable,Variable)], e1: Expr, e2: Expr): Boolean = (e1,e2) match {
      case (Num(n), Num(m)) => n == m
      case (Plus(e11,e12), Plus(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (Times(e11,e12), Times(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (Minus(e11,e12), Minus(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)

      case (Bool(b1), Bool(b2)) => b1 == b2
      case (Eq(e11,e12), Eq(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (IfThenElse(e10,e11,e12), IfThenElse(e20,e21,e22)) =>
        go(l,e10,e20) && go(l,e11,e21) && go(l,e12,e22)

      case (Str(s1), Str(s2)) => s1 == s2
      case (Length(e1), Length(e2)) =>
        go(l,e1,e2)
      case (Index(e11,e12), Index(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (Concat(e11,e12), Concat(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)

      case (Var(v1),Var(v2)) => equivVar(l,v1,v2)
      case (Let(x1,e11,e12),Let(x2,e21,e22)) =>
        go(l,e11,e21) && go((x1,x2)::l,e12,e22)
      case (LetFun(f1,x1,ty1,e11,e12),LetFun(f2,x2,ty2,e21,e22)) =>
        ty1 == ty2 && go((x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
      case (LetRec(f1,x1,ty11,ty12,e11,e12),LetRec(f2,x2,ty21,ty22,e21,e22)) =>
        ty11 == ty21 && ty12 == ty22 &&
        go((f1,f2)::(x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
      case (LetPair(x1,y1,e11,e12), LetPair(x2,y2,e21,e22)) =>
        go(l,e11,e21) && go((x1,x2)::(y1,y2)::l, e12,e22)

      case (Pair(e11,e12), Pair(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (First(e1), First(e2)) =>
        go(l,e1,e2)
      case (Second(e1), Second(e2)) =>
        go(l,e1,e2)

      case (Lambda(x1,t1,e1),Lambda(x2,t2,e2)) =>
        t1 == t2 && go((x1,x2)::l,e1,e2)
      case (Apply(e11,e12), Apply(e21,e22)) =>
        go(l,e11,e21) && go(l,e12,e22)
      case (Rec(f1,x1,ty11,ty12,e1),Rec(f2,x2,ty21,ty22,e2)) =>
        ty11 == ty21 && ty12 == ty22 &&
        go((f1,f2)::(x1,x2)::l,e1,e2)
      case (_,_) => false
    };
    go(Nil,e1,e2)
  }

  def substTests:List[Test[Expr]] = List(
    Test("Case for Bool",
      aequiv(
        subst(
          Bool(true),
          Var("z"),
          "x"),
        _),
      Bool(true)),
    Test("Substitution propagates under eq",
      aequiv(
        subst(
          Eq(Var("x"),Var("x")),
          Var("z"),
          "x"),
        _),
      Eq(Var("z"),Var("z"))),
    Test("Substitution propagates under if",
      aequiv(
        subst(
          IfThenElse(Var("x"),Var("x"),Var("x")),
          Var("z"),
          "x"),
        _),
      IfThenElse(Var("z"),Var("z"),Var("z"))),

    Test("Case for String",
      aequiv(
        subst(
          Str("foobar"),
          Var("z"),
          "x"),
        _),
      Str("foobar")),
    Test("Substitution propagates under length",
      aequiv(
        subst(
          Length(Var("x")),
          Var("z"),
          "x"),
        _),
      Length(Var("z"))),
    Test("Substitution propagates under index",
      aequiv(
        subst(
          subst(
            Index(Var("x"),Var("y")),
            Var("w"),
            "x"),
          Var("z"),
          "y"),
        _),
      Index(Var("w"),Var("z"))),
    Test("Substitution propagates under concat",
      aequiv(
        subst(
          subst(
            Concat(Var("x"),Var("y")),
            Var("w"),
            "x"),
          Var("z"),
          "y"),
        _),
      Concat(Var("w"),Var("z"))),

    Test("Substitution propagates under pairs",
      aequiv(
        subst(
          subst(
            Pair(Var("x"),Var("y")),
            Var("w"),
            "x"),
          Var("z"),
          "y"),
        _),
      Pair(Var("w"),Var("z"))),
    Test("Substitution propagates under fst",
      aequiv(
        subst(
          First(Var("x")),
          Var("z"),
          "x"),
        _),
      First(Var("z"))),
    Test("Substitution propagates under snd",
      aequiv(
        subst(
          Second(Var("x")),
          Var("z"),
          "x"),
        _),
      Second(Var("z"))),

    Test("Basic Lambda with different variable",
      aequiv(
        subst(
          Lambda("y",IntTy,Var("x")),
          Var("z"),
          "x"),
        _),
      Lambda("a",IntTy,Var("z"))),
    Test("Basic Lambda with same argument",
      aequiv(
        subst(
          Lambda("y",IntTy,Var("y")),
          Var("z"),
          "y"),
        _),
      Lambda("y",IntTy,Var("y"))),
    Test("Basic Lambda avoiding capture",
      aequiv(
        subst(
          Lambda("y",IntTy,Plus(Var("x"),Var("y"))),
          Plus(Var("y"),Var("y")),
          "x"),
        _),
      Lambda("a",IntTy,Plus(Plus(Var("y"),Var("y")),Var("a")))),
    Test("Substitution propagates under apply",
      aequiv(
        subst(
          subst(
            Apply(Var("x"),Var("y")),
            Var("w"),
            "x"),
          Var("z"),
          "y"),
        _),
      Apply(Var("w"),Var("z"))),
    Test("Basic Rec with different variable",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Var("z"),
          "x"),
        _),
      Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("z"))))),
    Test("Basic Rec with same function name",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Var("z"),
          "f"),
        _),
      Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x"))))),
    Test("Basic Rec with same arg name",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Var("z"),
          "y"),
        _),
      Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x"))))),
    Test("Basic Rec avoiding capture - function",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Var("f"),
          "x"),
        _),
      Rec("g","y",IntTy,IntTy,Apply(Var("g"),Plus(Var("y"),Var("f"))))),
    Test("Basic Rec avoiding capture - argument",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Var("y"),
          "x"),
        _),
      Rec("f","z",IntTy,IntTy,Apply(Var("f"),Plus(Var("z"),Var("y"))))),
    Test("Basic Rec avoiding capture - both",
      aequiv(
        subst(
          Rec("f","y",IntTy,IntTy,Apply(Var("f"),Plus(Var("y"),Var("x")))),
          Apply(Var("f"),Var("y")),
          "x"),
        _),
      Rec("g","z",
        IntTy,IntTy,Apply(Var("g"),Plus(Var("z"),Apply(Var("f"),Var("y"))))))
  )

  def exp1 =
    LetFun("f","x",IntTy,Plus(Var("x"),Var("x")),Apply(Var("f"),Num(1)))

  def dsExp1 =
    Let("f",Lambda("x",IntTy,Plus(Var("x"),Var("x"))),Apply(Var("f"),Num(1)))

  def desugarTests:List[Test[Expr]] = List(
    Test("Basic Let Pair",
      aequiv(
        desugar(
          parser.parseStr(
            """let (x,y) = (1,2) in x + y""")),
        _),
      Let("p",Pair(Num(1),Num(2)),Plus(First(Var("p")),Second(Var("p"))))),
    Test("Basic Let Fun",
      aequiv(
        desugar(
          parser.parseStr(
            """let fun f(x:int) = x + x in f 1 """)),
        _),
      Let("f",Lambda("x",IntTy,Plus(Var("x"),Var("x"))),
        Apply(Var("f"),Num(1)))),
    Test("Basic Let Rec",
      aequiv(
        desugar(
          parser.parseStr(
            """let rec f(x:int):int = f(x+x) in f 1 """)),
        _),
      Let("f",Rec("f","x",IntTy,IntTy,Apply(Var("f"),Plus(Var("x"),Var("x")))),
        Apply(Var("f"),Num(1)))),

    Test("Case for Bool",
      aequiv(
        desugar(
          parser.parseStr(
            """true""")),
        _),
      Bool(true)),
    Test("Desugar propagates under eq",
      aequiv(
        desugar(
          Eq(exp1,exp1)),
        _),
      Eq(dsExp1,dsExp1)),
    Test("Desugar propagates under if-statement",
      aequiv(
        desugar(
          IfThenElse(exp1,exp1,exp1)),
        _),
      IfThenElse(dsExp1,dsExp1,dsExp1)),

    Test("Case for String",
      aequiv(
        desugar(
          parser.parseStr(
            """ "foobar" """)),
        _),
      Str("foobar")),
    Test("Desugar propagates under length",
      aequiv(
        desugar(
          Length(exp1)),
        _),
      Length(dsExp1)),
    Test("Desugar propagates under index",
      aequiv(
        desugar(
         Index(exp1,exp1)),
        _),
      Index(dsExp1,dsExp1)),
    Test("Desugar propagates under concat",
      aequiv(
        desugar(
          Concat(exp1,exp1)),
        _),
      Concat(dsExp1,dsExp1)),

    Test("Case for Var",
      aequiv(
        desugar(Var("x")),
        _),
      Var("x")),
    Test("Desugar propagates under let",
      aequiv(
        desugar(
          Let("a",exp1,exp1)),
          _),
      Let("a",dsExp1,dsExp1)),

    Test("Desugar propagates under pairs",
      aequiv(
        desugar(
          Pair(exp1,exp1)),
        _),
      Pair(dsExp1,dsExp1)),
    Test("Desugar propagates under fst",
      aequiv(
        desugar(
          First(exp1)),
        _),
      First(dsExp1)),
    Test("Desugar propagates under snd",
      aequiv(
        desugar(
          Second(exp1)),
        _),
      Second(dsExp1)),

    Test("Desugar propagates under lambda",
      aequiv(
        desugar(
          Lambda("a",IntTy,exp1)),
          _),
      Lambda("a",IntTy,dsExp1)),
    Test("Desugar propagates under apply",
      aequiv(
        desugar(
          Apply(exp1,exp1)),
          _),
      Apply(dsExp1,dsExp1)),
    Test("Desugar propagates under rec",
      aequiv(
        desugar(
          Rec("a","b",IntTy,IntTy,exp1)),
          _),
      Rec("a","b",IntTy,IntTy,dsExp1))
  )

  def primitiveTests:List[Test[Value]] = List(
    Test("Multiplication",
      (x => x == Value.multiply(NumV(2),NumV(4))),
      NumV(8)),
    Test("Eq Int (True)",
      (x => x == Value.eq(NumV(2),NumV(2))),
      BoolV(true)),
    Test("Eq Int (False)",
      (x => x == Value.eq(NumV(2),NumV(3))),
      BoolV(false)),
    Test("Eq String (True)",
      (x => x == Value.eq(StringV("foo"),StringV("foo"))),
      BoolV(true)),
    Test("Eq String (False)",
      (x => x == Value.eq(StringV("foo"),StringV("bar"))),
      BoolV(false)),
    Test("Eq Bool (True)",
      (x => x == Value.eq(BoolV(true),BoolV(true))),
      BoolV(true)),
    Test("Eq Bool (False)",
      (x => x == Value.eq(BoolV(true),BoolV(false))),
      BoolV(false)),
    Test("Length \"\"",
      (x => x == Value.length(StringV(""))),
      NumV(0)),
    Test("Length \"foobar\"",
      (x => x == Value.length(StringV("foobar"))),
      NumV(6)),
    Test("Index \"foobar\" 0",
      (x => x == Value.index(StringV("foobar"),NumV(0))),
      StringV("f")),
    Test("Index \"foobar\" 1",
      (x => x == Value.index(StringV("foobar"),NumV(1))),
      StringV("o")),
    Test("Index \"foobar\" 5",
      (x => x == Value.index(StringV("foobar"),NumV(5))),
      StringV("r")),
    Test("Concat \"\" \"foobar\"",
      (x => x == Value.concat(StringV(""),StringV("foobar"))),
      StringV("foobar")),
    Test("Concat \"foobar\" \"\"",
      (x => x == Value.concat(StringV("foobar"),StringV(""))),
      StringV("foobar")),
    Test("Concat \"foo\" \"bar\"",
      (x => x == Value.concat(StringV("foo"),StringV("bar"))),
      StringV("foobar"))
  )

  def evalTests:List[Test[Value]] = List(
    Test("Case for Bool (True)",
      (x => x == eval(Map.empty,Bool(true))),
      BoolV(true)),
    Test("Case for Bool (False)",
      (x => x == eval(Map.empty,Bool(false))),
      BoolV(false)),
    Test("Eq Int (True)",
      (x => {
        val i = rnd.nextInt()
        x == eval(Map.empty,Eq(Num(i),Num(i)))
      }),
      BoolV(true)),
    Test("Eq Int (False)",
      (x => {
        val i = rnd.nextInt()
        x == eval(Map.empty,Eq(Num(i),Num(i-1)))
      }),
      BoolV(false)),
    Test("Eq String (True)",
      (x => {
        val i = rnd.nextString(10)
        x == eval(Map.empty,Eq(Str(i),Str(i)))
      }),
      BoolV(true)),
    Test("Eq String (False)",
      (x => {
        val i = rnd.nextString(10)
        x == eval(Map.empty,Eq(Str(i),Str(i+i)))
      }),
      BoolV(false)),
    Test("Eq Bool (True)",
      (x => {
        val i = rnd.nextBoolean()
        x == eval(Map.empty,Eq(Bool(i),Bool(i)))
      }),
      BoolV(true)),
    Test("Eq Bool (False)",
      (x => {
        val i = rnd.nextBoolean()
        x == eval(Map.empty,Eq(Bool(i),Bool(!i)))
      }),
      BoolV(false)),
    Test("If (True)",
      (x =>
        x == eval(Map.empty,IfThenElse(Bool(true),
          Num(1),
          Num(2)))),
      NumV(1)),
    Test("If (False)",
      (x =>
        x == eval(Map.empty,IfThenElse(Bool(false),
          Num(1),
          Num(2)))),
      NumV(2)),
    Test("Case for String",
      (x => {
        val i = rnd.nextString(10)
        StringV(i) == eval(Map.empty,Str(i))
      }),
      StringV("ignore")),
    Test("Length",
      (x => {
        val i = rnd.nextInt(1000)
        val s = rnd.nextString(i)
        NumV(i) == eval(Map.empty,Length(Str(s)))
      }),
      StringV("ignore")),
    Test("Index",
      (x => {
        val i = rnd.nextInt(1000)
        val s = rnd.nextString(1000)
        StringV(s.apply(i).toString) == eval(Map.empty,Index(Str(s),Num(i)))
      }),
      StringV("ignore")),
    Test("Concat",
      (x => {
        val s = rnd.nextString(10)
        val s1 = rnd.nextString(10)
        StringV(s + s1) == eval(Map.empty,Concat(Str(s),Str(s1)))
      }),
      StringV("ignore")),
    Test("Var",
      (x => x == eval(Map.empty + ("x" -> x),Var("x"))),
      NumV(0)),
    Test("Let empty env",
      (x => x == eval(Map.empty,Let("x",Num(0),Var("x")))),
      NumV(0)),
    Test("Let shadow env",
      (x => x == eval(Map.empty + ("x" -> (NumV(1))),
        Let("x",Num(0),Var("x")))),
      NumV(0)),
    Test("Pair",
      (x => x == eval(Map.empty,Pair(Pair(Num(0),Num(0)),Num(1)))),
      PairV(PairV(NumV(0),NumV(0)),NumV(1))),
    Test("Fst",
      (x => x == eval(Map.empty,First(Pair(Pair(Num(0),Num(0)),Num(1))))),
      PairV(NumV(0),NumV(0))),
    Test("Snd",
      (x => x == eval(Map.empty,Second(Pair(Num(0),Pair(Num(1),Num(1)))))),
      PairV(NumV(1),NumV(1))),
    Test("Lambda - empty",
      (x => x == eval(Map.empty,Lambda("x",IntTy,Var("x")))),
      ClosureV(Map.empty,"x",Var("x"))),
    Test("Lambda - non-empty",
      (x => x == eval(Map.empty + ("x" -> NumV(0)),
        Lambda("x",IntTy,Var("x")))),
      ClosureV(Map.empty + ("x" -> NumV(0)),"x",Var("x"))),
    Test("Rec - empty",
      (x => x == eval(Map.empty,Rec("f","x",IntTy,IntTy,Var("x")))),
      RecV(Map.empty,"f","x",Var("x"))),
    Test("Rec - non-empty",
      (x => x == eval(Map.empty + ("x" -> NumV(0)),
        Rec("f","x",IntTy,IntTy,Var("x")))),
      RecV(Map.empty + ("x" -> NumV(0)),"f","x",Var("x"))),
    Test("Apply Lambda empty env",
      (x => x == eval(Map.empty,
        Apply(Lambda("x",IntTy,Var("x")),Num(1)))),
      NumV(1)),
    Test("Apply Lambda bound env",
      (x => x == eval(Map.empty + ("x" -> NumV(0)),
        Apply(Lambda("x",IntTy,Var("x")),Num(1)))),
      NumV(1)),
    Test("Apply Evaluates Fun",
      (x => x == eval(Map.empty + ("x" -> NumV(0)),
        Apply(Apply(Lambda("x",IntTy,Var("x")),
          Lambda("x",IntTy,Var("x")))
          ,Num(1)))),
      NumV(1)),
    Test("Case for Rec without recursion",
      (x => x == eval(Map.empty,
        Apply(Rec("f","x",IntTy,IntTy,Var("x")),Num(1)))),
      NumV(1)),
    Test("Case for Rec with recursion",
      (x => x == eval(Map.empty + ("y" -> NumV(10)),
        Apply(Rec("f","x",IntTy,IntTy,
          IfThenElse(Eq(Var("x"),Var("y")),
            Num(0),
            Plus(Num(1),
              Apply(Var("f"),Plus(Var("x"),Num(1))))))
          ,Num(0)))),
      NumV(10))
  )

  def typeOfTests:List[Test[Type]] = List(
    Test("Subtraction",
      (x => x == tyOf(Map.empty,
        Minus(Num(1),Num(1)))),
      IntTy),
    Test("Multiplication",
      (x => x == tyOf(Map.empty,
        Times(Num(1),Num(1)))),
      IntTy),
    Test("Case for Bool (True)",
      (x => x == tyOf(Map.empty,
        Bool(true))),
      BoolTy),
    Test("Case for Bool (False)",
      (x => x == tyOf(Map.empty,
        Bool(false))),
      BoolTy),
    Test("Eq Int",
      (x => x == tyOf(Map.empty,
        Eq(Num(1),Num(2)))),
      BoolTy),
    Test("Eq String",
      (x => x == tyOf(Map.empty,
        Eq(Str("foobar"),Str("baz")))),
      BoolTy),
    Test("Eq Bool",
      (x => x == tyOf(Map.empty,
        Eq(Bool(true),Bool(false)))),
      BoolTy),
    Test("Eq (ill-typed)",
      (x => try {
        tyOf(Map.empty,
          Eq(Bool(true),Num(1)));
        false
      } catch {
        case e:Throwable => true
      }),
      BoolTy),
    Test("If Then Else",
      (x => x == tyOf(Map.empty,
        IfThenElse(Eq(Num(1),Num(2)),Num(10),Num(11)))),
      IntTy),
    Test("If Then Else (ill-typed condition)",
      (x => try {
        tyOf(Map.empty,
          IfThenElse(Num(1),Num(10),Num(11)));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("If Then Else (different branches)",
      (x => try {
        tyOf(Map.empty,
          IfThenElse(Eq(Num(1),Num(2)),Num(10),Bool(true)));
        false;
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Case for String",
      (x => {
        val i = rnd.nextString(10)
        x == tyOf(Map.empty,Str(i))
      }),
      StringTy),
    Test("Length",
      (x => x == tyOf(Map.empty,
        Length(Str("foo")))),
      IntTy),
    Test("Length (ill-typed)",
      (x => try {
        tyOf(Map.empty,
          Length(Num(3)));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Index",
      (x => x == tyOf(Map.empty,
        Index(Str("foo"),Num(0)))),
      StringTy),
    Test("Index (ill-typed string)",
      (x => try {
        tyOf(Map.empty,
          Index(Num(0),Num(0)));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Index (ill-typed index)",
      (x => try {
        tyOf(Map.empty,
          Index(Str("foo"),Bool(true)));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Concat",
      (x => x == tyOf(Map.empty,
        Concat(Str("foo"),Str("bar")))),
      StringTy),
    Test("Concat (ill-typed 1)",
      (x => try {
        tyOf(Map.empty,
          Concat(Num(3),Str("bar")));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Concat (ill-typed 2)",
      (x => try {
        tyOf(Map.empty,
          Concat(Str("foo"),Num(4)));
        false
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Pair",
      (x => x == tyOf(Map.empty,
        Pair(Str("foo"),Str("bar")))),
      PairTy(StringTy,StringTy)),
    Test("First",
      (x => x == tyOf(Map.empty,
        First(Pair(Str("foo"),Str("bar"))))),
      StringTy),
    Test("First (ill-typed)",
      (x => try {
        x == tyOf(Map.empty,
          First(Str("bar")));
        false
      } catch {
        case e:Throwable => true
      }),
      StringTy),
    Test("Second",
      (x => x == tyOf(Map.empty,
        Second(Pair(Str("foo"),Num(3))))),
      IntTy),
    Test("Second (ill-typed)",
      (x => try {
        x == tyOf(Map.empty,
          Second(Str("bar")));
        false
      } catch {
        case e:Throwable => true
      }),
      StringTy),
    Test("Lambda Int ID",
      (x => x == tyOf(Map.empty,
        Lambda("x",IntTy,Var("x")))),
      FunTy(IntTy,IntTy)),
    Test("Rec Int ID",
      (x => x == tyOf(Map.empty,
        Rec("f","x",IntTy,IntTy,Var("x")))),
      FunTy(IntTy,IntTy)),
    Test("Rec Int Recur",
      (x => x == tyOf(Map.empty,
        Rec("f","x",IntTy,IntTy,Apply(Var("f"),Var("x"))))),
      FunTy(IntTy,IntTy)),
    Test("Apply",
      (x => x == tyOf(Map.empty,
        Apply(Lambda("x",IntTy,Var("x")),Num(3)))),
      IntTy),
    Test("Apply (ill-typed domain)",
      (x => try {
        x == tyOf(Map.empty,
          Apply(Lambda("x",IntTy,Var("x")),Bool(true)));
        false;
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Apply (ill-typed applier)",
      (x => try {
        x == tyOf(Map.empty,
          Apply(Num(3),Bool(true)));
        false;
      } catch {
        case e:Throwable => true
      }),
      IntTy),
    Test("Let Fun Int ID",
      (x => x == tyOf(Map.empty,
        LetFun("f","x",IntTy,Var("x"),Var("f")))),
      FunTy(IntTy,IntTy)),
    Test("Let Fun Int App",
      (x => x == tyOf(Map.empty,
        LetFun("f","x",IntTy,Var("x"),Apply(Var("f"),Num(3))))),
      IntTy),
    Test("Let Rec Int ID",
      (x => x == tyOf(Map.empty,
        LetRec("f","x",IntTy,IntTy,Var("x"),Var("f")))),
      FunTy(IntTy,IntTy)),
    Test("Let Rec Int Recur",
      (x => x == tyOf(Map.empty,
        LetRec("f","x",IntTy,IntTy,Apply(Var("f"),Var("x")),Var("f")))),
      FunTy(IntTy,IntTy)),
    Test("Let Rec Int App",
      (x => x == tyOf(Map.empty,
        LetRec("f","x",IntTy,IntTy,Apply(Var("f"),Var("x")),Apply(Var("f"),Num(3))))),
      IntTy),
    Test("Let Pair ID",
      (x => x == tyOf(Map.empty,
        LetPair("x","y",Pair(Num(1),Num(2)),Pair(Var("x"),Var("y"))))),
      PairTy(IntTy,IntTy)),
    Test("Let Pair (ill-typed pair)",
      (x => try {
        x == tyOf(Map.empty,
          LetPair("x","y",Num(3),Pair(Var("x"),Var("y"))));
        false
      } catch {
        case e:Throwable => true
      }),
      PairTy(IntTy,IntTy))
  )

  def simpleProgramTests:List[Test[Expr]] = List(
    Test("Fib has the correct type",
      (x => tyOf(Map.empty,fib) == FunTy(IntTy,IntTy)),
      Num(0)),
    Test("Substring has the correct type",
      (x => tyOf(Map.empty,substring) ==
        FunTy(PairTy(StringTy,StringTy),BoolTy)),
      Num(0)),
    Test("Fib 1",
      (x => eval(Map.empty,Apply(fib,Num(1))) ==
        NumV(1)),
      Num(0)),
    Test("Fib 2",
      (x => eval(Map.empty,Apply(fib,Num(1))) ==
        NumV(1)),
      Num(0)),
    Test("Fib 8",
      (x => eval(Map.empty,Apply(fib,Num(8))) ==
        NumV(21)),
      Num(0)),
    Test("Fib 12",
      (x => eval(Map.empty,Apply(fib,Num(12))) ==
        NumV(144)),
      Num(0)),
    Test("Substring '' 'foo'",
      (x => eval(Map.empty,desugar(Apply(substring,
        Pair(Str(""),Str("foo"))))) ==
        BoolV(true)),
      Num(0)),
    Test("Substring 'needle' 'haystackneedlehaystack'",
      (x => eval(Map.empty,desugar(Apply(substring,
        Pair(Str("needle"),Str("haystackneedlehaystack"))))) ==
        BoolV(true)),
      Num(0)),
    Test("Substring 'needle' 'haystackneedlhaystack'",
      (x => eval(Map.empty,desugar(Apply(substring,
        Pair(Str("needle"),Str("haystackneedlhaystack"))))) ==
        BoolV(false)),
      Num(0)),
    Test("Substring 'needle' 'haystackneedle'",
      (x => eval(Map.empty,desugar(Apply(substring,
        Pair(Str("needle"),Str("haystackneedle"))))) ==
        BoolV(true)),
      Num(0))
  )

  def subst_b = Batch("Substitution",substTests)
  def desug = Batch("Desugaring",desugarTests)
  def opers = Batch("Operation",primitiveTests)
  def evals = Batch("Evaluation",evalTests)
  def typechecks = Batch("Type-Checking",typeOfTests)
  def simpleProg = Batch("Simple Programs",simpleProgramTests)

  def main(args:Array[String]):Unit = {
    val subst_res      = runBatch(subst_b)
    val desug_res      = runBatch(desug)
    val opers_res      = runBatch(opers)
    val evals_res      = runBatch(evals)
    val typechecks_res = runBatch(typechecks)
    val simpleProg_res = runBatch(simpleProg)
    val total = (subst_res._1 + desug_res._1 +
      opers_res._1 + evals_res._1 + typechecks_res._1 +
      simpleProg_res._1,
      subst_res._2 + desug_res._2 +
        opers_res._2 + evals_res._2 + typechecks_res._2 +
        simpleProg_res._2
    )


    println("*************************** Results **************************")
    System.out.printf("* %-53s%2d/%2d *%n","Substitution",
      subst_res._1,subst_res._2);

    System.out.printf("* %-53s%2d/%2d *%n","Desugaring",
      desug_res._1,desug_res._2);

    System.out.printf("* %-53s%2d/%2d *%n","Operations",
    opers_res._1,opers_res._2);

    System.out.printf("* %-53s%2d/%2d *%n","Evaluation",
    evals_res._1,evals_res._2);

    System.out.printf("* %-53s%2d/%2d *%n","Type-Checking",
      typechecks_res._1,typechecks_res._2);

    System.out.printf("* %-53s%2d/%2d *%n","Simple Programs",
      simpleProg_res._1,simpleProg_res._2);

    System.out.printf("* %-51s%3d/%3d *%n","TOTAL",
    new Integer(total._1), new Integer(total._2));

    println("**************************************************************\n")


  }

}
