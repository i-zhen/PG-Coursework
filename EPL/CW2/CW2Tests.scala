import CW2._
import CW2.MyPrinter._
import CW2.Main._
import scala.util.Random

object CW2Tests {

  case class Test[A](
    description: String,
    test: A => Boolean,
    sample: () => A)

  case class Batch[A](
    description: String,
    tests: List[Test[A]])


  def runTest[A](test: Test[A]): Boolean = {
    test match {
      case Test(description,test,sample) => {
        try {
          val res = test(sample ());
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

  def runBatch[A](batch: => Batch[A]): (Integer,Integer) = {
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
        //val results = tests.map(runTest).filter(x => x)
        val results =
          for (t <- tests if (runTest(t)))
            yield (t);

        println("**************************************************************\n")
        return (new Integer(results.length),new Integer(tests.length))
      }
    }
  }

  // Exercise 1: quote, braces, anglebrackets.
  // Assumes that the printer DSL is implemented: if not,
  // look at the code explicitly.
  def quoteTest(): Test[Doc] =
    Test("Quote a document",
      { (doc: Doc) => print(quote(doc)) == "\"" + print(doc) + "\"" },
      () => text("hello world") )

  def bracesTest(): Test[Doc] =
    Test("Add braces to a document",
      { (doc: Doc) => print(braces(doc)) == "{" + print(doc) + "}" },
      () => text("hello world") )

  def angleBracketsTest(): Test[Doc] =
    Test("Quote a document",
      { (doc: Doc) => print(anglebrackets(doc)) == "<" + print(doc) + ">" },
      () => text("hello world") )

  // Exercise 2: sep function
  def commaSepTest(desc: String, expected: String, sample: List[Doc]): Test[List[Doc]] =
    Test("Separator test with commas" + " (" + desc + ")",
      {(docs: List[Doc]) =>
        print(sep(text(","), docs)) == expected},
      () => sample)

  def newlineSepTest(desc: String, expected: String, sample: List[Doc]): Test[List[Doc]] =
    Test("Separator test with semicolons" + " (" + desc +")",
      { (docs: List[Doc]) =>
        print(sep(line, docs)) == expected},
      () => sample)

  // Exercise 3: Printing DSL.
  // Now the fun really starts! :)

  // Firstly, check the basics individually.
  def nilTest(): Test[Doc] =
    Test("Nil", { (x: Doc) => print(x) == "" }, () => nil)

  def textTest(): Test[Doc] =
    Test("Text", { (x: Doc) => print(x) == "hello"}, () => text("hello"))

  def lineTest(): Test[Doc] =
    Test("Line", { (x: Doc) => print(x) == "\n"}, () => line)

  def appendTest(): Test[Doc] =
    Test("Append", { (x: Doc) => print(x) == "hello world" },
      () => text("hello ") <> text("world") )

  // Now, various variations on nest / unnest
  // Expected:
  // hello world
  def nestNoEffect(): Test[Doc] =
    Test("Nest with no effect", { (x: Doc) => print(x) == "hello world"},
      () => text("hello ") <> nest(2, text("world")))

  // Expected:
  // hello
  //   world
  def basicNestDoc: Doc =
    text("hello") <> nest(2, line <> text("world"))

  def basicNest(): Test[Doc] =
    Test("Basic nest", { (x: Doc) => print(x) == "hello\n  world"},
      () => basicNestDoc)

  // Expected:
  // hello
  //   world
  //     hi
  //   universe
  // bye
  def nestedNestDoc: Doc = {
    text("hello") <> nest(2, line <> text("world") <>
        nest(2, line <> text("hi")) <> line <> text("universe")) <> line <> text("bye")
  }

  def nestedNest(): Test[Doc] =
    Test("Nested nest", { (x: Doc) =>
      print(x) == "hello\n  world\n    hi\n  universe\nbye"},
        () => nestedNestDoc)
  // Expected:
  // hello world
  def noeffectUnnest1(): Test[Doc] =
    Test("Unnest has no effect on non-nested docs (1)",
      {(x: Doc) => print(x) == "hello world"}, () => unnest(text("hello ") <> text("world")))

  // Expected:
  // hello world
  def noeffectUnnest2(): Test[Doc] =
    Test("Unnest has no effect on non-nested docs (2)",
      {(x: Doc) => print(x) == "hello\nworld"}, () => unnest(text("hello") <> line <> text("world")))

  // Expected:
  // hello
  // world
  def nestInsideUnnest(): Test[Doc] =
    Test("Nest inside unnest = no nesting",  { (x: Doc) => print(x) == "hello\nworld" },
      () => unnest(nest(2, text("hello") <> line <> text("world"))))

  // Expected:
  // hello
  // world
  def unnestInsideNestBasic(): Test[Doc] =
    Test("Unnest inside nest = no nesting",
      { (x: Doc) => print(x) == "hello\nworld" },
      () => nest(2, unnest(text("hello") <> line <> text("world"))))


  def nestDistributes(): Test[Doc] =
    Test("Nest distributes over lines",
      { (x: Doc) =>
        print(text("hello") <> nest(2, line <> text("world") <> line <>
              text("hi") <> line <> text("universe"))) ==
        print(text("hello") <>
          nest(2, line <> text("world")) <>
          nest(2, line <> text("hi")) <>
          nest(2, line <> text("universe"))) }, () => nil )

  // Expected:
  // hello
  //   world
  // hi
  //   universe
  def nestThenUnnest(): Test[Doc] =
    Test("Nesting with inner unnest, followed by a doc at the original nesting level",
      { (x: Doc) =>
        print(x) == "hello\n  world\nhi\n  universe" },
      () => text("hello") <> nest(2, line <> text("world") <>
        unnest(line <> text("hi")) <> line <> text("universe")))

  // Expected:
  // hello
  //   world
  // hi
  // universe
  def nestThenUnnest2(): Test[Doc] =
    Test("Nesting with inner unnest, with another inner nest",
    { (x: Doc) =>
      print(x) == "hello\n  world\nhi\nuniverse"},
      () => nest(2, text("hello") <> line <> text("world") <>
        unnest(line <> text("hi") <> nest(2, line <> text("universe")))))

  def ifStatementDoc: Doc = {
    text("def f(x: Int) = {") <>
    // Nesting level: 2
    nest(2, line <> text("if (x < 1) {") <>
      // Nesting level: 4
      nest(2, line <> text("println(x + 1)")) <>
      // Nesting level: 2
      line <> text("}")
    ) <>
    // Nesting level: 0
    line <> text("}")
  }

  def ifStatement: Test[Doc] =
    Test("ifStatement example from TestCases",
    { (x: Doc) =>
      print(x) ==
        "def f(x: Int) = {\n  if (x < 1) {\n    println(x + 1)\n  }\n}"},
    () => ifStatementDoc
    // Nesting level: 0

  )

  def unnestInsideNestDoc: Doc = {
    text("not nested") <>
      nest(2, line <> text("nested at level 2") <>
        nest(2, line <> text("nested at level 4") <>
          unnest(line <> text("not nested") <>
            nest(2, line <> text("still not nested"))) <>
        line <> text("nested at level 4")) <>
      line <> text("nested at level 2")) <>
    line <> text("not nested")
  }

  def unnestInsideNest(): Test[Doc] = Test(
    "unnestInsideNest example from TestCases",
    { (x: Doc) => print(x) ==
"""not nested
  nested at level 2
    nested at level 4
not nested
still not nested
    nested at level 4
  nested at level 2
not nested"""},
  () => unnestInsideNestDoc  )


  // Exercises 4, 5, 6: Test by observation on sample documents
  def parseFromString(s: String): MiniMDExpr = {
      import MiniMDParser._
      val source = scala.io.Source.fromString(s)
      val lines = try source.mkString finally source.close()
      val paragraphs = MiniMDParser.tokeniseParagraphs(lines)
      val parsedParagraphs = paragraphs.flatMap((par: Paragraph) => parseParagraph(par))
      normalise(MDDoc(parsedParagraphs))
  }

  def mdRoundTrip(): Test[String] = {
    import MiniMDParser._
    Test("Generated MiniMD Parses using the MiniMD Parser",
      { (filename: String) =>
        val parsed = Main.getInput(filename)
        val genMd = print(MarkdownFormatter.format(parsed))
        val parsed2 = parseFromString(genMd)
        true }, () => "testMiniMD.md")
  }

  // Exercise 7:
  import Rng._

  def flipToIntGen(b: Boolean): Gen[Int] = {
    if (b) {
      fromList(List(1,2,3,4))
    } else {
      fromList(List(5,6,7,8))
    }
  }

  def testFlatMap(gen: Gen[Boolean]): Test[Gen[Boolean]] = {
    Test("flatMap (boolean gen): " + gen.get(),
      { g =>
        val testBool = g.get()
        if (testBool) {
          val res = g.flatMap({ _ => flipToIntGen(testBool) }).get()
          List(1,2,3,4).contains(res)
        } else {
          val res = g.flatMap({ _ => flipToIntGen(testBool) }).get()
          List(5,6,7,8).contains(res)
        }
      }, () => gen)
  }

  def testFlatMapTrue(): Test[Gen[Boolean]] = {
    testFlatMap(
      // Can't assume const is completed
      new Gen[Boolean] {
        def get() = true;
      })
  }

  def testFlatMapFalse(): Test[Gen[Boolean]] = {
    testFlatMap(
      // Can't assume const is completed
      new Gen[Boolean] {
        def get() = false;
      })
  }

  // Exercise 8

  // const
  def testConstBoolTrue(): Test[Boolean] = {
    Test ("Gen const: true",
      { (b: Boolean) => b }, () => const(true).get())
  }

  def testConstBoolFalse(): Test[Boolean] = {
    Test ("Gen const: false",
      { (b: Boolean) => !b }, () => const(false).get())
  }

  // flip
  def testFlip(): Test[Gen[Boolean]] = {
    Test ("Flip",
      { (g: Gen[Boolean]) =>
        // Of course, nondeterministic, but should
        // give some indication of whether this works...
        var n = 0;
        val lst =
          for (n <- 0 to 100)
            yield g.get()

          (lst.exists { (x: Boolean) => x == true}) && (lst.exists { (x: Boolean) => x == false})},
        () => flip)
    }


  // range

  def testNothingOutsideRange(min: Integer, max: Integer): Test[(Integer, Integer)] = {
    Test ("range: Nothing outside of given range (" + min + ", " + max + ")",
      { (pair: (Integer, Integer)) =>
        val min = pair._1
        val max = pair._2
        val g = range(min, max)
        var n = 0;
        val lst =
          for (n <- 0 to 100)
            yield g.get()
        lst.forall { (x: Integer) => x >= min && x <= max }

      },
      () => (min, max)
    )
  }

  def testRangeOneToTen(): Test[(Integer, Integer)] =
    testNothingOutsideRange(1, 10)

  def testConstZero(): Test[(Integer, Integer)] =
    testNothingOutsideRange(0, 0)

  // fromList

  // Test nothing's outside the range
  def testFromListElem(): Test[Gen[Integer]] = {
    val baseLst: List[Integer] = List(1,2,3,4,5)
    Test("fromList: All elements in source list",
      { (g: Gen[Integer]) =>
          var n = 0;
          val lst =
            for (n <- 0 to 100)
              yield g.get()

          baseLst.forall { x => lst.contains(x) } },
      () => fromList(baseLst))
  }

  // Test that the items aren't all the same
  def testFromListDifferent(): Test[Gen[Integer]] = {
    val baseLst: List[Integer] = List(1,2,3,4,5)
    Test("fromList: elements different",
      { (g: Gen[Integer]) =>
          var n = 0;
          val lst =
            for (n <- 0 to 100)
              yield g.get()

          lst.max != lst.min },
      () => fromList(baseLst))
  }


  // genFromList
  def testGenFromList(): Test[Gen[Integer]] = {
    lazy val gen1: Gen[Integer] = fromList(List(1))
    lazy val gen2: Gen[Integer] = fromList(List(2))
    lazy val gens = List(gen1, gen2)
    Test("genFromList",
      { (g: Gen[Integer]) =>
        var n = 0;
        val lst =
          for (n <- 0 to 100)
            yield g.get()
        lst.min == 1 && lst.max == 2
      }, () => genFromList(gens))
  }

  // genList
  def testGenList(): Test[Gen[Integer]] = {
    val lst: List[Integer] = List(1,2,3,4,5)
    Test("genList",
      { g =>
        val res: List[Integer] = genList(100, g).get()
        res.length == 100 && (res.min == 1 && res.max == 5) },
    () => fromList(lst))
  }


  def testStringGen(name: String, gen: => Gen[String],
    acceptable: List[String]): Test[Gen[String]] = {
    Test(name, { g => acceptable.contains(g.get()) },
      () => gen)
  }

  def testGenSectionText(): Test[Gen[String]] = {
    testStringGen("genSectionText", genSectionText,
      List("Chapter 1", "Introduction", "Conclusion"))
  }

  def testGenSubsectionText(): Test[Gen[String]] = {
    testStringGen("genSubsectionText", genSubsectionText,
      List("Section 1.1", "Table of Contents", "References"))
  }

  def testGenListitemText(): Test[Gen[String]] = {
    testStringGen("genListItemText", genListitemText,
      List("Apples", "Oranges", "Spaceship"))
  }

  def testGenLinkText(): Test[Gen[(String, String)]] = {
    Test("genLinkText",
      {(g: Gen[(String, String)]) =>
        val acceptable: List[(String, String)] =
          List(("Google", "http://www.google.com"),
            ("Facebook", "http://www.facebook.com"))
        acceptable.contains(g.get()) },
        () => genLink)
  }

  def testGenVerbatimText(): Test[Gen[String]] = {
    testStringGen("genVerbatim", genVerbatimText,
      List("== This isn't valid MiniMD ===\n", "*Neither_ _is' 'this*\n"))
  }

  def testGenFreeText(): Test[Gen[String]] = {
    testStringGen("genFreeText", genFreeText,
      List("It was a dark and stormy night", "It was the best of times"))
  }

  def testGenMiniMDExprRoot(): Test[Gen[MiniMDExpr]] = {
    Test("genMiniMDExpr root document type is MDDoc",
      { g =>
        val randomDoc = g.get()
        randomDoc match {
          case MDDoc(x) => true
          case _ => false
        }
      }, () => genMiniMDExpr(6))
  }

  def testGenMiniMDExprToplevels(): Test[Gen[MiniMDExpr]] = {
      def validSubdocType(d: MiniMDExpr) = d match {
        case MDPar(_) => true
        case MDBulletedList(_) => true
        case MDNumberedList(_) => true
        case MDSectionHeader(_) => true
        case MDSubsectionHeader(_) => true
        case MDVerbatim(_) => true
        case _ => false
      }
      Test("""genMiniMDExpr: MDDoc sub-doctypes are either MDPar,
              | MDBulletedList, MDNumberedList, MDSectionHeader, MDSubsectionHeader ,
              | or MDVerbatim""".stripMargin,
        { g =>
          val randomDoc = g.get()
          randomDoc match {
            case MDDoc(subdocs) => subdocs.forall { x => validSubdocType(x) }
            case _ => false
          }
        }, () => genMiniMDExpr(6))
    }


  def ex1Tests: Batch[Doc] =
    Batch[Doc]("Tests for exercise 1",
      List(quoteTest, bracesTest, angleBracketsTest))

  def ex2Tests: Batch[List[Doc]] =
    Batch("Tests for exercise 2",
    List(
      commaSepTest("hello world", "hello,world",
        List(text("hello"), text("world"))),

      commaSepTest("empty", "", List()),
      commaSepTest("singleton", "hello", List(text("hello"))),

      newlineSepTest("hello world", "hello\nworld",
        List(text("hello"), text("world"))),

      newlineSepTest("empty", "", List()),
      newlineSepTest("singleton", "hello", List(text("hello")))
    )
  )

  def printingDSLTests: Batch[Doc] =
    Batch("Pretty-printing DSL",
      List(nilTest, textTest, lineTest, appendTest, nestNoEffect,
        basicNest, nestedNest, noeffectUnnest1, noeffectUnnest2,
        nestInsideUnnest, unnestInsideNestBasic, nestDistributes,
        nestThenUnnest, nestThenUnnest2, ifStatement, unnestInsideNest)
  )

  def formatTests: Batch[String] = {
    Batch("Formatter Tests", List(mdRoundTrip))
  }

  def flatMapTests: Batch[Gen[Boolean]] = {
    Batch("flatMap", List(testFlatMapTrue, testFlatMapFalse))
  }

  def constTests: Batch[Boolean] = {
    Batch("Const tests", List(testConstBoolTrue, testConstBoolFalse))
  }

  def flipTests: Batch[Gen[Boolean]] = {
    Batch("Flip tests", List(testFlip))
  }

  def rangeTests: Batch[(Integer, Integer)] =
    Batch("Range tests", List(testRangeOneToTen, testConstZero))

  def fromListTests: Batch[Gen[Integer]] = {
    Batch("fromList tests", List(testFromListElem, testFromListDifferent))
  }

  def genFromListTests: Batch[Gen[Integer]] = {
    Batch("genFromList tests", List(testGenFromList))
  }

  def genListTests: Batch[Gen[Integer]] = {
    Batch("genList tests", List(testGenList))
  }

  def randomGenTests: Batch[Gen[String]] = {
    Batch("Random generator tests (Strings)",
      List(testGenSectionText, testGenSubsectionText,
        testGenListitemText, testGenVerbatimText,
        testGenFreeText))
  }

  def randomLinkGenTests: Batch[Gen[(String, String)]] = {
    Batch("Random generator tests (Links)",
      List(testGenLinkText))
  }

  def randomGenExprTests: Batch[Gen[MiniMDExpr]] = {
    Batch("Random generator tests (Expressions)",
      List(testGenMiniMDExprRoot, testGenMiniMDExprToplevels))
  }

  def main(args: Array[String]): Unit = {
    runBatch(ex1Tests)
    runBatch(ex2Tests)
    runBatch(printingDSLTests)
    runBatch(formatTests)
    runBatch(flatMapTests)
    runBatch(constTests)
    runBatch(flipTests)
    runBatch(rangeTests)
    runBatch(fromListTests)
    runBatch(genFromListTests)
    runBatch(genListTests)
    runBatch(randomGenTests)
    runBatch(randomGenExprTests)
    ()
  }

}

CW2Tests.main(Array())
// vim: set ts=2 sw=2 et sts=2:
