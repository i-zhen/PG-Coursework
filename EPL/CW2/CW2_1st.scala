// Because I confused with the meaning of the questions, I discussed with Zhu young about that.
/*
scala> :load TestCases.scala
Loading TestCases.scala...
import CW2._
import CW2.MyPrinter._
defined type alias Test
test: (test: Test)Unit
helloWorldPlain: Test = (helloWorldPlain,<function2>)
helloWorldNewline: Test = (helloWorldNewline,<function2>)
helloWorldNewlineNest: Test = (helloWorldNewlineNest,<function2>)
helloWorldNewlineNotNested: Test = (helloWorldNewlineNotNested,<function2>)
ifStatement: Test = (ifStatement,<function2>)
unnestInsideNest: Test = (unnestInsideNest,<function2>)
Test helloWorldPlain
----------------------------
helloworld
----------------------------
Test helloWorldNewline
----------------------------
hello
world
----------------------------
Test helloWorldNewlineNest
----------------------------
hello
  world
----------------------------
Test helloWorldNewlineNotNested
----------------------------
hello
world
----------------------------
Test ifStatement
----------------------------
def f(x: Int) = {
  if (x < 1) {
    println(x + 1);
  }
}
----------------------------
Test unnestInsideNest
----------------------------
not nested
  nested at level 2
    nested at level 4
not nested
still not nested
    nested at level 4
  nested at level 2
not nested
----------------------------
*/

import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

object CW2 {

  /* =====  Abstract syntax tree for MiniMD  ===== */
  abstract class MiniMDExpr
  // A block of MiniMD expressions. The top-level of a program is a MDDoc.
  case class MDDoc(contents: List[MiniMDExpr]) extends MiniMDExpr

  // A paragraph of free text / bold / italic / section headers
  case class MDPar(contents: List[MiniMDExpr]) extends MiniMDExpr
  case class MDVerbatim(contents: String) extends MiniMDExpr

  // Free text
  case class MDFreeText(text: String) extends MiniMDExpr
  case class MDBold(text: String) extends MiniMDExpr
  case class MDItalic(text: String) extends MiniMDExpr
  case class MDUnderlined(text: String) extends MiniMDExpr


  // List items
  case class MDListItem(exprs: List[MiniMDExpr]) extends MiniMDExpr

  case class MDBulletedList(listItems: List[MDListItem]) extends MiniMDExpr
  case class MDNumberedList(listItems: List[MDListItem]) extends MiniMDExpr

  // Sections; `text` is the section header name.
  case class MDSectionHeader(text: String) extends MiniMDExpr
  case class MDSubsectionHeader(text: String) extends MiniMDExpr

  // Links
  case class MDLink(text: String, url: String) extends MiniMDExpr


  /* ===== Printing Language ===== */
  import scala.language.implicitConversions


  // ======================================================================
  // Part 1: Pretty-printing
  // ======================================================================

  trait Printer {
    // The abstract Doc type
    type Doc

    // An empty document
    val nil : Doc

    // A block of text
    def text(s: String): Doc

    // A line break / newline
    val line: Doc

    // Append two Docs together
    def append(x:Doc, y: Doc): Doc

    // A doc which is nested to a certain level.
    def nest(i: Int, doc: Doc): Doc

    // A doc whose content is rendered without indentation
    // (nesting is suspended)
    def unnest(doc: Doc): Doc

    // A method which prints the Doc to a string.
    def print(doc: Doc): String

    // some Scala incantations to allow infix <> document append operation
    class AppendAssoc(x: Doc) {
      def <> (y: Doc): Doc = append(x,y)
    }
    implicit def doc2AppendAssoc(x: Doc): AppendAssoc = new AppendAssoc(x)



    // ======================================================================
    //  Exercise 1
    // ======================================================================

    def quote(d1: Doc): Doc = text("\"") <> d1 <> text("\"")

    def braces(d1: Doc): Doc = text("{") <> d1 <> text("}")

    def anglebrackets(d1: Doc): Doc = text("<") <> d1 <> text(">")

    /* ======================================================================
     *  Exercise 2
     * ====================================================================== */

     def sep(d: Doc, ds: List[Doc]): Doc = ds match {
       case Nil => text("")
       case x::Nil => x
       case x::xs => x <> d <> sep(d, xs)
     }

  }


  // ======================================================================
  // Exercise 3
  // ======================================================================

  //  The following instance is a stub, provided just to make the
  // rest of the code compile.

  type FDoc = (Int, Boolean) => String

  /*
  abstract class DocAST

  object StatefulPrinter extends Printer{
    type Doc = String
    val nil = ""
    def text(s: String) = sys.error("TODO")
    val line = ""
    def append(x:Doc, y: Doc) = sys.error("TODO")
    def nest(i: Int, doc: Doc) = sys.error("TODO")
    def unnest(doc: Doc) = sys.error("TODO")
    def print(doc: Doc) = sys.error("TODO")
  }
  */

  object MyPrinter extends Printer{
    type Doc = FDoc

    def indent(lev : Int, ifSus : Boolean) : String ={
      if (ifSus) "" else {" " * lev}
    }

    val nil = {(lev : Int, ifSus : Boolean) => "" }

    def text(str: String): Doc =  {
      (lev : Int, ifSus : Boolean) => str
    }

    val line = {(lev:Int, ifSus:Boolean)    => "\n" }
    /*
     * 我在写这段程序的时候，尚未完全理解缩进到底要用在哪些地方。所以我单独实现缩进indent。
     * 并且在语义上让 append nest 以及 unnest的返回值更具可读性，因此实现的方式看上去比较复杂。
     * 实际上在理解了缩进只在换行后产生意义时，我们可以简写append，得到线性复杂度的解。
     * 需要强化英文理解能力，这样才能彻底看懂Handout上的要求以及老师的出题用意。
     */

    def append(x:Doc, y: Doc) = {
      val xRes = x(0, false)    //we need eagar evaluation here, memorize them, time complexity is O(n^2)
      //每次构造，我们要把子结构重新计算一遍，所以是平方的复杂度
      //比如text("a")<>text("b")<>text("c")<>text("d")
      //(text("a")<>text("b"))<>text("c")
      //(text("a")<>text("b")<>text("c"))<>("d")，abc的部分中，text("a")<>text("b")被重复计算了。
      val yRes = y(0, false)
      (lev: Int, ifSus: Boolean) =>{
        lazy val accum = 0;
        lazy val flag  = false;
        (xRes == "\n",yRes == "\n")match{
          //if we use x(0, false) here, time complexity is O(2^n)
          //assume the time complexity of (xRes + yRes) is X.
          //this function has the complexity of Y = 2 * X.
          //and also X = 2 * (X - 1)
          case (true, true)   => "\n"  + indent(lev + accum, ifSus || flag) +
                                 "\n"  + indent(lev + accum, ifSus || flag)
          case (true, false)  => "\n"  + indent(lev + accum, ifSus || flag) +
                                 y(lev + accum, ifSus || flag)
          case (false, true)  => x(lev + accum, ifSus || flag)              +
                                 "\n"  + indent(lev + accum, ifSus || flag)
          case (false, false) => x(lev + accum, ifSus || flag)              +
                                 y(lev + accum, ifSus || flag)
        }
      }
    }

    def nest(i: Int, doc: Doc) = {
      (lev : Int, ifSus: Boolean) =>
        lazy val accum = i;
        lazy val flag  = false;
        doc(lev + accum, flag || ifSus)
    }

    def unnest(doc: Doc) = {
      (lev : Int, ifSus: Boolean) =>
        lazy val accum = 0;
        lazy val flag  = true;
        doc(lev + accum, flag || ifSus)
    }

    // x : FDoc (0, false) calls the function which the indentation level is 0 and unnest is false

    def print(doc: Doc)  = {
      doc(0, false)
    }
  }

  // Import it for use in the rest of the program
  import MyPrinter._

  // A Formatter[T] knows how to turn T into a Doc.
  trait Formatter[T] {
    // The abstract method that needs to be implemented.
    def format(e: T): Doc
    // The method formatList applies format to each element of a list, concatenating the results
    // It can be called from format().
    def formatList(xs: List[T]): Doc = sep(nil,xs.map{x: T => format(x)})
  }

  // ======================================================================
  // Exercise 4
  // ======================================================================

  // counter with closure feature. Because of variable, I don't use this, just an implementation
  def increment() : () => Int ={
    var i = 0
    return {() => i = i + 1; i}
  }

  val inc = increment()

  object MarkdownFormatter extends Formatter[MiniMDExpr] {

    def format(e: MiniMDExpr) = e match{
      case MDDoc(xs) =>
        formatList(xs)
      case MDPar(xs) =>
        formatList(xs) <>
        line           <>
        line
      case MDVerbatim(cont) =>
        text("{{{")    <>
        line           <>
        text(cont)     <>
        text("}}}")    <>
        line

      case MDFreeText(cont) =>
        text(cont)
      case MDBold(cont) =>
        text("*") <> text(cont) <> text("*")
      case MDItalic(cont) =>
        text("`") <> text(cont) <> text("`")
      case MDUnderlined(cont) =>
        text("_") <> text(cont) <> text("_")

      case MDListItem(xs) =>
        formatList(xs)          <>
        line
      case MDBulletedList(xs) =>
        text("* ")                  <>
        sep(text("* "),
            xs.map{x => format(x)}) <>
        line

      //generator edtion
      case MDNumberedList(xs) =>
        sep(nil,
            for(x <- xs.zipWithIndex) yield(
                text((x._2 + 1) + ". ")      <>
                format(x._1)))               <>
        line
      /* with increment
      case MDNumberedList(xs) =>
        sep(nil,
            for(x <- xs) yield text(inc() + ". ")   <> format(x)) <>
        line
      */
      case MDSectionHeader(cont) =>
        text("== ")  <> text(cont)  <> text(" ==")  <>
        line
      case MDSubsectionHeader(cont) =>
        text("=== ") <> text(cont)  <> text(" ===") <>
        line

      case MDLink(linkText, url) =>
        text("(") <> text(linkText) <> text(")") <> text("[") <> text(url) <> text("]")

      case _ => sys.error("MiniMD : Unknown Markdown type")

    }

  }

  /* ======================================================================
   *  Exercise 5
   * ====================================================================== */

   object LatexFormatter extends Formatter[MiniMDExpr] {

     def format(e: MiniMDExpr) = e match {
       case MDDoc(x::xs) =>
         formatList(x::xs)
       case MDPar(x::xs) =>
         formatList(x::xs) <>
         line              <>
         line
       case MDVerbatim(cont) =>
         unnest(
           text("\\begin") <> braces(text("verbatim")) <>
           line                                        <>
           text(cont)                                  <>
           text("\\end")   <> braces(text("verbatim")) <>
           line)

       case MDFreeText(cont) =>
         text(cont)
       case MDBold(cont) =>
         text("\\textbf")    <> braces(text(cont))
       case MDItalic(cont) =>
         text("\\textit")    <> braces(text(cont))
       case MDUnderlined(cont) =>
         text("\\underline") <> braces(text(cont))

       case MDListItem(x::xs) =>
         nest( 2,
               line               <>
               text("\\item ")    <>
               formatList(x::xs))
       case MDBulletedList(x::xs) =>
         text("\\begin") <> braces(text("itemize"))    <>
         formatList(x::xs)                             <>
         line                                          <>
         text("\\end")   <> braces(text("itemize"))    <>
         line <> line

       case MDNumberedList(x::xs) =>
         text("\\begin") <> braces(text("enumerate"))  <>
         formatList(x::xs)                             <>
         line                                          <>
         text("\\end")   <> braces(text("enumerate"))  <>
         line <> line

       case MDSectionHeader(cont) =>
         text("\\section")    <> braces(text(cont))    <>
         line
       case MDSubsectionHeader(cont) =>
         text("\\subsection") <> braces(text(cont))    <>
         line

       case MDLink(linkText, url) =>
         text("\\href")  <> braces(text(url)) <> braces(text(linkText))

       case _ => sys.error("Latex : Unknown Markdown type")

     }

   }

  // ======================================================================
  //  Exercise 6
  // ======================================================================


  object HTMLFormatter extends Formatter[MiniMDExpr] {

    def format(e: MiniMDExpr) = e match {
      case MDDoc(x::xs) =>
        formatList(x::xs)
      case MDPar(x::xs) =>
        anglebrackets(text("p")) <> formatList(x::xs) <> anglebrackets(text("/p")) <>
        line <> line
      case MDVerbatim(cont) =>
        unnest(
          anglebrackets(text("pre")) <> text(cont) <> anglebrackets(text("/pre"))  <>
          line)

      case MDFreeText(cont) =>
        text(cont)
      case MDBold(cont) =>
        anglebrackets(text("b")) <> text(cont) <> anglebrackets(text("/b"))
      case MDItalic(cont) =>
        anglebrackets(text("i")) <> text(cont) <> anglebrackets(text("/i"))
      case MDUnderlined(cont) =>
        anglebrackets(text("u")) <> text(cont) <> anglebrackets(text("/u"))

      case MDListItem(x::xs) =>
        nest(2,
             line <> anglebrackets(text("li")) <> formatList(x::xs) <>
                     anglebrackets(text("/li")))
      case MDBulletedList(x::xs) =>
        anglebrackets(text("ul"))  <> formatList(x::xs) <> line     <>
        anglebrackets(text("/ul")) <> line
      case MDNumberedList(x::xs) =>
        anglebrackets(text("ol"))  <> formatList(x::xs) <> line     <>
        anglebrackets(text("/ol")) <> line

      case MDSectionHeader(cont) =>
        anglebrackets(text("h1"))  <> text(cont) <>
        anglebrackets(text("/h1")) <> line
      case MDSubsectionHeader(cont) =>
        anglebrackets(text("h2"))  <> text(cont) <>
        anglebrackets(text("/h2")) <> line

      case MDLink(linkText, url) =>
        anglebrackets(text("a href=") <> quote(text(url)))          <>
        text(linkText)                <> anglebrackets(text("/a"))

      case _ => sys.error("HTML : Unknown Markdown type")

    }

  }

  // ======================================================================
  // Part 2: Random test case generation
  // ======================================================================

  object Rng {


    // A Gen[T] has a method called get that generates a random T.
    trait Gen[+A] {
      val rng = scala.util.Random

      def get(): A // abstract

      // Gen[T] also supports the map and flatMap methods, so for-comprehensions
      // can be used with them.
      def map[B](f: A => B):Gen[B] =
      {
        val self = this
        new Gen[B] { def get() = f(self.get()) }
      }

      // **********************************************************************
      // Exercise 8
      // **********************************************************************

      def flatMap[B](f: A => Gen[B]) : Gen[B]= {
        val self = this
        new Gen[B] {
          def get() = f(self.get()).get()
        }
      }
    }

    // **********************************************************************
    // Exercise 7
    // **********************************************************************

    def const[T](c: T): Gen[T] =
      new Gen[T] {
        def get() = c
      }

    def flip: Gen[Boolean] =
      new Gen[Boolean] {
        def get() = rng.nextBoolean()
      }

    def range(min: Integer, max: Integer): Gen[Integer] =
      new Gen[Integer] {
        def get() = min + rng.nextInt(max - min + 1)
      }

    def fromList[T](items: List[T]): Gen[T] =
      new Gen[T] {
        def get() = items(rng.nextInt(items.length))
      }

    // **********************************************************************
    // Exercise 9
    // **********************************************************************

    def genFromList[A](gs: List[Gen[A]]): Gen[A] =
      new Gen[A] {
        def get() = gs(range(0, gs.length - 1).get).get
      }

    // **********************************************************************
    // Exercise 10
    // **********************************************************************

    def genList[T](n: Integer, g: Gen[T]): Gen[List[T]] =
      new Gen[List[T]] {
        def get() = List.fill(n)(g.get)
      }

    // **********************************************************************
    // Exercise 11
    // **********************************************************************

    def genSectionText: Gen[String] =
      fromList(List("Chapter 1", "Introduction", "Conclusion"))

    def genSubsectionText: Gen[String] =
      fromList(List("Section 1.1", "Table of Contents", "References"))

    def genListitemText: Gen[String] =
      fromList(List("Apples", "Oranges", "Spaceship"))

    def genLink: Gen[(String, String)] =
      fromList(List(("Google", "http://www.google.com"), ("Facebook", "http://www.facebook.com")))

    def genFreeText: Gen[String] =
      fromList(List("It was a dark and stormy night", "It was the best of times"))

    def genVerbatimText: Gen[String] =
      fromList(List("== This isn’t valid MiniMD ===", "*Neither_ _is’ ’this*"))

    // **********************************************************************
    // Exercise 12
    // **********************************************************************

    def genMiniMDExpr(n: Integer): Gen[MiniMDExpr] =
      new Gen[MiniMDExpr]{
        //we can also implement some of them by for-comprehensions
        //But I used another design pattern here
        //And I am also not sure where can I use flip and const
        def get() = {
          val genMDListItemNode = new Gen[MiniMDExpr] {
            def get() = MDFreeText(genListitemText.get)
          }

          val genMDListItem = new Gen[MDListItem]{
            def get() = MDListItem(genList(1, genMDListItemNode).get)
             //MDListItem((for(i <- range(1,1); j <- genList(i, genMDListItemNode)) yield j).get)
          }

          val genMDBulletedList = new Gen[MDBulletedList]{
            def get() = MDBulletedList(genList(range(2,4).get, genMDListItem).get)
            //here we can implement for-comprehensions
          }
          val genMDNumberedList = new Gen[MDNumberedList]{
            def get() = MDNumberedList(genList(range(2,4).get, genMDListItem).get)
            //here we can implement for-comprehensions
          }

          val genMDSectionHeader = new Gen[MDSectionHeader]{
            def get() = MDSectionHeader(genSectionText.get)
          }
          val genSubsectionHeader = new Gen[MDSubsectionHeader]{
            def get() = MDSubsectionHeader(genSubsectionText.get)
          }
          val genMDVerbatim = new Gen[MDVerbatim]{
            def get() = MDVerbatim(genVerbatimText.get)
          }

          val genMDLink = new Gen[MDLink]{
            def get() = {
              val link = genLink.get
              MDLink(link._1, link._2)
            }
          }

          val genMDFreeText = new Gen[MDFreeText]{
            def get() = MDFreeText(genFreeText.get)
          }

          val genMDBold = new Gen[MDBold]{
            def get() = MDBold(genFreeText.get)
          }
          val genMDItalic = new Gen[MDItalic]{
            def get() = MDItalic(genFreeText.get)
          }
          val genMDUnderlined = new Gen[MDUnderlined]{
            def get() = MDUnderlined(genFreeText.get)
          }

          val genMDPar = new Gen[MDPar] {
            def get() = MDPar(genList(range(3, 5).get,
                              genFromList(List(genMDFreeText   , genMDBold, genMDItalic,
                                               genMDUnderlined , genMDLink
                             ))).get)
            //here we can implement for-comprehensions
          }

          MDDoc(genList(n, genFromList(List(genMDPar           , genMDBulletedList ,
                                            genMDNumberedList  , genMDSectionHeader,
                                            genSubsectionHeader, genMDVerbatim
               ))).get)
        }
      }
  }


  /*======================================================================
   The rest of this file is support code, which you should not (and do not
   need to) change.
   ====================================================================== */
  /* ===== MiniMD Parser ===== */

  object MiniMDParser extends RegexParsers {
    val eol = sys.props("line.separator")

    // Here be dragons.

    type P[+A] = Parser[A]
    private val eoi = """\z""".r // end of input
    private val separator = eoi | eol

    override val skipWhitespace = false

    // Paragraph: Either a long line of free text with the whitespace
    // stripped out, or a list with whitespace kept in
    type Line = String
    type Paragraph = String



    // Parses an input file
    def parse(input: String): MiniMDExpr = {
      val source = scala.io.Source.fromFile(input)
      val lines = try source.mkString finally source.close()
      val paragraphs = tokeniseParagraphs(lines)

      println("Paragraphs:")
      println(paragraphs + "\n\n")
      val parsedParagraphs = paragraphs.flatMap((par: Paragraph) => parseParagraph(par))

      normalise(MDDoc(parsedParagraphs))
    }

    // Top-level parse function: takes a string, returns a MiniMDExpr.
    // Throws an error upon failure.
    def parseParagraph(input: String): List[MiniMDExpr] = {
      if (input.trim.length == 0) { Nil }
      else {
        parseAll(paragraph, input) match {
          case Success(ast, _) => List(ast)
          case (e: NoSuccess) => {
            sys.error(e.msg + ", " + e.next.pos + ", " + e.next.source)
            Nil
          }
        }
      }
    }


    // Given an input string, generates a list of paragraphs
    def tokeniseParagraphs(input: String): List[Paragraph] = {

      def isEmptyLine(s: String) = s.trim.length == 0

      def isBulletListItem(s: String) = s.startsWith("* ")
      def isNumberListItem(s: String) = """^\d+\. """.r.findFirstIn(s).isDefined
      def isListItem(s: String) = isBulletListItem(s) || isNumberListItem(s)

      def isStartVerbatim(s: String) = s.trim == "{{{"
      def isEndVerbatim(s: String) = s.trim == "}}}"
      def isSection(s: String) = s.trim.startsWith("==")


      def gatherList(isBulleted: Boolean, par: Paragraph,
        remainder: List[Line]): (Paragraph, List[Line]) = remainder match {
        case Nil => (par, remainder)
        case x::xs =>
          if (isBulleted && isBulletListItem(x)) {
            gatherList(isBulleted, par + x, xs)
          } else if (!isBulleted && isNumberListItem(x)) {
            gatherList(isBulleted, par + x, xs)
          } else if (isEmptyLine(x)) {
            (par, xs)
          } else {
            (par, remainder)
          }
      }

      def gatherParagraph(par: Paragraph, remainder: List[Line]):
          (Paragraph, List[Line]) =
        remainder match {
          case Nil => (par, remainder)
          case x::xs =>
            if (isEmptyLine(x)) {
              (par, xs)
            } else if (isListItem(x) || isStartVerbatim(x)) {
              (par, remainder)
            } else {
              gatherParagraph(par + x.stripLineEnd + " ", xs)
            }
        }

      def gatherVerbatim(par: Paragraph, remainder: List[Line]):
          (Paragraph, List[Line]) =
        remainder match {
          case Nil => (par, remainder)
          case x::xs =>
            if (isEndVerbatim(x)) {
              (par + x.trim, xs)
            } else {
              gatherVerbatim(par + x, xs)
            }
        }

      def eatEmptyLines(remainder: List[Line]):
          (List[Line]) =
        remainder match {
          case Nil => Nil
          case x::xs =>
            if (isEmptyLine(x)) {
              eatEmptyLines(xs)
            } else {
              remainder
            }
        }

      def doTokeniseParagraphs(remainder: List[Line]): List[Paragraph] =
        remainder match {
          case Nil => Nil
          case x::xs =>
            if (isEmptyLine(x)) {
              doTokeniseParagraphs(xs)
            } else if (isSection(x)) {
              x.stripLineEnd::(doTokeniseParagraphs(xs))
            } else if (isStartVerbatim(x)) {
              val (par, newRemainder) = gatherVerbatim("", remainder)
              par::(doTokeniseParagraphs(newRemainder))
            } else if (isBulletListItem(x)) {
              val (par, newRemainder) = gatherList(true, "", remainder)
              par::(doTokeniseParagraphs(newRemainder))
            } else if (isNumberListItem(x)) {
              val (par, newRemainder) = gatherList(false, "", remainder)
              par::(doTokeniseParagraphs(newRemainder))
            } else {
              val (par, newRemainder) = gatherParagraph("", remainder)
              par::(doTokeniseParagraphs(newRemainder))
            }
        }

      val linesList = input.linesWithSeparators.toList
      doTokeniseParagraphs(linesList)
    }

    def delimitedSequence(delimiter: Char, breakOnNL: Boolean): P[String] = {
      (rep(delimitedChar(delimiter, breakOnNL)) <~ aChar) ^^ {
        case seq => seq.mkString
      }
    }

    def num: P[Int] = "[0-9]+".r ^^ { case n => n.toInt }

    def delimitedChar(delimiter: Char, breakOnNL: Boolean): P[Char] =
      acceptIf {ch => (ch != delimiter) || (breakOnNL && ch == eol)} {_ => "Delimiter char reached"}

    def aChar: P[Char] = Parser { in =>
      if (in.atEnd) {
        Failure("End of input", in)
      } else {
        Success(in.first, in.rest)
      }
    }

    def isDelimiterChar(c: Char): Boolean =
      c match {
        case '*' => true
        case '_' => true
        case '`' => true
        case '=' => true
        case '\r' => true
        case '\n' => true
        case '(' => true
        case '{' => true
        case _ => false
      }

    def bulletedListItem = {
      ("* " ~> listExpr) <~ eol ^^ { case e => MDListItem(e) }
    }

    def bulletedList: P[MiniMDExpr] = {
      rep1(bulletedListItem) ^^ { case seq => MDBulletedList(seq) }
    }

    def numberedListItem: P[MDListItem] =
      ((num <~ ". ") ~ listExpr) <~ eol ^^ {
        case (num ~ e) => MDListItem(e)
      }

    def numberedList: P[MiniMDExpr] = {
      rep1(numberedListItem) ^^ { case seq => MDNumberedList(seq) }
    }

    def parseDelimiterRun(breakOnNL: Boolean): P[MiniMDExpr] = {
      ("*" ~> delimitedSequence('*', breakOnNL) ^^ { case str => MDBold(str) }) |
      ("`" ~> delimitedSequence('`', breakOnNL) ^^ { case str => MDItalic(str) }) |
      ("_" ~> delimitedSequence('_', breakOnNL) ^^ { case str => MDUnderlined(str) })
    }

    def freeChar: P[Char] =
      acceptIf {ch => !isDelimiterChar(ch)} {_ => "Delimiter char reached"}

    // Parse until we hit a delimiter character.
    def freeText: P[MiniMDExpr] =
      aChar ~ rep(freeChar) ^^ { case ch ~ xs => MDFreeText((ch::xs).mkString) }

    def subsectionHeader: P[MiniMDExpr] =
      ("===" ~> "[^=]+".r <~ "===[ ]*".r) ^^ { case headertxt => MDSubsectionHeader(headertxt.trim) }

    def sectionHeader: P[MiniMDExpr] =
      ("==" ~> "[^=]+".r <~ "==[ ]*".r) ^^ { case headertxt => MDSectionHeader(headertxt.trim) }

    def link: P[MiniMDExpr] =
      ("(" ~> ("[^)]*".r) <~ ")") ~ ("[" ~> ("[^\\]]*".r) <~ "]") ^^ {
        case desc~url => MDLink(desc, url)
      }

    def verbatim: P[MiniMDExpr] =
      ("{{{" ~> eol ~> """(?s).*?(?=}}})""".r.unanchored <~ "}}}") ^^ { case vrb => MDVerbatim(vrb) }

    def listExpr: P[List[MiniMDExpr]] = {
      rep1((guard(not(eol))) ~> (parseDelimiterRun(true) | freeText))
    }

    def expr: P[MiniMDExpr] = {
      parseDelimiterRun(false) | link | freeText
    }

    def plainPar: P[MiniMDExpr] = {
      rep1(expr) ^^ { xs => MDPar(xs) }
    }

    def paragraph: P[MiniMDExpr] =
       subsectionHeader | sectionHeader | bulletedList | numberedList | verbatim | plainPar



    /* Normalisation pass.
     * We'll get a stream of FreeText / lists / section headers from
     * the parser.
     * We want to ensure that if we have two consecutive FreeTexts,
     * that they're combined into one.
     */
    def normaliseInner(es: List[MiniMDExpr]): List[MiniMDExpr] = es match {
      case Nil => Nil
      case MDFreeText(s1)::MDFreeText(s2)::xs => normaliseInner(MDFreeText(s1 ++ s2)::xs)
      case e::xs => normalise(e)::normaliseInner(xs)
    }

    def normalise(e: MiniMDExpr): MiniMDExpr = e match {
      case MDDoc(xs) => MDDoc(normaliseInner(xs))
      case MDPar(xs) => MDPar(normaliseInner(xs))
      case MDBulletedList(xs) =>
        MDBulletedList(xs.map(x => normalise(x).asInstanceOf[MDListItem]))
      case MDNumberedList(xs) =>
        MDNumberedList(xs.map(x => normalise(x).asInstanceOf[MDListItem]))
      case MDListItem(xs) => MDListItem(normaliseInner(xs))
      case e => e
    }

  }


  object Main {
    def usage() {
      println("MiniMD formatter version 1.8 (November 19, 2015)")
      println("Usage: scala CW2.scala <infile> <mode> <outfile>")
      println("<infile> is the input file name, or RANDOM to generate a random test")
      println("<mode> is one of \"html\", \"md\" or \"latex\", and defaults to \"md\"")
      println("<outfile> is optional and defaults to \"output\"")
    }

    def getInput(infile: String): MiniMDExpr = {
      if (infile == "RANDOM") {
        println("Generating random test file...")
        Rng.genMiniMDExpr(100).get()
      }
      else {
        println("Reading " + infile)
        MiniMDParser.parse(infile)
      }
    }

    def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
      val p = new java.io.PrintWriter(f)
      try { op(p) } finally { p.close() }
    }

    def writeHtml(outfile:String, html: String) {
      println("Writing " + outfile)
      printToFile(new java.io.File(outfile)) { out =>
        out.write("<html>\n<body>\n<!-- Beginning of MiniMD code -->\n")
        out.write(html)
        out.write("<!-- End of MiniMD code -->\n</body>\n")
      }
    }

    def writeMd(outfile: String, md: String) {
      println("Writing " + outfile)
      printToFile(new java.io.File(outfile)) { out =>
        out.write(md)
      }
    }

    def writeLatex(outfile: String, latex: String) {
      println("Writing " + outfile)
      printToFile(new java.io.File(outfile)) { out =>
        out.write("\\documentclass{article}\n" +
          "\\usepackage[colorlinks=true]{hyperref}\n" +
          "\\begin{document}\n" +
          "%%% Beginning of MiniMD content\n")
        out.write(latex)
        out.write("%%% End of MiniMD content\n" +
          "\\end{document}\n")
      }
    }

  }
  def main(args: Array[String]): Unit = {
    if (args.length >= 1 ) {
      val infile = args(0)
      val mode =  if (args.length >= 2) { args(1) } else { "md" }
      // Check that outfile is one of html, md or latex
      if (mode == "html" || mode == "md" || mode == "latex") {

        val parsed = Main.getInput(infile)

        mode match {
          case "html" => {
            println("Generating HTML...")
            val genHtml = print(HTMLFormatter.format(parsed))
            println(genHtml)
            if (args.length >= 3) {
              Main.writeHtml(args(2), genHtml)
            }
          }
          case "md" => {
            println("Generating MiniMD...")
            val genMd = print(MarkdownFormatter.format(parsed))
            println(genMd)
            if (args.length >= 3) {
              Main.writeMd(args(2), genMd)
            }
          }
          case "latex" => {
            println("Generating LaTeX...")
            val genLatex = print(LatexFormatter.format(parsed))
            println(genLatex)
            if (args.length >= 3) {
              Main.writeLatex(args(2),genLatex)
            }
          }
        }
      } else {
        Main.usage()
      }
    } else {
      Main.usage()
    }
  }
}
