/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of keywords.
*/

package isabelle

import scala.util.parsing.combinator.RegexParsers


object Scan
{

  /** Lexicon -- position tree **/

  object Lexicon
  {
    private case class Tree(val branches: Map[Char, (String, Tree)])
    private val empty_tree = Tree(Map())

    private def make(tree: Tree): Lexicon =
      new Lexicon { override val main_tree = tree }

    val empty: Lexicon = new Lexicon
    def apply(strs: String*): Lexicon = (empty /: strs) ((lex, str) => lex + str)
  }

  class Lexicon extends scala.collection.immutable.Set[String] with RegexParsers
  {
    /* representation */

    import Lexicon.Tree
    val main_tree: Tree = Lexicon.empty_tree


    /* auxiliary operations */

    private def content(tree: Tree, result: List[String]): List[String] =
      (result /: tree.branches.toList) ((res, entry) =>
        entry match { case (_, (s, tr)) =>
          if (s.isEmpty) content(tr, res) else content(tr, s :: res) })

    private def lookup(str: CharSequence): Option[(Boolean, Tree)] =
    {
      val len = str.length
      def look(tree: Tree, tip: Boolean, i: Int): Option[(Boolean, Tree)] =
      {
        if (i < len) {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => look(tr, !s.isEmpty, i + 1)
            case None => None
          }
        } else Some(tip, tree)
      }
      look(main_tree, false, 0)
    }

    def completions(str: CharSequence): List[String] =
    {
      (lookup(str) match {
        case Some((true, tree)) => content(tree, List(str.toString))
        case Some((false, tree)) => content(tree, Nil)
        case None => Nil
      }).sort((s1, s2) => s1.length < s2.length || s1.length == s2.length && s1 <= s2)
    }


    /* Set methods */

    override def stringPrefix = "Lexicon"

    override def isEmpty: Boolean = { main_tree.branches.isEmpty }

    def size: Int = content(main_tree, Nil).length
    def elements: Iterator[String] = content(main_tree, Nil).sort(_ <= _).elements

    def contains(str: String): Boolean =
      lookup(str) match {
        case Some((tip, _)) => tip
        case _ => false
      }

    def +(str: String): Lexicon =
    {
      val len = str.length
      def extend(tree: Tree, i: Int): Tree =
      {
        if (i < len) {
          val c = str.charAt(i)
          val end = (i + 1 == len)
          tree.branches.get(c) match {
            case Some((s, tr)) =>
              Tree(tree.branches + (c -> (if (end) str else s, extend(tr, i + 1))))
            case None =>
              Tree(tree.branches + (c -> (if (end) str else "", extend(Lexicon.empty_tree, i + 1))))
          }
        } else tree
      }
      if (contains(str)) this
      else Lexicon.make(extend(main_tree, 0))
    }

    def empty[A]: Set[A] = error("Undefined")
    def -(str: String): Lexicon = error("Undefined")


    /* RegexParsers methods */

    override val whiteSpace = "".r

    def keyword: Parser[String] = new Parser[String] {
      def apply(in: Input) =
      {
        val source = in.source
        val offset = in.offset
        val len = source.length - offset

        def scan(tree: Tree, text: String, i: Int): String =
        {
          if (i < len) {
            tree.branches.get(source.charAt(offset + i)) match {
              case Some((s, tr)) => scan(tr, if (s.isEmpty) text else s, i + 1)
              case None => text
            }
          } else text
        }
        val text = scan(main_tree, "", 0)
        if (text.isEmpty) Failure("keyword expected", in)
        else Success(text, in.drop(text.length))
      }
    }.named("keyword")

  }


  /** reverse CharSequence **/

  class Reverse(text: CharSequence, start: Int, end: Int) extends CharSequence
  {
    require(0 <= start && start <= end && end <= text.length)

    def this(text: CharSequence) = this(text, 0, text.length)

    def length: Int = end - start
    def charAt(i: Int): Char = text.charAt(end - i - 1)

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Reverse(text, end - j, end - i)
      else throw new IndexOutOfBoundsException

    override def toString: String =
    {
      val buf = new StringBuffer(length)
      for (i <- 0 until length)
        buf.append(charAt(i))
      buf.toString
    }
  }

}

