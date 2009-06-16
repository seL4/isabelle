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

    private def make(tree: Tree, max: Int): Lexicon =
      new Lexicon {
        override val main_tree = tree
        override val max_entry = max
      }

    val empty: Lexicon = new Lexicon
    def apply(strs: String*): Lexicon = (empty /: strs) ((lex, str) => lex + str)
  }

  class Lexicon extends scala.collection.immutable.Set[String] with RegexParsers
  {
    /* representation */

    import Lexicon.Tree
    val main_tree: Tree = Lexicon.empty_tree
    val max_entry = -1


    /* Set methods */

    override def stringPrefix = "Lexicon"

    override def isEmpty: Boolean = (max_entry < 0)

    private def destruct: List[String] =
    {
      def dest(tree: Tree, result: List[String]): List[String] =
        (result /: tree.branches.toList) ((res, entry) =>
          entry match { case (_, (s, tr)) =>
            if (s.isEmpty) dest(tr, res) else dest(tr, s :: res) })
      dest(main_tree, Nil).sort(_ <= _)
    }

    def size: Int = destruct.length
    def elements: Iterator[String] = destruct.elements

    def contains(str: String): Boolean =
    {
      val len = str.length
      def check(tree: Tree, i: Int): Boolean =
        i < len && {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => !s.isEmpty && i + 1 == len || check(tr, i + 1)
            case None => false
          }
        }
      check(main_tree, 0)
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
      else Lexicon.make(extend(main_tree, 0), max_entry max str.length)
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

        def scan(tree: Tree, i: Int, res: String): String =
        {
          if (i < len) {
            tree.branches.get(source.charAt(offset + i)) match {
              case Some((s, tr)) => scan(tr, i + 1, if (s.isEmpty) res else s)
              case None => res
            }
          } else res
        }
        val res = scan(main_tree, 0, "")
        if (res.isEmpty) Failure("keyword expected", in)
        else Success(res, in.drop(res.length))
      }
    }.named("keyword")

  }
}

