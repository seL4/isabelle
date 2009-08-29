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

    val empty: Lexicon = new Lexicon
    def apply(elems: String*): Lexicon = empty ++ elems
  }

  class Lexicon extends scala.collection.Set[String] with RegexParsers
  {
    /* representation */

    import Lexicon.Tree
    protected val main_tree: Tree = Lexicon.empty_tree


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
      lookup(str) match {
        case Some((true, tree)) => content(tree, List(str.toString))
        case Some((false, tree)) => content(tree, Nil)
        case None => Nil
      }


    /* Set methods */

    override def stringPrefix = "Lexicon"

    override def isEmpty: Boolean = { main_tree.branches.isEmpty }

    def size: Int = content(main_tree, Nil).length
    def elements: Iterator[String] = content(main_tree, Nil).sort(_ <= _).elements

    def contains(elem: String): Boolean =
      lookup(elem) match {
        case Some((tip, _)) => tip
        case _ => false
      }

    def + (elem: String): Lexicon =
      if (contains(elem)) this
      else {
        val len = elem.length
        def extend(tree: Tree, i: Int): Tree =
          if (i < len) {
            val c = elem.charAt(i)
            val end = (i + 1 == len)
            tree.branches.get(c) match {
              case Some((s, tr)) =>
                Tree(tree.branches +
                  (c -> (if (end) elem else s, extend(tr, i + 1))))
              case None =>
                Tree(tree.branches +
                  (c -> (if (end) elem else "", extend(Lexicon.empty_tree, i + 1))))
            }
          } else tree
        val old = this
        new Lexicon { override val main_tree = extend(old.main_tree, 0) }
      }

    def + (elem1: String, elem2: String, elems: String*): Lexicon =
      this + elem1 + elem2 ++ elems
    def ++ (elems: Iterable[String]): Lexicon = (this /: elems) ((s, elem) => s + elem)
    def ++ (elems: Iterator[String]): Lexicon = (this /: elems) ((s, elem) => s + elem)


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
}

