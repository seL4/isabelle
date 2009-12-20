/*  Title:      Pure/Isar/outer_lex.scala
    Author:     Makarius

Outer lexical syntax for Isabelle/Isar.
*/

package isabelle


object Outer_Lex
{
  sealed abstract class Token
  {
    def source: String
    def content: String = source

    def is_delimited: Boolean = false
    def is_name: Boolean = false
    def is_xname: Boolean = false
    def is_text: Boolean = false
    def is_space: Boolean = false
    def is_comment: Boolean = false
    def is_proper: Boolean = !(is_space || is_comment)
  }

  case class Command(val source: String) extends Token

  case class Keyword(val source: String) extends Token

  case class Ident(val source: String) extends Token
  {
    override def is_name = true
    override def is_xname = true
    override def is_text = true
  }

  case class Long_Ident(val source: String) extends Token
  {
    override def is_xname = true
    override def is_text = true
  }

  case class Sym_Ident(val source: String) extends Token
  {
    override def is_name = true
    override def is_xname = true
    override def is_text = true
  }

  case class Var(val source: String) extends Token

  case class Type_Ident(val source: String) extends Token

  case class Type_Var(val source: String) extends Token

  case class Nat(val source: String) extends Token
  {
    override def is_name = true
    override def is_xname = true
    override def is_text = true
  }

  case class String_Token(val source: String) extends Token
  {
    override def content = Scan.Lexicon.empty.quoted_content("\"", source)
    override def is_delimited = true
    override def is_name = true
    override def is_xname = true
    override def is_text = true
  }

  case class Alt_String_Token(val source: String) extends Token
  {
    override def content = Scan.Lexicon.empty.quoted_content("`", source)
    override def is_delimited = true
  }

  case class Verbatim(val source: String) extends Token
  {
    override def content = Scan.Lexicon.empty.verbatim_content(source)
    override def is_delimited = true
    override def is_text = true
  }

  case class Space(val source: String) extends Token
  {
    override def is_space = true
  }

  case class Comment(val source: String) extends Token
  {
    override def content = Scan.Lexicon.empty.comment_content(source)
    override def is_delimited = true
    override def is_comment = true
  }

  case class Bad_Input(val source: String) extends Token
  case class Unparsed(val source: String) extends Token
}

