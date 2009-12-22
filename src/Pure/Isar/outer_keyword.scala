/*  Title:      Pure/Isar/outer_keyword.scala
    Author:     Makarius

Isar command keyword classification and keyword tables.
*/

package isabelle


import scala.util.parsing.input.{Reader, CharSequenceReader}


object Outer_Keyword
{
  val MINOR = "minor"
  val CONTROL = "control"
  val DIAG = "diag"
  val THY_BEGIN = "theory-begin"
  val THY_SWITCH = "theory-switch"
  val THY_END = "theory-end"
  val THY_HEADING = "theory-heading"
  val THY_DECL = "theory-decl"
  val THY_SCRIPT = "theory-script"
  val THY_GOAL = "theory-goal"
  val QED = "qed"
  val QED_BLOCK = "qed-block"
  val QED_GLOBAL = "qed-global"
  val PRF_HEADING = "proof-heading"
  val PRF_GOAL = "proof-goal"
  val PRF_BLOCK = "proof-block"
  val PRF_OPEN = "proof-open"
  val PRF_CLOSE = "proof-close"
  val PRF_CHAIN = "proof-chain"
  val PRF_DECL = "proof-decl"
  val PRF_ASM = "proof-asm"
  val PRF_ASM_GOAL = "proof-asm-goal"
  val PRF_SCRIPT = "proof-script"

  val minor = Set(MINOR)
  val control = Set(CONTROL)
  val diag = Set(DIAG)
  val heading = Set(THY_HEADING, PRF_HEADING)
  val theory1 = Set(THY_BEGIN, THY_SWITCH, THY_END)
  val theory2 = Set(THY_DECL, THY_GOAL)
  val proof1 =
    Set(QED, QED_BLOCK, QED_GLOBAL, PRF_GOAL, PRF_BLOCK, PRF_OPEN, PRF_CLOSE, PRF_CHAIN, PRF_DECL)
  val proof2 = Set(PRF_ASM, PRF_ASM_GOAL)
  val improper = Set(THY_SCRIPT, PRF_SCRIPT)
}


class Outer_Keyword(symbols: Symbol.Interpretation)
{
  protected val lexicon: Scan.Lexicon = Scan.Lexicon.empty
  protected val keywords: Map[String, String] = Map((";" -> Outer_Keyword.DIAG))

  def keyword(name: String, kind: String): Outer_Keyword =
  {
    val new_lexicon = lexicon + name
    val new_keywords = keywords + (name -> kind)
    new Outer_Keyword(symbols) {
      override val lexicon = new_lexicon
      override val keywords = new_keywords
    }
  }

  def keyword(name: String): Outer_Keyword = keyword(name, Outer_Keyword.MINOR)

  def is_command(name: String): Boolean =
    keywords.get(name) match {
      case Some(kind) => kind != Outer_Keyword.MINOR
      case None => false
    }


  /* tokenize */

  def tokenize(input: Reader[Char]): List[Outer_Lex.Token] =
  {
    import lexicon._

    parseAll(rep(token(symbols, is_command)), input) match {
      case Success(tokens, _) => tokens
      case _ => error("Failed to tokenize input:\n" + input.source.toString)
    }
  }

  def tokenize(input: CharSequence): List[Outer_Lex.Token] =
    tokenize(new CharSequenceReader(input))
}
