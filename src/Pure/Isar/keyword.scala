/*  Title:      Pure/Isar/keyword.scala
    Author:     Makarius

Isar command keyword classification and keyword tables.
*/

package isabelle


object Keyword
{
  /* kinds */

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
  val THY_SCHEMATIC_GOAL = "theory-schematic-goal"
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


  /* categories */

  val minor = Set(MINOR)
  val control = Set(CONTROL)
  val diag = Set(DIAG)
  val theory =
    Set(THY_BEGIN, THY_SWITCH, THY_END, THY_HEADING, THY_DECL, THY_SCRIPT,
      THY_GOAL, THY_SCHEMATIC_GOAL)
  val theory1 = Set(THY_BEGIN, THY_SWITCH, THY_END)
  val theory2 = Set(THY_DECL, THY_GOAL)
  val proof =
    Set(QED, QED_BLOCK, QED_GLOBAL, PRF_HEADING, PRF_GOAL, PRF_BLOCK,
      PRF_OPEN, PRF_CHAIN, PRF_DECL, PRF_ASM, PRF_ASM_GOAL, PRF_SCRIPT)
  val proof1 =
    Set(QED, QED_BLOCK, QED_GLOBAL, PRF_GOAL, PRF_BLOCK, PRF_OPEN, PRF_CLOSE, PRF_CHAIN, PRF_DECL)
  val proof2 = Set(PRF_ASM, PRF_ASM_GOAL)
  val improper = Set(THY_SCRIPT, PRF_SCRIPT)


  /* protocol messages */

  object Keyword_Decl {
    def unapply(msg: XML.Tree): Option[String] =
      msg match {
        case XML.Elem(Markup(Isabelle_Markup.KEYWORD_DECL, List((Markup.NAME, name))), _) =>
          Some(name)
        case _ => None
      }
  }

  object Command_Decl {
    def unapply(msg: XML.Tree): Option[(String, String)] =
      msg match {
        case XML.Elem(Markup(Isabelle_Markup.COMMAND_DECL,
            List((Markup.NAME, name), (Markup.KIND, kind))), _) => Some((name, kind))
        case _ => None
      }
  }
}

