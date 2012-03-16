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
  val THY_BEGIN = "thy_begin"
  val THY_END = "thy_end"
  val THY_HEADING = "thy_heading"
  val THY_DECL = "thy_decl"
  val THY_SCRIPT = "thy_script"
  val THY_GOAL = "thy_goal"
  val THY_SCHEMATIC_GOAL = "thy_schematic_goal"
  val QED = "qed"
  val QED_BLOCK = "qed_block"
  val QED_GLOBAL = "qed_global"
  val PRF_HEADING = "prf_heading"
  val PRF_GOAL = "prf_goal"
  val PRF_BLOCK = "prf_block"
  val PRF_OPEN = "prf_open"
  val PRF_CLOSE = "prf_close"
  val PRF_CHAIN = "prf_chain"
  val PRF_DECL = "prf_decl"
  val PRF_ASM = "prf_asm"
  val PRF_ASM_GOAL = "prf_asm_goal"
  val PRF_SCRIPT = "prf_script"


  /* categories */

  val minor = Set(MINOR)
  val control = Set(CONTROL)
  val diag = Set(DIAG)
  val theory =
    Set(THY_BEGIN, THY_END, THY_HEADING, THY_DECL, THY_SCRIPT, THY_GOAL, THY_SCHEMATIC_GOAL)
  val theory1 = Set(THY_BEGIN, THY_END)
  val theory2 = Set(THY_DECL, THY_GOAL)
  val proof =
    Set(QED, QED_BLOCK, QED_GLOBAL, PRF_HEADING, PRF_GOAL, PRF_BLOCK,
      PRF_OPEN, PRF_CHAIN, PRF_DECL, PRF_ASM, PRF_ASM_GOAL, PRF_SCRIPT)
  val proof1 =
    Set(QED, QED_BLOCK, QED_GLOBAL, PRF_GOAL, PRF_BLOCK, PRF_OPEN, PRF_CLOSE, PRF_CHAIN, PRF_DECL)
  val proof2 = Set(PRF_ASM, PRF_ASM_GOAL)
  val improper = Set(THY_SCRIPT, PRF_SCRIPT)
}

