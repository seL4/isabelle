/*  Title:      Pure/Isar/keyword.scala
    Author:     Makarius

Isar keyword classification.
*/

package isabelle


object Keyword
{
  /** keyword classification **/

  /* kinds */

  val MINOR = "minor"
  val DIAG = "diag"
  val HEADING = "heading"
  val THY_BEGIN = "thy_begin"
  val THY_END = "thy_end"
  val THY_DECL = "thy_decl"
  val THY_DECL_BLOCK = "thy_decl_block"
  val THY_LOAD = "thy_load"
  val THY_GOAL = "thy_goal"
  val QED = "qed"
  val QED_SCRIPT = "qed_script"
  val QED_BLOCK = "qed_block"
  val QED_GLOBAL = "qed_global"
  val PRF_GOAL = "prf_goal"
  val PRF_BLOCK = "prf_block"
  val PRF_OPEN = "prf_open"
  val PRF_CLOSE = "prf_close"
  val PRF_CHAIN = "prf_chain"
  val PRF_DECL = "prf_decl"
  val PRF_ASM = "prf_asm"
  val PRF_ASM_GOAL = "prf_asm_goal"
  val PRF_ASM_GOAL_SCRIPT = "prf_asm_goal_script"
  val PRF_SCRIPT = "prf_script"


  /* categories */

  val diag = Set(DIAG)

  val heading = Set(HEADING)

  val theory = Set(THY_BEGIN, THY_END, THY_LOAD, THY_DECL, THY_DECL_BLOCK, THY_GOAL)

  val theory_block = Set(THY_BEGIN, THY_DECL_BLOCK)

  val theory_body = Set(THY_LOAD, THY_DECL, THY_DECL_BLOCK, THY_GOAL)

  val proof =
    Set(QED, QED_SCRIPT, QED_BLOCK, QED_GLOBAL, PRF_GOAL, PRF_BLOCK, PRF_OPEN, PRF_CLOSE,
      PRF_CHAIN, PRF_DECL, PRF_ASM, PRF_ASM_GOAL, PRF_ASM_GOAL_SCRIPT, PRF_SCRIPT)

  val proof_body =
    Set(DIAG, HEADING, PRF_BLOCK, PRF_OPEN, PRF_CLOSE, PRF_CHAIN, PRF_DECL, PRF_ASM,
      PRF_ASM_GOAL, PRF_ASM_GOAL_SCRIPT, PRF_SCRIPT)

  val theory_goal = Set(THY_GOAL)
  val proof_goal = Set(PRF_GOAL, PRF_ASM_GOAL, PRF_ASM_GOAL_SCRIPT)
  val qed = Set(QED, QED_SCRIPT, QED_BLOCK)
  val qed_global = Set(QED_GLOBAL)


  type Spec = ((String, List[String]), List[String])



  /** keyword tables **/

  object Keywords
  {
    def empty: Keywords = new Keywords()

    def apply(names: List[String]): Keywords =
      (empty /: names)({ case (keywords, a) => keywords + (a, (MINOR, Nil)) })
  }

  class Keywords private(
    keywords: Map[String, (String, List[String])] = Map.empty,
    val minor: Scan.Lexicon = Scan.Lexicon.empty,
    val major: Scan.Lexicon = Scan.Lexicon.empty)
  {
    /* content */

    override def toString: String =
      (for ((name, (kind, files)) <- keywords) yield {
        if (kind == MINOR) quote(name)
        else
          quote(name) + " :: " + quote(kind) +
          (if (files.isEmpty) "" else " (" + commas_quote(files) + ")")
      }).toList.sorted.mkString("keywords\n  ", " and\n  ", "")

    def is_empty: Boolean = keywords.isEmpty

    def + (name: String, kind: (String, List[String])): Keywords =
    {
      val keywords1 = keywords + (name -> kind)
      val (minor1, major1) =
        if (kind._1 == MINOR) (minor + name, major) else (minor, major + name)
      new Keywords(keywords1, minor1, major1)
    }


    /* kind */

    def kind(name: String): Option[String] = keywords.get(name).map(_._1)

    def command_kind(token: Token, pred: String => Boolean): Boolean =
      token.is_command &&
        (kind(token.source) match { case Some(k) => k != MINOR && pred(k) case None => false })


    /* load commands */

    def load_command(name: String): Option[List[String]] =
      keywords.get(name) match {
        case Some((THY_LOAD, exts)) => Some(exts)
        case _ => None
      }

    private lazy val load_commands: List[(String, List[String])] =
      (for ((name, (THY_LOAD, files)) <- keywords.iterator) yield (name, files)).toList

    def load_commands_in(text: String): Boolean =
      load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })
  }
}

