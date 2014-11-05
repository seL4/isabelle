/*  Title:      Pure/Isar/keyword.scala
    Author:     Makarius

Isar keyword classification.
*/

package isabelle


object Keyword
{
  /** keyword classification **/

  /* kinds */

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

    def apply(keywords: List[String]): Keywords = (empty /: keywords)(_ + _)
  }

  class Keywords private(
    val minor: Scan.Lexicon = Scan.Lexicon.empty,
    val major: Scan.Lexicon = Scan.Lexicon.empty,
    commands: Map[String, (String, List[String])] = Map.empty)
  {
    /* content */

    def is_empty: Boolean = minor.isEmpty && major.isEmpty

    override def toString: String =
    {
      val keywords1 = minor.iterator.map(quote(_)).toList
      val keywords2 =
        for ((name, (kind, files)) <- commands.toList.sortBy(_._1)) yield {
          quote(name) + " :: " + quote(kind) +
          (if (files.isEmpty) "" else " (" + commas_quote(files) + ")")
        }
      (keywords1 ::: keywords2).mkString("keywords\n  ", " and\n  ", "")
    }


    /* add keywords */

    def + (name: String): Keywords =
      new Keywords(minor + name, major, commands)

    def + (name: String, kind: (String, List[String])): Keywords =
    {
      val major1 = major + name
      val commands1 = commands + (name -> kind)
      new Keywords(minor, major1, commands1)
    }


    /* command kind */

    def command_kind(name: String): Option[String] = commands.get(name).map(_._1)

    def is_command_kind(token: Token, pred: String => Boolean): Boolean =
      token.is_command &&
        (command_kind(token.source) match { case Some(k) => pred(k) case None => false })


    /* load commands */

    def load_command(name: String): Option[List[String]] =
      commands.get(name) match {
        case Some((THY_LOAD, exts)) => Some(exts)
        case _ => None
      }

    private lazy val load_commands: List[(String, List[String])] =
      (for ((name, (THY_LOAD, files)) <- commands.iterator) yield (name, files)).toList

    def load_commands_in(text: String): Boolean =
      load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })
  }
}

