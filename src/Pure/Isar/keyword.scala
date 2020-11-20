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
  val DOCUMENT_HEADING = "document_heading"
  val DOCUMENT_BODY = "document_body"
  val DOCUMENT_RAW = "document_raw"
  val THY_BEGIN = "thy_begin"
  val THY_END = "thy_end"
  val THY_DECL = "thy_decl"
  val THY_DECL_BLOCK = "thy_decl_block"
  val THY_DEFN = "thy_defn"
  val THY_STMT = "thy_stmt"
  val THY_LOAD = "thy_load"
  val THY_GOAL = "thy_goal"
  val THY_GOAL_DEFN = "thy_goal_defn"
  val THY_GOAL_STMT = "thy_goal_stmt"
  val QED = "qed"
  val QED_SCRIPT = "qed_script"
  val QED_BLOCK = "qed_block"
  val QED_GLOBAL = "qed_global"
  val PRF_GOAL = "prf_goal"
  val PRF_BLOCK = "prf_block"
  val NEXT_BLOCK = "next_block"
  val PRF_OPEN = "prf_open"
  val PRF_CLOSE = "prf_close"
  val PRF_CHAIN = "prf_chain"
  val PRF_DECL = "prf_decl"
  val PRF_ASM = "prf_asm"
  val PRF_ASM_GOAL = "prf_asm_goal"
  val PRF_SCRIPT = "prf_script"
  val PRF_SCRIPT_GOAL = "prf_script_goal"
  val PRF_SCRIPT_ASM_GOAL = "prf_script_asm_goal"

  val BEFORE_COMMAND = "before_command"
  val QUASI_COMMAND = "quasi_command"


  /* command categories */

  val vacuous = Set(DIAG, DOCUMENT_HEADING, DOCUMENT_BODY, DOCUMENT_RAW)

  val diag = Set(DIAG)

  val document_heading = Set(DOCUMENT_HEADING)
  val document_body = Set(DOCUMENT_BODY)
  val document_raw = Set(DOCUMENT_RAW)
  val document = Set(DOCUMENT_HEADING, DOCUMENT_BODY, DOCUMENT_RAW)

  val theory_begin = Set(THY_BEGIN)
  val theory_end = Set(THY_END)

  val theory_load = Set(THY_LOAD)

  val theory =
    Set(THY_BEGIN, THY_END, THY_LOAD, THY_DECL, THY_DECL_BLOCK, THY_DEFN, THY_STMT,
      THY_GOAL, THY_GOAL_DEFN, THY_GOAL_STMT)

  val theory_block = Set(THY_BEGIN, THY_DECL_BLOCK)

  val theory_body =
    Set(THY_LOAD, THY_DECL, THY_DECL_BLOCK, THY_DEFN, THY_STMT,
      THY_GOAL, THY_GOAL_DEFN, THY_GOAL_STMT)

  val theory_defn = Set(THY_DEFN, THY_GOAL_DEFN)

  val prf_script = Set(PRF_SCRIPT)

  val proof =
    Set(QED, QED_SCRIPT, QED_BLOCK, QED_GLOBAL, PRF_GOAL, PRF_BLOCK, NEXT_BLOCK, PRF_OPEN,
      PRF_CLOSE, PRF_CHAIN, PRF_DECL, PRF_ASM, PRF_ASM_GOAL, PRF_SCRIPT, PRF_SCRIPT_GOAL,
      PRF_SCRIPT_ASM_GOAL)

  val proof_body =
    Set(DIAG, DOCUMENT_HEADING, DOCUMENT_BODY, DOCUMENT_RAW, PRF_BLOCK, NEXT_BLOCK, PRF_OPEN,
      PRF_CLOSE, PRF_CHAIN, PRF_DECL, PRF_ASM, PRF_ASM_GOAL, PRF_SCRIPT, PRF_SCRIPT_GOAL,
      PRF_SCRIPT_ASM_GOAL)

  val proof_asm = Set(PRF_ASM, PRF_ASM_GOAL)
  val improper = Set(QED_SCRIPT, PRF_SCRIPT, PRF_SCRIPT_GOAL, PRF_SCRIPT_ASM_GOAL)

  val theory_goal = Set(THY_GOAL, THY_GOAL_DEFN, THY_GOAL_STMT)
  val proof_goal = Set(PRF_GOAL, PRF_ASM_GOAL, PRF_SCRIPT_GOAL, PRF_SCRIPT_ASM_GOAL)
  val qed = Set(QED, QED_SCRIPT, QED_BLOCK)
  val qed_global = Set(QED_GLOBAL)

  val proof_open = proof_goal + PRF_OPEN
  val proof_close = qed + PRF_CLOSE
  val proof_enclose = Set(PRF_BLOCK, NEXT_BLOCK, QED_BLOCK, PRF_CLOSE)

  val close_structure = Set(NEXT_BLOCK, QED_BLOCK, PRF_CLOSE, THY_END)



  /** keyword tables **/

  object Spec
  {
    val none: Spec = Spec("")
  }
  sealed case class Spec(kind: String, exts: List[String] = Nil, tags: List[String] = Nil)
  {
    def is_none: Boolean = kind == ""

    override def toString: String =
      kind +
        (if (exts.isEmpty) "" else " (" + commas_quote(exts) + ")") +
        (if (tags.isEmpty) "" else tags.map(quote).mkString(" % ", " % ", ""))
  }

  object Keywords
  {
    def empty: Keywords = new Keywords()
  }

  class Keywords private(
    val kinds: Map[String, String] = Map.empty,
    val load_commands: Map[String, List[String]] = Map.empty)
  {
    override def toString: String =
    {
      val entries =
        for ((name, kind) <- kinds.toList.sortBy(_._1)) yield {
          val exts = load_commands.getOrElse(name, Nil)
          val kind_decl =
            if (kind == "") ""
            else " :: " + quote(kind) + (if (exts.isEmpty) "" else " (" + commas_quote(exts) + ")")
          quote(name) + kind_decl
        }
      entries.mkString("keywords\n  ", " and\n  ", "")
    }


    /* merge */

    def is_empty: Boolean = kinds.isEmpty

    def ++ (other: Keywords): Keywords =
      if (this eq other) this
      else if (is_empty) other
      else {
        val kinds1 =
          if (kinds eq other.kinds) kinds
          else if (kinds.isEmpty) other.kinds
          else (kinds /: other.kinds) { case (m, e) => if (m.isDefinedAt(e._1)) m else m + e }
        val load_commands1 =
          if (load_commands eq other.load_commands) load_commands
          else if (load_commands.isEmpty) other.load_commands
          else
            (load_commands /: other.load_commands) {
              case (m, e) => if (m.isDefinedAt(e._1)) m else m + e }
        new Keywords(kinds1, load_commands1)
      }


    /* add keywords */

    def + (name: String, kind: String = "", exts: List[String] = Nil): Keywords =
    {
      val kinds1 = kinds + (name -> kind)
      val load_commands1 =
        if (kind == THY_LOAD) {
          if (!Symbol.iterator(name).forall(Symbol.is_ascii))
            error("Bad theory load command " + quote(name))
          load_commands + (name -> exts)
        }
        else load_commands
      new Keywords(kinds1, load_commands1)
    }

    def add_keywords(header: Thy_Header.Keywords): Keywords =
      (this /: header) {
        case (keywords, (name, spec)) =>
          if (spec.is_none)
            keywords + Symbol.decode(name) + Symbol.encode(name)
          else
            keywords +
              (Symbol.decode(name), spec.kind, spec.exts) +
              (Symbol.encode(name), spec.kind, spec.exts)
      }


    /* command kind */

    def is_command(token: Token, check_kind: String => Boolean): Boolean =
      token.is_command &&
        (kinds.get(token.source) match { case Some(k) => check_kind(k) case None => false })

    def is_before_command(token: Token): Boolean =
      token.is_keyword && kinds.get(token.source) == Some(BEFORE_COMMAND)

    def is_quasi_command(token: Token): Boolean =
      token.is_keyword && kinds.get(token.source) == Some(QUASI_COMMAND)

    def is_indent_command(token: Token): Boolean =
      token.is_begin_or_command || is_quasi_command(token)


    /* load commands */

    def load_commands_in(text: String): Boolean =
      load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })


    /* lexicons */

    private def make_lexicon(is_minor: Boolean): Scan.Lexicon =
      (Scan.Lexicon.empty /: kinds)(
        {
          case (lex, (name, kind)) =>
            if ((kind == "" || kind == BEFORE_COMMAND || kind == QUASI_COMMAND) == is_minor)
              lex + name
            else lex
        })

    lazy val minor: Scan.Lexicon = make_lexicon(true)
    lazy val major: Scan.Lexicon = make_lexicon(false)
  }
}
