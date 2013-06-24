/*  Title:      Pure/Tools/keywords.scala
    Author:     Makarius

Generate keyword files for Emacs Proof General.
*/

package isabelle


import scala.collection.mutable


object Keywords
{
  /* keywords */

  private val convert_kinds = Map(
    "thy_begin" -> "theory-begin",
    "thy_end" -> "theory-end",
    "thy_heading1" -> "theory-heading",
    "thy_heading2" -> "theory-heading",
    "thy_heading3" -> "theory-heading",
    "thy_heading4" -> "theory-heading",
    "thy_load" -> "theory-decl",
    "thy_decl" -> "theory-decl",
    "thy_script" -> "theory-script",
    "thy_goal" -> "theory-goal",
    "qed_block" -> "qed-block",
    "qed_global" -> "qed-global",
    "prf_heading2" -> "proof-heading",
    "prf_heading3" -> "proof-heading",
    "prf_heading4" -> "proof-heading",
    "prf_goal" -> "proof-goal",
    "prf_block" -> "proof-block",
    "prf_open" -> "proof-open",
    "prf_close" -> "proof-close",
    "prf_chain" -> "proof-chain",
    "prf_decl" -> "proof-decl",
    "prf_asm" -> "proof-asm",
    "prf_asm_goal" -> "proof-asm-goal",
    "prf_script" -> "proof-script"
  ).withDefault((s: String) => s)

  private val emacs_kinds = List(
    "major",
    "minor",
    "control",
    "diag",
    "theory-begin",
    "theory-switch",
    "theory-end",
    "theory-heading",
    "theory-decl",
    "theory-script",
    "theory-goal",
    "qed",
    "qed-block",
    "qed-global",
    "proof-heading",
    "proof-goal",
    "proof-block",
    "proof-open",
    "proof-close",
    "proof-chain",
    "proof-decl",
    "proof-asm",
    "proof-asm-goal",
    "proof-script")

  def keywords(
    options: Options,
    name: String = "",
    dirs: List[Path] = Nil,
    sessions: List[String] = Nil)
  {
    val deps = Build.session_dependencies(options, false, dirs, sessions).deps
    val keywords =
    {
      var keywords = Map.empty[String, String]
      for {
        (_, dep) <- deps
        (name, kind_spec, _) <- dep.keywords
        kind = kind_spec match { case Some(((kind, _), _)) => kind case None => "minor" }
        k = convert_kinds(kind)
      } {
        keywords.get(name) match {
          case Some(k1) if k1 != k && k1 != "minor" && k != "minor" =>
            error("Inconsistent declaration of keyword " + quote(name) + ": " + k1 + " vs " + k)
          case _ =>
        }
        keywords += (name -> k)
      }
      keywords
    }

    val output =
    {
      val out = new mutable.StringBuilder

      out ++= ";;\n"
      out ++= ";; Generated keyword classification tables for Isabelle/Isar.\n"
      out ++= ";; *** DO NOT EDIT *** DO NOT EDIT *** DO NOT EDIT ***\n"
      out ++= ";;\n"

      for (kind <- emacs_kinds) {
        val names =
          (for {
            (name, k) <- keywords.iterator
            if (if (kind == "major") k != "minor" else k == kind)
            if kind != "minor" || Symbol.is_ascii_identifier(name)
          } yield name).toList.sorted

        out ++= "\n(defconst isar-keywords-" + kind
        out ++= "\n  '("
        out ++=
          names.map(name => quote("""[\.\*\+\?\[\]\^\$]""".r replaceAllIn (name, """\\\\$0""")))
            .mkString("\n    ")
        out ++= "))\n"
      }

      out ++= "\n(provide 'isar-keywords)\n"

      out.toString
    }

    val file = if (name == "") "isar-keywords.el" else "isar-keywords-" + name + ".el"
    java.lang.System.err.println(file)
    File.write(Path.explode(file), output)
  }


  /* administrative update_keywords */

  def update_keywords(options: Options)
  {
    val tree = Build.find_sessions(options, Nil)

    def chapter(ch: String): List[String] =
      for ((name, info) <- tree.topological_order if info.chapter == ch) yield name

    keywords(options, sessions = chapter("HOL"))
    keywords(options, name = "ZF", sessions = chapter("ZF"))
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      args.toList match {
        case "keywords" :: name :: Command_Line.Chunks(dirs, sessions) =>
          keywords(Options.init(), name, dirs.map(Path.explode), sessions)
          0
        case "update_keywords" :: Nil =>
          update_keywords(Options.init())
          0
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}

