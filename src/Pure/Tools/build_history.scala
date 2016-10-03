/*  Title:      Pure/Tools/build_history.scala
    Author:     Makarius

Build other history versions.
*/

package isabelle


import java.io.{File => JFile}


object Build_History
{
  def apply(hg: Mercurial.Repository, rev: String = "",
    isabelle_identifier: String = "build_history"): Build_History =
      new Build_History(hg, rev, isabelle_identifier)


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var force = false

      val getopts = Getopts("""
Usage: isabelle build_history [OPTIONS] REPOSITORY [REV]

  Options are:
    -f           force -- allow irreversible operations on REPOSITORY

  Build Isabelle sessions from the history of another REPOSITORY clone,
  starting at changeset REV (default: tip).
""",
        "f" -> (_ => force = true))

      val more_args = getopts(args)

      val (root, rev) =
        more_args match {
          case List(root, rev) => (root, rev)
          case List(root) => (root, "tip")
          case _ => getopts.usage()
        }

      using(Mercurial.open_repository(Path.explode(root)))(hg =>
        {
          val build_history = Build_History(hg, rev)

          if (!force)
            error("Repository " + hg + " will be cleaned by force!\n" +
              "Need to provide option -f to confirm this.")

          build_history.init()

          Output.writeln(
            build_history.bash("bin/isabelle getenv ISABELLE_HOME ISABELLE_HOME_USER").check.out)
        })
    }
  }
}

class Build_History private(hg: Mercurial.Repository, rev: String, isabelle_identifier: String)
{
  override def toString: String =
    List(hg.toString, rev, isabelle_identifier).mkString("Build_History(", ",", ")")

  def bash(script: String): Process_Result =
    Isabelle_System.bash("env ISABELLE_IDENTIFIER=" + File.bash_string(isabelle_identifier) +
      " " + script, cwd = hg.root.file, env = null)

  def init()
  {
    hg.update(rev = rev, clean = true)
  }
}
