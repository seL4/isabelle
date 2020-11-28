/*  Title:      Pure/Tools/update_comments.scala
    Author:     Makarius

Update formal comments in outer syntax: \<comment> \<open>...\<close>
*/

package isabelle


import scala.annotation.tailrec


object Update_Comments
{
  def update_comments(path: Path)
  {
    def make_comment(tok: Token): String =
      Symbol.comment + Symbol.space + Symbol.cartouche(Symbol.trim_blanks(tok.content))

    @tailrec def update(toks: List[Token], result: List[String]): String =
    {
      toks match {
        case tok :: rest
        if tok.source == "--" || tok.source == Symbol.comment =>
          rest.dropWhile(_.is_space) match {
            case tok1 :: rest1 if tok1.is_text =>
              update(rest1, make_comment(tok1) :: result)
            case _ => update(rest, tok.source :: result)
          }
        case tok :: rest if tok.is_formal_comment && tok.source.startsWith(Symbol.comment) =>
          update(rest, make_comment(tok) :: result)
        case tok :: rest => update(rest, tok.source :: result)
        case Nil => result.reverse.mkString
      }
    }

    val text0 = File.read(path)
    val text1 = update(Token.explode(Keyword.Keywords.empty, text0), Nil)

    if (text0 != text1) {
      Output.writeln("changing " + path)
      File.write_backup2(path, text1)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update_comments", "update formal comments in outer syntax",
      Scala_Project.here, args =>
    {
      val getopts = Getopts("""
Usage: isabelle update_comments [FILES|DIRS...]

  Recursively find .thy files and update formal comments in outer syntax.

  Old versions of files are preserved by appending "~~".
""")

      val specs = getopts(args)
      if (specs.isEmpty) getopts.usage()

      for {
        spec <- specs
        file <- File.find_files(Path.explode(spec).file, file => file.getName.endsWith(".thy"))
      } update_comments(File.path(file))
    })
}
