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
    @tailrec def update(toks: List[Token], result: List[String]): String =
    {
      toks match {
        case tok :: rest if tok.source == "--" || tok.source == Symbol.comment =>
          rest.dropWhile(_.is_space) match {
            case tok1 :: rest1 if tok1.is_text =>
              val res = Symbol.comment + Symbol.space + Library.cartouche(tok1.content)
              update(rest1, res :: result)
            case _ => update(rest, tok.source :: result)
          }
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
    Isabelle_Tool("update_comments", "update formal comments in outer syntax", args =>
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
      } update_comments(Path.explode(File.standard_path(file)))
    })
}
