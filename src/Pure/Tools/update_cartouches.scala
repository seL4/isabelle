/*  Title:      Pure/Tools/update_cartouches.scala
    Author:     Makarius

Update theory syntax to use cartouches etc.
*/

package isabelle


import scala.util.matching.Regex


object Update_Cartouches
{
  /* update cartouches */

  private val Verbatim_Body = """(?s)[ \t]*(.*?)[ \t]*""".r

  val Text_Antiq: Regex = """(?s)@\{\s*text\b\s*(.+)\}""".r

  def update_text(content: String): String =
  {
    (try { Some(Antiquote.read(content)) } catch { case ERROR(_) => None }) match {
      case Some(ants) =>
        val ants1: List[Antiquote.Antiquote] =
          ants.map(ant =>
            ant match {
              case Antiquote.Antiq(Text_Antiq(body)) =>
                Token.explode(Keyword.Keywords.empty, body).filterNot(_.is_space) match {
                  case List(tok) => Antiquote.Control(Symbol.cartouche(tok.content))
                  case _ => ant
                }
              case _ => ant
            })
        if (ants == ants1) content else ants1.map(_.source).mkString
      case None => content
    }
  }

  def update_cartouches(replace_text: Boolean, path: Path)
  {
    val text0 = File.read(path)

    // outer syntax cartouches
    val text1 =
      (for (tok <- Token.explode(Keyword.Keywords.empty, text0).iterator)
        yield {
          if (tok.kind == Token.Kind.ALT_STRING) Symbol.cartouche(tok.content)
          else if (tok.kind == Token.Kind.VERBATIM) {
            tok.content match {
              case Verbatim_Body(s) => Symbol.cartouche(s)
              case s => tok.source
            }
          }
          else tok.source
        }
      ).mkString

    // cartouches within presumed text tokens
    val text2 =
      if (replace_text) {
        (for (tok <- Token.explode(Keyword.Keywords.empty, text1).iterator)
          yield {
            if (tok.kind == Token.Kind.STRING || tok.kind == Token.Kind.CARTOUCHE) {
              val content = tok.content
              val content1 = update_text(content)

              if (content == content1) tok.source
              else if (tok.kind == Token.Kind.STRING) Outer_Syntax.quote_string(content1)
              else Symbol.cartouche(content1)
            }
            else tok.source
          }).mkString
      }
      else text1

    if (text0 != text2) {
      Output.writeln("changing " + path)
      File.write_backup2(path, text2)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update_cartouches", "update theory syntax to use cartouches",
      Scala_Project.here, args =>
    {
      var replace_text = false

      val getopts = Getopts("""
Usage: isabelle update_cartouches [FILES|DIRS...]

  Options are:
    -t           replace @{text} antiquotations within text tokens

  Recursively find .thy or ROOT files and update theory syntax to use
  cartouches instead of old-style {* verbatim *} or `alt_string` tokens.

  Old versions of files are preserved by appending "~~".
""",
        "t" -> (_ => replace_text = true))

      val specs = getopts(args)
      if (specs.isEmpty) getopts.usage()

      for {
        spec <- specs
        file <- File.find_files(Path.explode(spec).file,
          file => file.getName.endsWith(".thy") || file.getName == "ROOT")
      } update_cartouches(replace_text, File.path(file))
    })
}
