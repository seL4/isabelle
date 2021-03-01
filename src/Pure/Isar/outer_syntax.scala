/*  Title:      Pure/Isar/outer_syntax.scala
    Author:     Makarius

Isabelle/Isar outer syntax.
*/

package isabelle


import scala.collection.mutable


object Outer_Syntax
{
  /* syntax */

  val empty: Outer_Syntax = new Outer_Syntax()

  def merge(syns: List[Outer_Syntax]): Outer_Syntax = (empty /: syns)(_ ++ _)


  /* string literals */

  def quote_string(str: String): String =
  {
    val result = new StringBuilder(str.length + 10)
    result += '"'
    for (s <- Symbol.iterator(str)) {
      if (s.length == 1) {
        val c = s(0)
        if (c < 32 && c != YXML.X && c != YXML.Y || c == '\\' || c == '"') {
          result += '\\'
          if (c < 10) result += '0'
          if (c < 100) result += '0'
          result ++= c.asInstanceOf[Int].toString
        }
        else result += c
      }
      else result ++= s
    }
    result += '"'
    result.toString
  }
}

final class Outer_Syntax private(
  val keywords: Keyword.Keywords = Keyword.Keywords.empty,
  val rev_abbrevs: Thy_Header.Abbrevs = Nil,
  val language_context: Completion.Language_Context = Completion.Language_Context.outer,
  val has_tokens: Boolean = true)
{
  /** syntax content **/

  override def toString: String = keywords.toString


  /* keywords */

  def + (name: String, kind: String = "", load_command: String = ""): Outer_Syntax =
    new Outer_Syntax(
      keywords + (name, kind, load_command), rev_abbrevs, language_context, has_tokens = true)

  def add_keywords(keywords: Thy_Header.Keywords): Outer_Syntax =
    (this /: keywords) {
      case (syntax, (name, spec)) =>
        syntax +
          (Symbol.decode(name), spec.kind, spec.load_command) +
          (Symbol.encode(name), spec.kind, spec.load_command)
    }


  /* abbrevs */

  def abbrevs: Thy_Header.Abbrevs = rev_abbrevs.reverse

  def add_abbrevs(new_abbrevs: Thy_Header.Abbrevs): Outer_Syntax =
    if (new_abbrevs.isEmpty) this
    else {
      val rev_abbrevs1 = Library.distinct(new_abbrevs) reverse_::: rev_abbrevs
      new Outer_Syntax(keywords, rev_abbrevs1, language_context, has_tokens)
    }


  /* completion */

  private lazy val completion: Completion =
  {
    val completion_keywords = (keywords.minor.iterator ++ keywords.major.iterator).toList
    val completion_abbrevs =
      completion_keywords.flatMap(name =>
        (if (Keyword.theory_block.contains(keywords.kinds(name)))
          List((name, name + "\nbegin\n\u0007\nend"))
         else Nil) :::
        (if (Completion.Word_Parsers.is_word(name)) List((name, name)) else Nil)) :::
      abbrevs.flatMap(
        { case (a, b) =>
            val a1 = Symbol.decode(a)
            val a2 = Symbol.encode(a)
            val b1 = Symbol.decode(b)
            List((a1, b1), (a2, b1))
        })
    Completion.make(completion_keywords, completion_abbrevs)
  }

  def complete(
    history: Completion.History,
    unicode: Boolean,
    explicit: Boolean,
    start: Text.Offset,
    text: CharSequence,
    caret: Int,
    context: Completion.Language_Context): Option[Completion.Result] =
  {
    completion.complete(history, unicode, explicit, start, text, caret, context)
  }


  /* build */

  def + (header: Document.Node.Header): Outer_Syntax =
    add_keywords(header.keywords).add_abbrevs(header.abbrevs)

  def ++ (other: Outer_Syntax): Outer_Syntax =
    if (this eq other) this
    else if (this eq Outer_Syntax.empty) other
    else {
      val keywords1 = keywords ++ other.keywords
      val rev_abbrevs1 = Library.merge(rev_abbrevs, other.rev_abbrevs)
      if ((keywords eq keywords1) && (rev_abbrevs eq rev_abbrevs1)) this
      else new Outer_Syntax(keywords1, rev_abbrevs1, language_context, has_tokens)
    }


  /* load commands */

  def load_command(name: String): Option[String] =
    keywords.load_commands.get(name)

  def has_load_commands(text: String): Boolean =
    keywords.load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })


  /* language context */

  def set_language_context(context: Completion.Language_Context): Outer_Syntax =
    new Outer_Syntax(keywords, rev_abbrevs, context, has_tokens)

  def no_tokens: Outer_Syntax =
  {
    require(keywords.is_empty, "bad syntax keywords")
    new Outer_Syntax(
      rev_abbrevs = rev_abbrevs,
      language_context = language_context,
      has_tokens = false)
  }



  /** parsing **/

  /* command spans */

  def parse_spans(toks: List[Token]): List[Command_Span.Span] =
  {
    val result = new mutable.ListBuffer[Command_Span.Span]
    val content = new mutable.ListBuffer[Token]
    val ignored = new mutable.ListBuffer[Token]

    def ship(content: List[Token]): Unit =
    {
      val kind =
        if (content.forall(_.is_ignored)) Command_Span.Ignored_Span
        else if (content.exists(_.is_error)) Command_Span.Malformed_Span
        else
          content.find(_.is_command) match {
            case None => Command_Span.Malformed_Span
            case Some(cmd) =>
              val name = cmd.source
              val offset =
                (0 /: content.takeWhile(_ != cmd)) {
                  case (i, tok) => i + Symbol.length(tok.source) }
              val end_offset = offset + Symbol.length(name)
              val range = Text.Range(offset, end_offset) + 1
              Command_Span.Command_Span(name, Position.Range(range))
          }
      result += Command_Span.Span(kind, content)
    }

    def flush(): Unit =
    {
      if (content.nonEmpty) { ship(content.toList); content.clear }
      if (ignored.nonEmpty) { ship(ignored.toList); ignored.clear }
    }

    for (tok <- toks) {
      if (tok.is_ignored) ignored += tok
      else if (keywords.is_before_command(tok) ||
        tok.is_command &&
          (!content.exists(keywords.is_before_command) || content.exists(_.is_command)))
      { flush(); content += tok }
      else { content ++= ignored; ignored.clear; content += tok }
    }
    flush()

    result.toList
  }

  def parse_spans(input: CharSequence): List[Command_Span.Span] =
    parse_spans(Token.explode(keywords, input))
}
