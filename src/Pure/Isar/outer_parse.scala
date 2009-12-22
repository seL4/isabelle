/*  Title:      Pure/Isar/outer_parse.scala
    Author:     Makarius

Generic parsers for Isabelle/Isar outer syntax.
*/

package isabelle

import scala.util.parsing.combinator.Parsers


object Outer_Parse
{
  /* parsing tokens */

  trait Parser extends Parsers
  {
    type Elem = Outer_Lex.Token

    private def proper(in: Input): Input =
      if (in.atEnd || in.first.is_proper) in
      else proper(in.rest)

    def token(s: String, pred: Elem => Boolean): Parser[Elem] = new Parser[Elem]
    {
      def apply(raw_input: Input) =
      {
        val in = proper(raw_input)
        if (in.atEnd) Failure(s + " expected (past end-of-file!)", in)
        else {
          val token = in.first
          if (pred(token)) Success(token, proper(in.rest))
          else
            token.text match {
              case (txt, "") =>
                Failure(s + " expected,\nbut " + txt + " was found", in)
              case (txt1, txt2) =>
                Failure(s + " expected,\nbut " + txt1 + " was found:\n" + txt2, in)
            }
        }
      }
    }

    def not_eof: Parser[Elem] = token("input token", _ => true)

    def keyword(name: String): Parser[Elem] =
      token(Outer_Lex.Token_Kind.KEYWORD.toString + " \"" + name + "\"",
        tok => tok.kind == Outer_Lex.Token_Kind.KEYWORD && tok.content == name)

    def name: Parser[Elem] = token("name declaration", _.is_name)
    def xname: Parser[Elem] = token("name reference", _.is_xname)
    def text: Parser[Elem] = token("text", _.is_text)
    def path: Parser[Elem] = token("file name/path specification", _.is_name)


    /* wrappers */

    def parse[T](p: Parser[T], in: Outer_Lex.Reader): ParseResult[T] = p(in)
    def parse_all[T](p: Parser[T], in: Outer_Lex.Reader): ParseResult[T] = parse(phrase(p), in)
  }
}

