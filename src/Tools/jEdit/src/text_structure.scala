/*  Title:      Tools/jEdit/src/text_structure.scala
    Author:     Makarius

Text structure based on Isabelle/Isar outer syntax.
*/

package isabelle.jedit


import isabelle._

import java.util.{List => JList}

import org.gjt.sp.jedit.indent.{IndentRule, IndentAction}
import org.gjt.sp.jedit.textarea.{TextArea, StructureMatcher, Selection}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.jEdit

object Text_Structure {
  /* token navigator */

  class Navigator(syntax: Outer_Syntax, buffer: JEditBuffer, comments: Boolean) {
    val limit: Int = PIDE.options.value.int("jedit_structure_limit") max 0

    def iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] = {
      val it = Token_Markup.line_token_iterator(syntax, buffer, line, line + lim)
      if (comments) it.filterNot(_.info.is_space) else it.filter(_.info.is_proper)
    }

    def reverse_iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] = {
      val it = Token_Markup.line_token_reverse_iterator(syntax, buffer, line, line - lim)
      if (comments) it.filterNot(_.info.is_space) else it.filter(_.info.is_proper)
    }
  }


  /* indentation */

  object Indent_Rule extends IndentRule {
    private val keyword_open = Keyword.theory_goal ++ Keyword.proof_open
    private val keyword_close = Keyword.proof_close
    // Indent diff applied to the first line of the current command, to be applied to
    // remaining lines
    private var current_command_diff: Option[Int] = None

    def apply(
      buffer: JEditBuffer,
      current_line: Int,
      prev_line0: Int,
      prev_prev_line0: Int,
      actions: JList[IndentAction]
    ): Unit = {
      // Get the start and end line numbers of the currently selected region
      val text_area = jEdit.getActiveView.getTextArea
      val selections = text_area.getSelection

      val (selection_start_line, selection_end_line) =
        if (!selections.isEmpty) {
          (selections(0).getStartLine, selections(0).getEndLine)
        } else {
          val caret_line = text_area.getCaretLine
          (caret_line, caret_line)
        }

      // Clear cached diff on first line of selection to prevent usage of a stale value
      if (current_line == selection_start_line) {
        current_command_diff = None
      }

      Isabelle.buffer_syntax(buffer) match {
        case Some(syntax) =>
          val keywords = syntax.keywords
          val nav = new Navigator(syntax, buffer, true)

          val indent_size = buffer.getIndentSize


          def line_indent(line: Int): Int =
            if (line < 0 || line >= buffer.getLineCount) 0
            else buffer.getCurrentIndentForLine(line, null)

          def line_head(line: Int): Option[Text.Info[Token]] =
            nav.iterator(line, 1).nextOption()

          def head_is_quasi_command(line: Int): Boolean =
            line_head(line) match {
              case None => false
              case Some(Text.Info(_, tok)) => keywords.is_quasi_command(tok)
            }

          val prev_line: Int =
            Range.inclusive(current_line - 1, 0, -1).find(line =>
              Token_Markup.Line_Context.before(buffer, line).get_context == Scan.Finished &&
              (!Token_Markup.Line_Context.after(buffer, line).structure.improper ||
                Token_Markup.Line_Context.after(buffer, line).structure.blank)) getOrElse -1

          def prev_line_command: Option[Token] =
            nav.reverse_iterator(prev_line, 1).
              collectFirst({ case Text.Info(_, tok) if tok.is_begin_or_command => tok })

          def prev_line_span: Iterator[Token] =
            nav.reverse_iterator(prev_line, 1).map(_.info).takeWhile(tok => !tok.is_begin_or_command)

          def prev_span: Iterator[Token] =
            nav.reverse_iterator(prev_line).map(_.info).takeWhile(tok => !tok.is_begin_or_command)


          val script_indent: Text.Info[Token] => Int = {
            val opt_rendering: Option[JEdit_Rendering] =
              if (PIDE.options.value.bool("jedit_indent_script"))
                GUI_Thread.now {
                  (for {
                    text_area <- JEdit_Lib.jedit_text_areas(buffer)
                    rendering <- Document_View.get_rendering(text_area)
                  } yield rendering).nextOption()
                }
              else None
            val limit = PIDE.options.value.int("jedit_indent_script_limit")
            (info: Text.Info[Token]) =>
              opt_rendering match {
                case Some(rendering) if keywords.is_command(info.info, Keyword.prf_script) =>
                  (rendering.indentation(info.range) min limit) max 0
                case _ => 0
              }
          }

          def indent_indent(tok: Token): Int =
            if (keywords.is_command(tok, keyword_open)) indent_size
            else if (keywords.is_command(tok, keyword_close)) { - indent_size }
            else 0

          def indent_offset(tok: Token): Int =
            if (keywords.is_command(tok, Keyword.proof_enclose)) indent_size
            else 0

          def indent_structure: Int =
            nav.reverse_iterator(current_line - 1).scanLeft((0, false))(
              { case ((ind, _), Text.Info(range, tok)) =>
                  val ind1 = ind + indent_indent(tok)
                  if (tok.is_begin_or_command && !keywords.is_command(tok, Keyword.prf_script)) {
                    val line = buffer.getLineOfOffset(range.start)
                    line_head(line) match {
                      case Some(info) if info.info == tok =>
                        (ind1 + indent_offset(tok) + line_indent(line), true)
                      case _ => (ind1, false)
                    }
                  }
                  else (ind1, false)
              }).collectFirst({ case (i, true) => i }).getOrElse(0)

          def indent_brackets: Int =
            prev_line_span.foldLeft(0) {
              case (i, tok) =>
                if (tok.is_open_bracket) i + indent_size
                else if (tok.is_close_bracket) i - indent_size
                else i
            }

          def indent_extra: Int =
            if (prev_span.exists(keywords.is_quasi_command)) indent_size
            else 0

          // Hook to run after computing the indent for a proof command line (like "apply (...)")
          def proof_command_post_hook(indent: Int, curr_line_head: Text.Info[Token]) = {
            // Compute how much this line will move by, and store it so we can use it
            // to indent subsequent lines
            val diff = indent - line_indent(current_line)
            current_command_diff = Some(diff)
          }

          val current_command_span: Option[Text.Info[Command_Span.Span]] = {
            for {
              line_info <- line_head(current_line)
              line_offset = line_info.range.start
              command_span <- Token_Markup.command_span(syntax, buffer, line_offset)
            } yield command_span
          }

          // Return true if the current line is part of a command which is only partially covered
          // by the current selection (in which case it should not be indented)
          def is_partially_selected_command: Boolean = {
            val res = for {
              command_span <- current_command_span
              start_line = buffer.getLineOfOffset(command_span.range.start)
              end_line = buffer.getLineOfOffset(command_span.range.stop)
            } yield (start_line < selection_start_line || end_line > selection_end_line)
            res getOrElse false
          }

          // Indent a line in the middle of a non-apply-style command
          def indent_middle_non_apply_line(curr_line_head: Text.Info[Token]): Int = {
            val tok = curr_line_head.info
            prev_line_command match {
              case None =>
                val extra =
                  (keywords.is_quasi_command(tok), head_is_quasi_command(prev_line)) match {
                    case (true, true) | (false, false) => 0
                    case (true, false) => - indent_extra
                    case (false, true) => indent_extra
                  }
                line_indent(prev_line) + indent_brackets + extra - indent_offset(tok)
              case Some(prev_tok) =>
                indent_structure + indent_brackets + indent_size - indent_offset(tok) -
                indent_offset(prev_tok) - indent_indent(prev_tok)
            }
          }

          // Return true if this is an apply-style command for which we should use a cached diff
          def is_apply_style_command(command: Text.Info[Command_Span.Span]): Boolean =
            command.info.content.headOption.map(
              (head_tok) => keywords.is_command(head_tok, Keyword.prf_script union Keyword.qed)
            ).getOrElse(false)

          // Compute the indent for a line in the middle of another command
          def indent_middle_line(curr_line_head: Text.Info[Token]): Int = {
            (current_command_span, current_command_diff) match {
              case (Some(command_span), Some(command_diff))
                if is_apply_style_command(command_span) =>
                  (line_indent(current_line) + command_diff) max indent_size
              case _ => indent_middle_non_apply_line(curr_line_head)
            }
          }

          // Compute the indent for a line of inner syntax, at present we only handle string quoted
          // syntax
          def indent_inner_syntax(curr_line_head: Option[Text.Info[Token]]): Int = {
            val res = for {
              command_diff <- current_command_diff
              case Text.Info(range, Token(Token.Kind.STRING, s)) <- curr_line_head
              num_leading_spaces = s.indexWhere(!_.isWhitespace) max 0
            } yield (num_leading_spaces + command_diff)
            res getOrElse line_indent(current_line)
          }

          val indent =
            if (Token_Markup.Line_Context.before(buffer, current_line).get_context != Scan.Finished) {
              indent_inner_syntax(line_head(current_line))
            } else if (Token_Markup.Line_Context.after(buffer, current_line).structure.blank) {
              0
            } else if (is_partially_selected_command) {
              line_indent(current_line)
            } else {
              line_head(current_line) match {
                case Some(info) =>
                  val tok = info.info
                  if (tok.is_begin ||
                      keywords.is_before_command(tok) ||
                      keywords.is_command(tok, Keyword.theory)) 0
                  else if (keywords.is_command(tok, Keyword.proof_enclose))
                    indent_structure + script_indent(info) - indent_offset(tok)
                  else if (keywords.is_command(tok, Keyword.proof)) {
                    val indent =
                      (indent_structure + script_indent(info) - indent_offset(tok)) max indent_size
                    proof_command_post_hook(indent, info)
                    indent
                  } else if (tok.is_command) {
                    indent_structure - indent_offset(tok)
                  } else {
                    indent_middle_line(info)
                  }
                case None =>
                  prev_line_command match {
                    case None =>
                      val extra = if (head_is_quasi_command(prev_line)) indent_extra else 0
                      line_indent(prev_line) + indent_brackets + extra
                    case Some(prev_tok) =>
                      indent_structure + indent_brackets + indent_size -
                      indent_offset(prev_tok) - indent_indent(prev_tok)
                  }
              }
            }

          actions.clear()
          actions.add(new IndentAction.AlignOffset(indent max 0))
        case None =>
      }
    }
  }

  def line_content(
    buffer: JEditBuffer,
    keywords: Keyword.Keywords,
    range: Text.Range,
    ctxt: Scan.Line_Context
  ): (List[Token], Scan.Line_Context) = {
    val text = JEdit_Lib.get_text(buffer, range).getOrElse("")
    val (toks, ctxt1) = Token.explode_line(keywords, text, ctxt)
    val toks1 = toks.filterNot(_.is_space)
    (toks1, ctxt1)
  }

  def split_line_content(
    buffer: JEditBuffer,
    keywords: Keyword.Keywords,
    line: Int,
    caret: Int
  ): (List[Token], List[Token]) = {
    val line_range = JEdit_Lib.line_range(buffer, line)
    val ctxt0 = Token_Markup.Line_Context.before(buffer, line).get_context
    val (toks1, ctxt1) = line_content(buffer, keywords, Text.Range(line_range.start, caret), ctxt0)
    val (toks2, _) = line_content(buffer, keywords, Text.Range(caret, line_range.stop), ctxt1)
    (toks1, toks2)
  }


  /* structure matching */

  object Matcher extends StructureMatcher {
    private def find_block(
      open: Token => Boolean,
      close: Token => Boolean,
      reset: Token => Boolean,
      restrict: Token => Boolean,
      it: Iterator[Text.Info[Token]]
    ): Option[(Text.Range, Text.Range)] = {
      val range1 = it.next().range
      it.takeWhile(info => !info.info.is_command || restrict(info.info)).
        scanLeft((range1, 1))(
          { case ((r, d), Text.Info(range, tok)) =>
              if (open(tok)) (range, d + 1)
              else if (close(tok)) (range, d - 1)
              else if (reset(tok)) (range, 0)
              else (r, d) }
        ).collectFirst({ case (range2, 0) => (range1, range2) })
    }

    private def find_pair(text_area: TextArea): Option[(Text.Range, Text.Range)] = {
      val buffer = text_area.getBuffer
      val caret_line = text_area.getCaretLine
      val caret = text_area.getCaretPosition

      Isabelle.buffer_syntax(text_area.getBuffer) match {
        case Some(syntax) =>
          val keywords = syntax.keywords

          val nav = new Navigator(syntax, buffer, false)

          def caret_iterator(): Iterator[Text.Info[Token]] =
            nav.iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          def reverse_caret_iterator(): Iterator[Text.Info[Token]] =
            nav.reverse_iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          nav.iterator(caret_line, 1).find(info => info.range.touches(caret))
          match {
            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.theory_goal) =>
              find_block(
                keywords.is_command(_, Keyword.proof_goal),
                keywords.is_command(_, Keyword.qed),
                keywords.is_command(_, Keyword.qed_global),
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.proof_goal) =>
              find_block(
                keywords.is_command(_, Keyword.proof_goal),
                keywords.is_command(_, Keyword.qed),
                _ => false,
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.qed_global) =>
              reverse_caret_iterator().find(info => keywords.is_command(info.info, Keyword.theory))
              match {
                case Some(Text.Info(range2, tok))
                if keywords.is_command(tok, Keyword.theory_goal) => Some((range1, range2))
                case _ => None
              }

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.qed) =>
              find_block(
                keywords.is_command(_, Keyword.qed),
                t =>
                  keywords.is_command(t, Keyword.proof_goal) ||
                  keywords.is_command(t, Keyword.theory_goal),
                _ => false,
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof) ||
                  keywords.is_command(t, Keyword.theory_goal),
                reverse_caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_begin =>
              find_block(_.is_begin, _.is_end, _ => false, _ => true, caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_end =>
              find_block(_.is_end, _.is_begin, _ => false, _ => true, reverse_caret_iterator())
              match {
                case Some((_, range2)) =>
                  reverse_caret_iterator().
                    dropWhile(info => info.range != range2).
                    dropWhile(info => info.range == range2).
                    find(info => info.info.is_command || info.info.is_begin)
                  match {
                    case Some(Text.Info(range3, tok)) =>
                      if (keywords.is_command(tok, Keyword.theory_block)) Some((range1, range3))
                      else Some((range1, range2))
                    case None => None
                  }
                case None => None
              }

            case _ => None
          }
        case None => None
      }
    }

    def getMatch(text_area: TextArea): StructureMatcher.Match =
      find_pair(text_area) match {
        case Some((_, range)) =>
          val line = text_area.getBuffer.getLineOfOffset(range.start)
          new StructureMatcher.Match(Matcher, line, range.start, line, range.stop)
        case None => null
      }

    def selectMatch(text_area: TextArea): Unit = {
      def get_span(offset: Text.Offset): Option[Text.Range] =
        for {
          syntax <- Isabelle.buffer_syntax(text_area.getBuffer)
          span <- Token_Markup.command_span(syntax, text_area.getBuffer, offset)
        } yield span.range

      find_pair(text_area) match {
        case Some((r1, r2)) =>
          (get_span(r1.start), get_span(r2.start)) match {
            case (Some(range1), Some(range2)) =>
              val start = range1.start min range2.start
              val stop = range1.stop max range2.stop

              text_area.moveCaretPosition(stop, false)
              if (!text_area.isMultipleSelectionEnabled) text_area.selectNone
              text_area.addToSelection(new Selection.Range(start, stop))
            case _ =>
          }
        case None =>
      }
    }
  }
}
