/*  Title:      Tools/jEdit/src/jedit/isabelle_hyperlinks.scala
    Author:     Fabian Immler, TU Munich

Hyperlink setup for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import java.io.File

import gatchan.jedit.hyperlinks.{Hyperlink, HyperlinkSource, AbstractHyperlink}

import org.gjt.sp.jedit.{View, jEdit, Buffer, TextUtilities}


private class Internal_Hyperlink(start: Int, end: Int, line: Int, ref_offset: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) {
    view.getTextArea.moveCaretPosition(ref_offset)
  }
}

class External_Hyperlink(start: Int, end: Int, line: Int, ref_file: String, ref_line: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) = {
    Isabelle.system.source_file(ref_file) match {
      case None =>
        Library.error_dialog(view, "File not found", "Could not find source file " + ref_file)
      case Some(file) =>
        jEdit.openFiles(view, file.getParent, Array(file.getName, "+line:" + ref_line))
    }
  }
}

class Isabelle_Hyperlinks extends HyperlinkSource
{
  def getHyperlink(buffer: Buffer, buffer_offset: Int): Hyperlink =
  {
    Swing_Thread.assert()
    Isabelle.buffer_lock(buffer) {
      Document_Model(buffer) match {
        case Some(model) =>
          val snapshot = model.snapshot()
          val markup =
            snapshot.select_markup(Text.Range(buffer_offset, buffer_offset + 1)) {
              // FIXME Isar_Document.Hyperlink extractor
              case Text.Info(info_range, XML.Elem(Markup(Markup.ML_REF, _),
                  List(XML.Elem(Markup(Markup.ML_DEF, props), _)))) =>
                val Text.Range(begin, end) = info_range
                val line = buffer.getLineOfOffset(begin)
                (Position.File.unapply(props), Position.Line.unapply(props)) match {
                  case (Some(ref_file), Some(ref_line)) =>
                    new External_Hyperlink(begin, end, line, ref_file, ref_line)
                  case _ =>
                    (props, props) match {
                      case (Position.Id(ref_id), Position.Offset(ref_offset)) =>
                        snapshot.lookup_command(ref_id) match {
                          case Some(ref_cmd) =>
                            snapshot.node.command_start(ref_cmd) match {
                              case Some(ref_cmd_start) =>
                                new Internal_Hyperlink(begin, end, line,
                                  snapshot.convert(ref_cmd_start + ref_cmd.decode(ref_offset)))
                              case None => null
                            }
                          case None => null
                        }
                      case _ => null
                    }
                }
            } { null }
          if (markup.hasNext) markup.next.info else null

        case None => null
      }
    }
  }
}
