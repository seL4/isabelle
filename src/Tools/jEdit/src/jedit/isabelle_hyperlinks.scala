/*  Title:      Tools/jEdit/src/jedit/isabelle_hyperlinks.scala
    Author:     Fabian Immler, TU Munich

Hyperlink setup for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import java.io.File

import gatchan.jedit.hyperlinks.{Hyperlink, HyperlinkSource, AbstractHyperlink}

import org.gjt.sp.jedit.{View, jEdit, Buffer, TextUtilities}


private class Internal_Hyperlink(start: Int, end: Int, line: Int, def_offset: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) {
    view.getTextArea.moveCaretPosition(def_offset)
  }
}

class External_Hyperlink(start: Int, end: Int, line: Int, def_file: String, def_line: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) = {
    Isabelle.system.source_file(def_file) match {
      case None =>
        Library.error_dialog(view, "File not found", "Could not find source file " + def_file)
      case Some(file) =>
        jEdit.openFiles(view, file.getParent, Array(file.getName, "+line:" + def_line))
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
              case Text.Info(info_range,
                  XML.Elem(Markup(Markup.ENTITY, props), _))
                if (props.find(
                  { case (Markup.KIND, Markup.ML_OPEN) => true
                    case (Markup.KIND, Markup.ML_STRUCT) => true
                    case _ => false }).isEmpty) =>
                val Text.Range(begin, end) = info_range
                val line = buffer.getLineOfOffset(begin)
                (Position.File.unapply(props), Position.Line.unapply(props)) match {
                  case (Some(def_file), Some(def_line)) =>
                    new External_Hyperlink(begin, end, line, def_file, def_line)
                  case _ =>
                    (props, props) match {
                      case (Position.Id(def_id), Position.Offset(def_offset)) =>
                        snapshot.lookup_command(def_id) match {
                          case Some(def_cmd) =>
                            snapshot.node.command_start(def_cmd) match {
                              case Some(def_cmd_start) =>
                                new Internal_Hyperlink(begin, end, line,
                                  snapshot.convert(def_cmd_start + def_cmd.decode(def_offset)))
                              case None => null
                            }
                          case None => null
                        }
                      case _ => null
                    }
                }
            }
          markup match {
            case Text.Info(_, Some(link)) #:: _ => link
            case _ => null
          }
        case None => null
      }
    }
  }
}
