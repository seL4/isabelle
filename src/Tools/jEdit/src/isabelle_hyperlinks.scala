/*  Title:      Tools/jEdit/src/isabelle_hyperlinks.scala
    Author:     Fabian Immler, TU Munich

Hyperlink setup for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import java.io.File

import gatchan.jedit.hyperlinks.{Hyperlink, HyperlinkSource, AbstractHyperlink}

import org.gjt.sp.jedit.{View, jEdit, Buffer, TextUtilities}


private class Internal_Hyperlink(name: String, start: Int, end: Int, line: Int, offset: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View)
  {
    val text_area = view.getTextArea
    if (Isabelle.buffer_name(view.getBuffer) == name)
      text_area.moveCaretPosition(offset)
    else
      Isabelle.jedit_buffer(name) match {
        case Some(buffer) =>
          view.setBuffer(buffer)
          text_area.moveCaretPosition(offset)
        case None =>
      }
  }
}

class External_Hyperlink(start: Int, end: Int, line: Int, def_file: String, def_line: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) = {
    Isabelle_System.source_file(Path.explode(def_file)) match {
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
            snapshot.select_markup(Text.Range(buffer_offset, buffer_offset + 1))(
              Markup_Tree.Select[Hyperlink](
                {
                  // FIXME Protocol.Hyperlink extractor
                  case Text.Info(info_range,
                      XML.Elem(Markup(Isabelle_Markup.ENTITY, props), _))
                    if (props.find(
                      { case (Markup.KIND, Isabelle_Markup.ML_OPEN) => true
                        case (Markup.KIND, Isabelle_Markup.ML_STRUCT) => true
                        case _ => false }).isEmpty) =>
                    val Text.Range(begin, end) = info_range
                    val line = buffer.getLineOfOffset(begin)
                    (Position.File.unapply(props), Position.Line.unapply(props)) match {
                      case (Some(def_file), Some(def_line)) =>
                        new External_Hyperlink(begin, end, line, def_file, def_line)
                      case _ if !snapshot.is_outdated =>
                        (props, props) match {
                          case (Position.Id(def_id), Position.Offset(def_offset)) =>
                            snapshot.state.find_command(snapshot.version, def_id) match {
                              case Some((def_node, def_cmd)) =>
                                def_node.command_start(def_cmd) match {
                                  case Some(def_cmd_start) =>
                                    new Internal_Hyperlink(def_cmd.node_name.node, begin, end, line,
                                      def_cmd_start + def_cmd.decode(def_offset))
                                  case None => null
                                }
                              case None => null
                            }
                          case _ => null
                        }
                      case _ => null
                    }
                },
                Some(Set(Isabelle_Markup.ENTITY))))
          markup match {
            case Text.Info(_, Some(link)) #:: _ => link
            case _ => null
          }
        case None => null
      }
    }
  }
}
