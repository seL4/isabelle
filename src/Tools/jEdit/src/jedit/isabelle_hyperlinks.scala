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
      case None => System.err.println("Could not find source file " + ref_file)  // FIXME ??
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
    Document_Model(buffer) match {
      case Some(model) =>
        val snapshot = model.snapshot()
        val offset = snapshot.revert(buffer_offset)
        snapshot.node.command_at(offset) match {
          case Some((command, command_start)) =>
            val root = Text.Info[Hyperlink]((Text.Range(offset) - command_start), null)
            (snapshot.state(command).markup.select(root) {
              case Text.Info(info_range, XML.Elem(Markup(Markup.ML_REF, _),
                  List(XML.Elem(Markup(Markup.ML_DEF, props), _)))) =>
                val Text.Range(begin, end) = snapshot.convert(info_range + command_start)
                val line = buffer.getLineOfOffset(begin)

                (Position.get_file(props), Position.get_line(props)) match {
                  case (Some(ref_file), Some(ref_line)) =>
                    new External_Hyperlink(begin, end, line, ref_file, ref_line)
                  case _ =>
                    (Position.get_id(props), Position.get_offset(props)) match {
                      case (Some(ref_id), Some(ref_offset)) =>
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
            }).head.info
          case None => null
        }
      case None => null
    }
  }
}
