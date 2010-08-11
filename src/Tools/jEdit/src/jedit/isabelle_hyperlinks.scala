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
  def getHyperlink(buffer: Buffer, original_offset: Int): Hyperlink =
  {
    Swing_Thread.assert()
    Document_Model(buffer) match {
      case Some(model) =>
        val snapshot = model.snapshot()
        val offset = snapshot.revert(original_offset)
        snapshot.node.command_at(offset) match {
          case Some((command, command_start)) =>
            snapshot.state(command).ref_at(offset - command_start) match {
              case Some(ref) =>
                val begin = snapshot.convert(command_start + ref.start)
                val line = buffer.getLineOfOffset(begin)
                val end = snapshot.convert(command_start + ref.stop)
                ref.info match {
                  case Command.RefInfo(Some(ref_file), Some(ref_line), _, _) =>
                    new External_Hyperlink(begin, end, line, ref_file, ref_line)
                  case Command.RefInfo(_, _, Some(id), Some(offset)) =>
                    Isabelle.session.lookup_entity(id) match {
                      case Some(ref_cmd: Command) =>
                        snapshot.node.command_start(ref_cmd) match {
                          case Some(ref_cmd_start) =>
                            new Internal_Hyperlink(begin, end, line,
                              snapshot.convert(ref_cmd_start + offset - 1))
                          case None => null // FIXME external ref
                        }
                      case _ => null
                    }
                  case _ => null
                }
              case None => null
            }
          case None => null
        }
      case None => null
    }
  }
}
