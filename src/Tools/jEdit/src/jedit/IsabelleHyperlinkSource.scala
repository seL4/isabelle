/*
 * Hyperlink setup for Isabelle proof documents
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import java.io.File

import gatchan.jedit.hyperlinks.Hyperlink
import gatchan.jedit.hyperlinks.HyperlinkSource
import gatchan.jedit.hyperlinks.AbstractHyperlink

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.TextUtilities

import isabelle.prover.RefInfo


class InternalHyperlink(start: Int, end: Int, line: Int, ref_offset: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) {
    view.getTextArea.moveCaretPosition(ref_offset)
  }
}

class ExternalHyperlink(start: Int, end: Int, line: Int, ref_file: String, ref_line: Int)
  extends AbstractHyperlink(start, end, line, "")
{
  override def click(view: View) = {
    Isabelle.system.source_file(ref_file) match {
      case None => System.err.println("Could not find source file " + ref_file)
      case Some(file) =>
        jEdit.openFiles(view, file.getParent, Array(file.getName, "+line:" + ref_line))
    }
  }
}

class IsabelleHyperlinkSource extends HyperlinkSource
{
	def getHyperlink(buffer: Buffer, original_offset: Int): Hyperlink = {
    val prover = Isabelle.prover_setup(buffer).map(_.prover)
    val theory_view_opt = Isabelle.prover_setup(buffer).map(_.theory_view)
    if (!prover.isDefined || !theory_view_opt.isDefined) null
    else if (prover.get == null || theory_view_opt.get == null) null
    else {
      val theory_view = theory_view_opt.get
      val document = theory_view.current_document()
      val offset = theory_view.from_current(document, original_offset)
      val command = document.find_command_at(offset)
      if (command != null) {
        val ref_o = command.ref_at(document, offset - command.start(document))
        if (!ref_o.isDefined) null
        else {
          val ref = ref_o.get
          val command_start = command.start(document)
          val begin = theory_view.to_current(document, command_start + ref.start)
          val line = buffer.getLineOfOffset(begin)
          val end = theory_view.to_current(document, command_start + ref.stop)
          ref.info match {
            case RefInfo(Some(ref_file), Some(ref_line), _, _) =>
              new ExternalHyperlink(begin, end, line, ref_file, ref_line)
            case RefInfo(_, _, Some(id), Some(offset)) =>
              prover.get.command(id) match {
                case Some(ref_cmd) =>
                  new InternalHyperlink(begin, end, line,
                    theory_view.to_current(document, ref_cmd.start(document) + offset - 1))
                case _ => null
              }
            case _ => null
          }
        }
      } else null
    }
  }
}
