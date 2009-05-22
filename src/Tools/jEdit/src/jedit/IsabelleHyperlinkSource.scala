/*
 * IsabelleHyperlinkSource.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package isabelle.jedit
import gatchan.jedit.hyperlinks.Hyperlink
import gatchan.jedit.hyperlinks.HyperlinkSource
import gatchan.jedit.hyperlinks.AbstractHyperlink

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.TextUtilities

import isabelle.prover.RefInfo

class InternalHyperlink(start: Int, end: Int, line: Int, ref_offset: Int)
  extends AbstractHyperlink(start, end, line, "tooltip")
{
  override def click(view: View) = {
    view.getTextArea.moveCaretPosition(ref_offset)
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
      val document = prover.get.document
      val theory_view = theory_view_opt.get
      val offset = theory_view.from_current(document, original_offset)
      val cmd = document.find_command_at(offset)
      if (cmd != null) {
        val ref_o = cmd.ref_at(offset - cmd.start(document))
        if (!ref_o.isDefined) null
        else {
          val ref = ref_o.get
          val start = theory_view.to_current(document, ref.abs_start(document))
          val line = buffer.getLineOfOffset(start)
          val end = theory_view.to_current(document, ref.abs_stop(document))
          ref.info match {
            case RefInfo(Some(file), Some(ref_line), _, _) =>
              null
            case RefInfo(_, _, Some(id), Some(offset)) =>
              prover.get.command(id) match {
                case Some(ref_cmd) =>
                  new InternalHyperlink(start, end, line,
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
