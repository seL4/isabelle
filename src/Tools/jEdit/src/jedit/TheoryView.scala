/*
 * jEdit text area as document text source
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit

import isabelle.utils.EventSource

import isabelle.proofdocument.Text

import isabelle.prover.{ Prover, Command, CommandChangeInfo }
import isabelle.prover.Command.Phase

import javax.swing.Timer
import javax.swing.event.{ CaretListener, CaretEvent }
import java.awt.Graphics2D
import java.awt.event.{ ActionEvent, ActionListener }
import java.awt.Color;

import org.gjt.sp.jedit.buffer.{ BufferListener, JEditBuffer }
import org.gjt.sp.jedit.textarea.{ JEditTextArea, TextAreaExtension, TextAreaPainter }
import org.gjt.sp.jedit.syntax.SyntaxStyle

object TheoryView {

  def chooseColor(state : Command) : Color = {
    if (state == null)
      Color.red
    else
      state.phase match {
        case Phase.UNPROCESSED => new Color(255, 255, 192)
        case Phase.FINISHED => new Color(192, 255, 192)
        case Phase.FAILED => new Color(255, 192, 192)
        case _ => Color.red
      }
  }

  def chooseColor(status : String) : Color = {
    //TODO: as properties!
    status match {
      //outer
      case "ident" | "command" | "keyword" => Color.blue
      case "verbatim"=> Color.green
      case "comment" => Color.gray
      case "control" => Color.white
      case "malformed" => Color.red
      case "string" | "altstring" => Color.orange
      //logical
      case "tclass" | "tycon" | "fixed_decl"  | "fixed"
        | "const_decl" | "const" | "fact_decl" | "fact"
        |"dynamic_fact" |"local_fact_decl" | "local_fact"
        => new Color(255, 0, 255)
      //inner syntax
      case "tfree" | "free" => Color.blue
      case "tvar" | "skolem" | "bound" | "var" => Color.green
      case "num" | "xnum" | "xstr" | "literal" | "inner_comment" => new Color(255, 128, 128)
      case "sort" | "typ" | "term" | "prop" | "attribute" | "method"  => Color.yellow
        // embedded source
      case "doc_source"  | "ML_source" | "ML_antic" | "doc_antiq" | "antiq"
        => new Color(0, 192, 0)
      case _ => Color.white
    }
  }
}

class TheoryView (text_area : JEditTextArea)
    extends TextAreaExtension with Text with BufferListener {
  import TheoryView._
  import Text.Changed

  var col : Changed = null

  val buffer = text_area.getBuffer
  buffer.addBufferListener(this)
  
  val colTimer = new Timer(300, new ActionListener() {
    override def actionPerformed(e : ActionEvent) { commit() }
  })
  
  val changesSource = new EventSource[Changed]
  val phase_overview = new PhaseOverviewPanel(Plugin.prover(buffer))

    val repaint_delay = new isabelle.utils.Delay(100, () => repaintAll())
    Plugin.prover(buffer).commandInfo.add(_ => repaint_delay.delay_or_ignore())
    Plugin.self.font_changed.add(font => updateFont())

    colTimer.stop
    colTimer.setRepeats(true)

  def activate() {
    text_area.addCaretListener(selectedStateController)
    phase_overview.textarea = text_area
    text_area.addLeftOfScrollBar(phase_overview)
    val painter = text_area.getPainter()
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, this)
    updateFont()
  }
  
  private def updateFont() {
    if (text_area != null) {
      val painter = text_area.getPainter()
      if (Plugin.self.font != null) {
        painter.setStyles(painter.getStyles.map(style =>
          new SyntaxStyle(style.getForegroundColor, 
                          style.getBackgroundColor, 
                          Plugin.self.font)
        ))
        painter.setFont(Plugin.self.font)
        repaintAll()
      }
    }
  }
  
  def deactivate() {
    text_area.getPainter().removeExtension(this)
    text_area.removeCaretListener(selectedStateController)
    text_area.removeLeftOfScrollBar(phase_overview)
  }
  
  val selectedStateController = new CaretListener() {
    override def caretUpdate(e : CaretEvent) {
      val cmd = Plugin.prover(buffer).document.getNextCommandContaining(e.getDot())
      if (cmd != null && cmd.start <= e.getDot() && 
            Plugin.prover_setup(buffer).selectedState != cmd)
        Plugin.prover_setup(buffer).selectedState = cmd
    }
  }

  private def fromCurrent(pos : Int) =
    if (col != null && col.start <= pos)
      if (pos < col.start + col.added) col.start
      else pos - col.added + col.removed
    else pos
  
  private def toCurrent(pos : Int) = 
    if (col != null && col.start <= pos)
      if (pos < col.start + col.removed) col.start
      else pos + col.added - col.removed
    else pos
  
  def repaint(cmd : Command)
  {
    val ph = cmd.phase
    if (text_area != null && ph != Phase.REMOVE && ph != Phase.REMOVED) {
      var start = text_area.getLineOfOffset(toCurrent(cmd.start))
      var stop = text_area.getLineOfOffset(toCurrent(cmd.stop) - 1)
      text_area.invalidateLineRange(start, stop)
      
      if (Plugin.prover_setup(buffer).selectedState == cmd)
        Plugin.prover_setup(buffer).selectedState = cmd // update State view
    }
  }
  
  def repaintAll()
  {
    if (text_area != null)
      text_area.invalidateLineRange(text_area.getFirstPhysicalLine,
                                   text_area.getLastPhysicalLine)
  }

  def encolor(gfx : Graphics2D, y : Int, height : Int, begin : Int, finish : Int, color : Color, fill : Boolean){
      val fm = text_area.getPainter.getFontMetrics
      val startP = text_area.offsetToXY(begin)
      val stopP = if (finish < buffer.getLength()) text_area.offsetToXY(finish)
                  else { var p = text_area.offsetToXY(finish - 1)
                         p.x = p.x + fm.charWidth(' ')
                         p }
			
      if (startP != null && stopP != null) {
        gfx.setColor(color)
        if(fill){gfx.fillRect(startP.x, y, stopP.x - startP.x, height)}
        else {gfx.drawRect(startP.x, y, stopP.x - startP.x, height)}
      }
  }

  override def paintValidLine(gfx : Graphics2D, screenLine : Int,
                              pl : Int, start : Int, end : Int, y : Int)
  {	
    val fm = text_area.getPainter.getFontMetrics
    var savedColor = gfx.getColor
    var e = Plugin.prover(buffer).document.getNextCommandContaining(fromCurrent(start))

    //Encolor Phase
    while (e != null && toCurrent(e.start) < end) {
      val begin =  start max toCurrent(e.start)
      val finish = end - 1 min  toCurrent(e.stop)
      encolor(gfx, y, fm.getHeight, begin, finish, chooseColor(e), true)
      // paint details of command
      for(node <- e.root_node.dfs){
        val begin = toCurrent(node.start + e.start)
        val finish = toCurrent(node.end + e.start)
        if(finish > start && begin < end)
        encolor(gfx, y + fm.getHeight - 4, 2, begin max start, finish min end, chooseColor(node.short), true)
      }
      e = e.next
    }

    gfx.setColor(savedColor)
  }
	
  def content(start : Int, stop : Int) = buffer.getText(start, stop - start)
  override def length = buffer.getLength

  def changes = changesSource

  private def commit() {
    if (col != null)
      changes.fire(col)
    col = null
    if (colTimer.isRunning())
      colTimer.stop()
  }	
	
  private def delayCommit() {
    if (colTimer.isRunning())
      colTimer.restart()
    else
      colTimer.start()
  }
	
  override def contentInserted(buffer : JEditBuffer, startLine : Int, 
                               offset : Int, numLines : Int, length : Int) { }
  override def contentRemoved(buffer : JEditBuffer, startLine : Int, 
                              offset : Int, numLines : Int, length : Int) { }

  override def preContentInserted(buffer : JEditBuffer, startLine : Int,
			offset : Int, numLines : Int, length : Int) {
    if (col == null)
      col = new Changed(offset, length, 0)
    else if (col.start <= offset && offset <= col.start + col.added) 
      col = new Changed(col.start, col.added + length, col.removed)
    else { 
      commit()
      col = new Changed(offset, length, 0) 
    }
    delayCommit()
  }	
  
  override def preContentRemoved(buffer : JEditBuffer, startLine : Int,
			start : Int, numLines : Int, removed : Int) {
    if (col == null)
      col = new Changed(start, 0, removed)
    else if (col.start > start + removed || start > col.start + col.added) { 
      commit()
      col = new Changed(start, 0, removed) 
    }
    else {
      val offset = start - col.start
      val diff = col.added - removed
      val (added, addRemoved) = 
        if (diff < offset) 
          (offset max 0, diff - (offset max 0))
        else 
          (diff - (offset min 0), offset min 0)
      
      col = new Changed(start min col.start, added, col.removed - addRemoved) 
    }
    delayCommit()
  }

  override def bufferLoaded(buffer : JEditBuffer) { }
  override def foldHandlerChanged(buffer : JEditBuffer) { }
  override def foldLevelChanged(buffer : JEditBuffer, startLine : Int, 
                                endLine : Int) = { }
  override def transactionComplete(buffer : JEditBuffer) = { } 
}