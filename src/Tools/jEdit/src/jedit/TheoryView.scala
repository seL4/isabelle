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
import org.gjt.sp.jedit.textarea.{ TextArea, TextAreaExtension, TextAreaPainter }
import org.gjt.sp.jedit.syntax.SyntaxStyle

object TheoryView {
  val ISABELLE_THEORY_PROPERTY = "de.tum.in.isabelle.jedit.Theory";

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
      case "ident" => new Color(192, 192, 255)
      case "literal" => new Color(192, 255, 255)
      case "fixed_decl" => new Color(192, 192, 192)
      case "prop" => new Color(255, 192 ,255)
      case "typ" => new Color(192, 192, 128)
      case "term" => new Color(192, 128, 192)
      case "method" => new Color(128, 192, 192)
      case "doc_source" => new Color(128, 128, 192)
      case "ML_source" => new Color(128, 192, 128)
      case "local_fact_decl" => new Color(192, 128, 128)
      case _ => Color.red
    }
  }
  def withView(view : TextArea, f : (TheoryView) => Unit) {
    if (view != null && view.getBuffer() != null)
      view.getBuffer().getProperty(ISABELLE_THEORY_PROPERTY) match {
        case null => null
        case view: TheoryView => f(view)
        case _ => null
      }
  }
	
  def activateTextArea(textArea : TextArea) {
    withView(textArea, _.activate(textArea))
  }	
	
  def deactivateTextArea(textArea : TextArea) {
    withView(textArea, _.deactivate(textArea))
  }
}

class TheoryView(prover : Prover, buffer : JEditBuffer) 
    extends TextAreaExtension with Text with BufferListener {
  import TheoryView._
  import Text.Changed
  
  var textArea : TextArea = null;
  var col : Changed = null;
  
  val colTimer = new Timer(300, new ActionListener() {
    override def actionPerformed(e : ActionEvent) { commit() }
  })
  
  val changesSource = new EventSource[Changed]

  {
    buffer.addBufferListener(this)
    buffer.setProperty(ISABELLE_THEORY_PROPERTY, this)
    
    prover.commandInfo.add(e => repaint(e.command))
    prover.commandInfo.add(e => repaintAll())
	
    Plugin.plugin.viewFontChanged.add(font => updateFont())
    
    colTimer.stop
    colTimer.setRepeats(true)
  }

  def activate(area : TextArea) {
    textArea = area
    textArea.addCaretListener(selectedStateController)
    
    val painter = textArea.getPainter()
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, this)
    updateFont()
  }
  
  private def updateFont() {
    if (textArea != null) {
      val painter = textArea.getPainter()
      if (Plugin.plugin.viewFont != null) {
        painter.setStyles(painter.getStyles().map(style =>
          new SyntaxStyle(style.getForegroundColor, 
                          style.getBackgroundColor, 
                          Plugin.plugin.viewFont)
        ))
        painter.setFont(Plugin.plugin.viewFont)
        repaintAll()
      }
    }
  }
  
  def deactivate(area : TextArea) {
    textArea.getPainter().removeExtension(this)
    textArea.removeCaretListener(selectedStateController)
    textArea = null
  }
  
  val selectedStateController = new CaretListener() {
    override def caretUpdate(e : CaretEvent) {
      val cmd = prover.document.getNextCommandContaining(e.getDot())
      if (cmd != null && cmd.start <= e.getDot() && 
            Plugin.plugin.selectedState != cmd)
        Plugin.plugin.selectedState = cmd
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
    var ph = cmd.phase
    if (textArea != null && ph != Phase.REMOVE && ph != Phase.REMOVED) {
      var start = textArea.getLineOfOffset(toCurrent(cmd.start))
      var stop = textArea.getLineOfOffset(toCurrent(cmd.stop) - 1)
      textArea.invalidateLineRange(start, stop)
      
      if (Plugin.plugin.selectedState == cmd)
        Plugin.plugin.selectedState = cmd // update State view 
    }
  }
  
  def repaintAll()
  {
    if (textArea != null)
      textArea.invalidateLineRange(textArea.getFirstPhysicalLine, 
                                   textArea.getLastPhysicalLine)
  }

  def encolor(gfx : Graphics2D, y : Int, height : Int, begin : Int, finish : Int, color : Color){
      val fm = textArea.getPainter.getFontMetrics
      val startP = textArea.offsetToXY(begin)
      val stopP = if (finish < buffer.getLength()) textArea.offsetToXY(finish)
                  else { var p = textArea.offsetToXY(finish - 1)
                         p.x = p.x + fm.charWidth(' ')
                         p }
			
      if (startP != null && stopP != null) {
        gfx.setColor(color)
        gfx.fillRect(startP.x, y, stopP.x - startP.x, height)
      }
  }

  override def paintValidLine(gfx : Graphics2D, screenLine : Int,
                              pl : Int, start : Int, end : Int, y : Int)
  {	
    val fm = textArea.getPainter.getFontMetrics
    var savedColor = gfx.getColor
    var e = prover.document.getNextCommandContaining(fromCurrent(start))

    //Encolor Phase
    while (e != null && toCurrent(e.start) < end) {
      val begin = Math.max(start, toCurrent(e.start))
      val finish = Math.min(end - 1, toCurrent(e.stop))
      encolor(gfx, y, fm.getHeight, begin, finish, chooseColor(e))
      // paint details of command
      var dy = 0
      for(status <- e.statuses){
        dy += 1
        val begin = Math.max(start, toCurrent(status.start + e.start))
        val finish = Math.min(end - 1, toCurrent(status.stop + e.start))
        encolor(gfx, y + dy, fm.getHeight - dy, begin, finish, chooseColor(status.kind))
      }
      e = e.next
    }

    gfx.setColor(savedColor)
  }
	
  def content(start : Int, stop : Int) = buffer.getText(start, stop - start)
  def length = buffer.getLength()

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