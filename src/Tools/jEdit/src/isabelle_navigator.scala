/*  Title:      Tools/jEdit/src/isabelle_navigator.scala
    Author:     Makarius

Navigate history of notable source positions.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.Selection


object Isabelle_Navigator {
  /* global state -- owned by GUI thread */

  private var _passive = false
  private var _navigators = Map.empty[View, Isabelle_Navigator_View]

  def is_active(): Boolean = GUI_Thread.require { !_passive }

  def passive[A](body: => A): A = GUI_Thread.require {
    val b = _passive
    _passive = true
    try (body) finally { _passive = b }
  }

  val none: Isabelle_Navigator = new Isabelle_Navigator

  def get(view: View): Isabelle_Navigator = GUI_Thread.require {
    _navigators.getOrElse(view, none)
  }

  def init(view: View): Unit = GUI_Thread.require {
    if (view != null) _navigators = _navigators + (view -> new Isabelle_Navigator_View(view))
  }

  def exit(view: View): Unit = GUI_Thread.require {
    if (view != null) _navigators = _navigators - view
  }

  def add_listener(buffers: List[Buffer]): Unit = GUI_Thread.require {
    _navigators.valuesIterator.foreach(_.add_listener(buffers))
  }

  def del_listener(buffers: List[Buffer]): Unit = GUI_Thread.require {
    _navigators.valuesIterator.foreach(_.del_listener(buffers))
  }


  /* recode symbols */

  def recode_buffer(buffer: JEditBuffer, unicode_symbols: Boolean): Unit = GUI_Thread.require {
    if (!buffer.isPerformingIO) {
      buffer.writeLock()
      try {
        val text0 = buffer.getText(0, buffer.getLength)
        val text1 = Symbol.output(unicode_symbols, text0)

        val encoding0 = buffer.getStringProperty(JEditBuffer.ENCODING)
        val encoding1 = if (unicode_symbols) Isabelle_Encoding.NAME else UTF8.charset.name

        if (text0 != text1 || encoding0 != encoding1) {
          passive {
            if (text0 != text1) {
              val text_areas = JEdit_Lib.jedit_text_areas(buffer).toList
              val carets = text_areas.map(_.getCaretPosition)
              val selections = text_areas.map(JEdit_Lib.selection_ranges) // approximative for Rect

              for (text_area <- text_areas) {
                text_area.setCaretPosition(0)
                text_area.selectNone()
              }

              JEdit_Lib.undo_manager(buffer).clear()

              val dirty = buffer.isDirty
              JEdit_Lib.set_text(buffer, List(text1))
              buffer.setDirty(dirty)

              val index0 = Symbol.Index(text0)
              val index1 = Symbol.Index(text1)
              def recode_offset(offset: Int): Int = index1.decode(index0.encode(offset))
              def recode_range(range: Text.Range): Text.Range = index1.decode(index0.encode(range))

              for ((text_area, caret) <- text_areas zip carets) {
                text_area.setCaretPosition(recode_offset(caret))
              }
              for ((text_area, selection) <- text_areas zip selections) {
                text_area.setSelection(
                  selection.iterator.map(recode_range).map(range =>
                    new Selection.Range(range.start, range.stop)).toArray[Selection])
              }

              for (navigator <- _navigators.valuesIterator) {
                navigator.adjust(JEdit_Lib.buffer_name(buffer), recode_offset)
              }
            }

            if (encoding0 != encoding1) {
              buffer.setStringProperty(JEditBuffer.ENCODING, encoding1)
            }

            buffer.propertiesChanged()
          }
        }
      }
      finally { buffer.writeUnlock() }
    }
  }


  /* source position */

  object Pos {
    val none: Pos = new Pos(Document_ID.none, "", 0)

    def make(name: String, offset: Int): Pos =
      if (name == null || name.isEmpty) none
      else new Pos(Document_ID.make(), name, offset)

    def apply(editor_context: JEdit_Editor.Context): Pos =
      editor_context.proper_buffer match {
        case Some(buffer) if buffer.isLoaded && !buffer.isUntitled =>
          make(editor_context.buffer_name, editor_context.caret_offset)
        case _ => none
      }
  }

  final class Pos private(
    val id: Document_ID.Generic,
    val name: String,
    val offset: Int
  ) {
    def defined: Boolean = id != Document_ID.none

    override def toString: String =
      if (defined) "(offset " + offset + " of " + quote(name) + ")" else "Pos.none"

    override def hashCode: Int = id.hashCode
    override def equals(other: Any): Boolean =
      other match {
        case that: Pos => id == that.id
        case _ => false
      }

    def equiv(that: Pos): Boolean = name == that.name && offset == that.offset

    def adjust(a: String, f: Int => Int): Pos =
      if (name == a) {
        val offset1 = f(offset)
        if (offset == offset1) this else Pos.make(name, offset1)
      }
      else this
  }


  /* history */

  object History {
    val limit: Int = 500
    val empty: History = new History(Linear_Set.empty)
  }

  final class History private(hist: Linear_Set[Pos]) {
    override def toString: String =
      size match {
        case 0 => "History.empty"
        case n => "History(" + n + ")"
      }
    def is_empty: Boolean = hist.isEmpty
    def size: Int = hist.size
    def iterator: Iterator[Pos] = hist.iterator

    def top: Pos = if (hist.isEmpty) Pos.none else hist.head
    def pop: History = if (hist.isEmpty) this else new History(hist.delete_after(None))

    def push(pos: Pos): History =
      if (!pos.defined || pos.equiv(top)) this
      else {
        val hist1 =
          if (hist.size < History.limit) hist
          else hist.delete_after(hist.prev(hist.last))
        new History(hist1.insert_after(None, pos))
      }

    def adjust(name: String, f: Int => Int): History =
      new History(
        hist.foldLeft(hist) {
          case (h, pos) =>
            val prev = h.prev(pos)
            val pos0 = prev.getOrElse(Pos.none)
            val pos1 = pos.adjust(name, f)
            if (pos1.equiv(pos0)) h.delete_after(prev)
            else if (pos1.equiv(pos)) h
            else h.delete_after(prev).insert_after(prev, pos1)
        }
      )
  }


  /* target position */

  sealed case class Target(line: Int = -1, offset: Text.Offset = -1) {
    def caret_offset(buffer: Buffer): Option[Text.Offset] =
      if (buffer != null && (line >= 0 || offset >= 0)) {
        val n = buffer.getLength
        val line_offset =
          if (line < 0) 0
          else if (line >= buffer.getLineCount) n
          else buffer.getLineStartOffset(line)
        Some((line_offset + offset.max(0)) min n)
      }
      else None
  }
}

class Isabelle_Navigator {
  override def toString: String = "Isabelle_Navigator.none"
  def current: Isabelle_Navigator.Pos = Isabelle_Navigator.Pos.none
  def recurrent: Isabelle_Navigator.Pos = Isabelle_Navigator.Pos.none
  def del_listener(buffers: List[Buffer]): Unit = ()
  def add_listener(buffers: List[Buffer]): Unit = ()
  def record(pos: Isabelle_Navigator.Pos): Unit = ()
  def goto_buffer(buffer: Buffer, target: Isabelle_Navigator.Target, focus: Boolean = false): Unit = ()
  def open_file(name: String, target: Isabelle_Navigator.Target): Unit = ()
  def goto(pos: Isabelle_Navigator.Pos): Unit = ()
  def backward(): Unit = ()
  def forward(): Unit = ()
}

class Isabelle_Navigator_View(view: View) extends Isabelle_Navigator {
  require(view != null)

  private val editor_context = JEdit_Editor.Context(view)

  // owned by GUI thread
  private var _backward = Isabelle_Navigator.History.empty
  private var _forward = Isabelle_Navigator.History.empty
  private var _goto_target = Map.empty[String, Isabelle_Navigator.Target]

  override def current: Isabelle_Navigator.Pos = _backward.top
  override def recurrent: Isabelle_Navigator.Pos = _forward.top

  override def toString: String = {
    val size = _backward.size + _forward.size
    "Isabelle_Navigator(" + if_proper(size > 0, size.toString) + ")"
  }

  def adjust(name: String, f: Int => Int): Unit = GUI_Thread.require {
    _backward = _backward.adjust(name, f)
    _forward = _forward.adjust(name, f)
  }

  private def goto_target(name: String, target: Isabelle_Navigator.Target): Unit =
    GUI_Thread.require { _goto_target = _goto_target + (name -> target) }

  private def init_caret(buffer: Buffer): Unit = GUI_Thread.require {
    val name = JEdit_Lib.buffer_name(buffer)
    for (target <- _goto_target.get(name)) {
      _goto_target = _goto_target - name
      for (caret <- target.caret_offset(buffer)) {
        val text_areas = JEdit_Lib.jedit_text_areas(buffer).toList
        for (text_area <- text_areas) text_area.setCaretPosition(caret)
        if (text_areas.isEmpty) buffer.unsetProperty(Buffer.SCROLL_VERT)
        buffer.setIntegerProperty(Buffer.CARET, caret)
        buffer.setBooleanProperty(Buffer.CARET_POSITIONED, true)
      }
    }
  }

  private val buffer_listener =
    JEdit_Lib.buffer_listener(
      (buffer, edit) =>
        if (buffer.isLoaded && Isabelle_Navigator.is_active()) {
          adjust(JEdit_Lib.buffer_name(buffer), edit.convert)
        },
      loaded = init_caret)

  override def del_listener(buffers: List[Buffer]): Unit = GUI_Thread.later {
    buffers.iterator.foreach(_.removeBufferListener(buffer_listener))
  }

  override def add_listener(buffers: List[Buffer]): Unit = GUI_Thread.later {
    del_listener(buffers)
    buffers.iterator.foreach(_.addBufferListener(buffer_listener))
  }

  override def record(pos: Isabelle_Navigator.Pos): Unit = GUI_Thread.require {
    if (Isabelle_Navigator.is_active() && pos.defined && !pos.equiv(current)) {
      _backward = _backward.push(pos)
      _forward = Isabelle_Navigator.History.empty
    }
  }

  override def goto_buffer(
    buffer: Buffer,
    target: Isabelle_Navigator.Target,
    focus: Boolean = false
  ): Unit = GUI_Thread.require {
    if (focus) view.goToBuffer(buffer) else view.showBuffer(buffer)
    for (caret <- target.caret_offset(buffer)) {
      view.getTextArea.setCaretPosition(caret)
    }
  }

  override def open_file(name: String, target: Isabelle_Navigator.Target): Unit = {
    require(JEdit_Lib.jedit_buffer(name).isEmpty, "File already open: " + quote(name))
    goto_target(name, target)
    jEdit.openFile(view, name)
  }

  override def goto(pos: Isabelle_Navigator.Pos): Unit = GUI_Thread.require {
    if (pos.defined) {
      Isabelle_Navigator.passive {
        JEdit_Editor.goto_file(editor_context, pos.name, offset = pos.offset, focus = true)
      }
    }
  }

  override def backward(): Unit = GUI_Thread.require {
    if (!_backward.is_empty) {
      val here = Isabelle_Navigator.Pos(editor_context)
      if (here.equiv(current)) {
        _forward = _forward.push(current)
        _backward = _backward.pop
      }
      else {
        _forward = _forward.push(here)
      }
      goto(current)
    }
  }

  override def forward(): Unit = GUI_Thread.require {
    if (!_forward.is_empty) {
      _backward = _backward.push(recurrent)
      _forward = _forward.pop
      goto(current)
    }
  }
}
