/*  Title:      Pure/General/file_watcher.scala
    Author:     Makarius

Watcher for file-system events.
*/

package isabelle


import java.util.{List => JList}
import java.io.{File => JFile}
import java.nio.file.FileSystems
import java.nio.file.{WatchKey, WatchEvent, Path => JPath}
import java.nio.file.StandardWatchEventKinds.{ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY}

import scala.jdk.CollectionConverters._


class File_Watcher private[File_Watcher]  // dummy template
{
  def register(dir: JFile): Unit = {}
  def register_parent(file: JFile): Unit = {}
  def deregister(dir: JFile): Unit = {}
  def purge(retain: Set[JFile]): Unit = {}
  def shutdown(): Unit = {}
}

object File_Watcher
{
  val none: File_Watcher = new File_Watcher
  {
    override def toString: String = "File_Watcher.none"
  }

  def apply(handle: Set[JFile] => Unit, delay: => Time = Time.seconds(0.5)): File_Watcher =
    if (Platform.is_windows) none else new Impl(handle, delay)


  /* proper implementation */

  sealed case class State(
    dirs: Map[JFile, WatchKey] = Map.empty,
    changed: Set[JFile] = Set.empty)

  class Impl private[File_Watcher](handle: Set[JFile] => Unit, delay: Time) extends File_Watcher
  {
    private val state = Synchronized(File_Watcher.State())
    private val watcher = FileSystems.getDefault.newWatchService()

    override def toString: String =
      state.value.dirs.keySet.mkString("File_Watcher(", ", ", ")")


    /* registered directories */

    override def register(dir: JFile): Unit =
      state.change(st =>
        st.dirs.get(dir) match {
          case Some(key) if key.isValid => st
          case _ =>
            val key = dir.toPath.register(watcher, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY)
            st.copy(dirs = st.dirs + (dir -> key))
        })

    override def register_parent(file: JFile): Unit =
    {
      val dir = file.getParentFile
      if (dir != null && dir.isDirectory) register(dir)
    }

    override def deregister(dir: JFile): Unit =
      state.change(st =>
        st.dirs.get(dir) match {
          case None => st
          case Some(key) =>
            key.cancel()
            st.copy(dirs = st.dirs - dir)
        })

    override def purge(retain: Set[JFile]): Unit =
      state.change(st =>
        st.copy(dirs = st.dirs --
          (for ((dir, key) <- st.dirs.iterator if !retain(dir)) yield { key.cancel(); dir })))


    /* changed directory entries */

    private val delay_changed = Delay.last(delay)
    {
      val changed = state.change_result(st => (st.changed, st.copy(changed = Set.empty)))
      handle(changed)
    }

    private val watcher_thread = Isabelle_Thread.fork(name = "file_watcher", daemon = true)
    {
      try {
        while (true) {
          val key = watcher.take
          val has_changed =
            state.change_result(st =>
              {
                val (remove, changed) =
                  st.dirs.collectFirst({ case (dir, key1) if key == key1 => dir }) match {
                    case Some(dir) =>
                      val events: Iterable[WatchEvent[JPath]] =
                        key.pollEvents.asInstanceOf[JList[WatchEvent[JPath]]].asScala
                      val remove = if (key.reset) None else Some(dir)
                      val changed =
                        events.iterator.foldLeft(Set.empty[JFile]) {
                          case (set, event) => set + dir.toPath.resolve(event.context).toFile
                        }
                      (remove, changed)
                    case None =>
                      key.pollEvents
                      key.reset
                      (None, Set.empty[JFile])
                  }
                (changed.nonEmpty, st.copy(dirs = st.dirs -- remove, changed = st.changed ++ changed))
              })
          if (has_changed) delay_changed.invoke()
        }
      }
      catch { case Exn.Interrupt() => }
    }


    /* shutdown */

    override def shutdown(): Unit =
    {
      watcher_thread.interrupt()
      watcher_thread.join
      delay_changed.revoke()
    }
  }
}
