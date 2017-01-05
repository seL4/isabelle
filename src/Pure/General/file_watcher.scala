/*  Title:      Pure/General/file_watcher.scala
    Author:     Makarius

Watcher for file-system events.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.FileSystems
import java.nio.file.{WatchKey, WatchEvent, Path => JPath}
import java.nio.file.StandardWatchEventKinds.{ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY}

import scala.collection.JavaConversions


class File_Watcher private[File_Watcher]  // dummy template
{
  def register(dir: JFile) { }
  def register_parent(file: JFile) { }
  def deregister(dir: JFile) { }
  def shutdown() { }
}

object File_Watcher
{
  def apply(handle: Set[JFile] => Unit, delay: => Time = Time.seconds(0.5)): File_Watcher =
    if (Platform.is_windows) new File_Watcher
    else new Impl(handle, delay)


  /* proper implementation */

  sealed case class State(
    dirs: Map[JFile, WatchKey] = Map.empty,
    changed: Set[JFile] = Set.empty)

  class Impl private[File_Watcher](handle: Set[JFile] => Unit, delay: Time) extends File_Watcher
  {
    private val state = Synchronized(File_Watcher.State())
    private val watcher = FileSystems.getDefault.newWatchService()


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
            key.cancel
            st.copy(dirs = st.dirs - dir)
        })


    /* changed directory entries */

    private val delay_changed = Standard_Thread.delay_last(delay)
    {
      val changed = state.change_result(st => (st.changed, st.copy(changed = Set.empty)))
      handle(changed)
    }

    private val watcher_thread = Standard_Thread.fork("File_Watcher", daemon = true)
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
                      val events =
                        JavaConversions.collectionAsScalaIterable(
                          key.pollEvents.asInstanceOf[java.util.List[WatchEvent[JPath]]])
                      val remove = if (key.reset) None else Some(dir)
                      val changed =
                        (Set.empty[JFile] /: events.iterator) {
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

    override def shutdown()
    {
      watcher_thread.interrupt
      watcher_thread.join
      delay_changed.revoke
    }
  }
}
