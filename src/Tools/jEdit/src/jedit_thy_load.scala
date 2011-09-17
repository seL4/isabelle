/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Primitives for loading theory files, based on jEdit buffer content.
*/

package isabelle.jedit


import isabelle._

import java.io.File
import javax.swing.text.Segment

import org.gjt.sp.jedit.io.{VFS, FileVFS, VFSManager}
import org.gjt.sp.jedit.MiscUtilities


class JEdit_Thy_Load extends Thy_Load
{
  override def append(dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (path.is_absolute) Isabelle_System.platform_path(path)
    else {
      val vfs = VFSManager.getVFSForPath(dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(dir, Isabelle_System.platform_path(path)))
      else vfs.constructPath(dir, Isabelle_System.standard_path(path))
    }
  }

  override def check_thy(name: Document.Node.Name): Thy_Header =
  {
    Swing_Thread.now {
      Isabelle.jedit_buffer(name.node) match {
        case Some(buffer) =>
          Isabelle.buffer_lock(buffer) {
            val text = new Segment
            buffer.getText(0, buffer.getLength, text)
            Some(Thy_Header.read(text))
          }
        case None => None
      }
    } getOrElse {
      val file = new File(name.node)  // FIXME load URL via jEdit VFS (!?)
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      Thy_Header.read(file)
    }
  }
}

