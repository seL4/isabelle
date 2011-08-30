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
  /* loaded theories provided by prover */

  private var loaded_theories: Set[String] = Set()

  override def register_thy(thy_name: String)
  {
    synchronized { loaded_theories += thy_name }
  }

  override def is_loaded(thy_name: String): Boolean =
    synchronized { loaded_theories.contains(thy_name) }


  /* file-system operations */

  override def append(master_dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (path.is_absolute) Isabelle_System.platform_path(path)
    else {
      val vfs = VFSManager.getVFSForPath(master_dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(master_dir, Isabelle_System.platform_path(path)))
      else vfs.constructPath(master_dir, Isabelle_System.standard_path(path))
    }
  }

  override def check_thy(node_name: String): Thy_Header =
  {
    Swing_Thread.now {
      Isabelle.jedit_buffers().find(buffer => Isabelle.buffer_name(buffer) == node_name) match {
        case Some(buffer) =>
          Isabelle.buffer_lock(buffer) {
            val text = new Segment
            buffer.getText(0, buffer.getLength, text)
            Some(Thy_Header.read(text))
          }
        case None => None
      }
    } getOrElse {
      val file = new File(node_name)  // FIXME load URL via jEdit VFS (!?)
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      Thy_Header.read(file)
    }
  }
}

