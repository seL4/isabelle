/*
 * Isabelle virtual file system for jEdit.
 *
 * This filesystem passes every operation on to FileVFS. Just the read and write
 * operations are overwritten to convert Isabelle symbols to unicode on read and
 * unicode to Isabelle symbols on write.
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit


import java.io.{InputStream, OutputStream, ByteArrayInputStream,
  ByteArrayOutputStream, InputStreamReader}
import java.awt.Component

import org.gjt.sp.jedit.{OperatingSystem, Buffer}
import org.gjt.sp.jedit.io
import org.gjt.sp.jedit.io.{VFSFile, VFSManager}


object VFS
{
  val BUFFER_SIZE = 1024

  def input_converter(in: InputStream): ByteArrayInputStream =
  {
    val reader = new InputStreamReader(in, IsabelleSystem.charset)
    val buffer = new StringBuilder
    val array = new Array[Char](BUFFER_SIZE)

    var finished = false
    while (!finished) {
      val length = reader.read(array, 0, array.length)
      if (length == -1)
        finished = true
      else
        buffer.append(array, 0, length)
    }

    val str = Isabelle.symbols.decode(buffer.toString)
    new ByteArrayInputStream(str.getBytes(IsabelleSystem.charset))
  }

  class OutputConverter(out: OutputStream) extends ByteArrayOutputStream
  {
    override def close()
    {
      out.write(Isabelle.symbols.encode(new String(buf, 0, count)).getBytes)
      out.close()
    }
  }

  class File(vfs: VFS, path: String, file: VFSFile) extends VFSFile
  {
    override def getVFS = vfs
    override def getPath = path

    override def getColor = file.getColor
    override def getDeletePath = file.getDeletePath
    override def getExtendedAttribute(name: String) = file.getExtendedAttribute(name)
    override def getIcon(expanded: Boolean, open: Boolean) = file.getIcon(expanded, open)
    override def getLength = file.getLength
    override def getName = file.getName
    override def getSymlinkPath = file.getSymlinkPath
    override def getType = file.getType
    override def isBinary(session: Object) = file.isBinary(session)
    override def isHidden = file.isHidden
    override def isReadable = file.isReadable
    override def isWriteable = file.isWriteable
    override def setDeletePath(path: String) = file.setDeletePath(path)
    override def setHidden(hidden: Boolean) = file.setHidden(hidden)
    override def setLength(length: Long) = file.setLength(length)
    override def setName(name: String) = file.setName(name)
    override def setPath(path: String) = file.setPath(path)
    override def setReadable(readable: Boolean) = file.setReadable(readable)
    override def setWriteable(writeable: Boolean) = file.setWriteable(writeable)
    override def setSymlinkPath(symlink_path: String) = file.setSymlinkPath(symlink_path)
    override def setType(ty: Int) = file.setType(ty)
  }
}

class VFS extends io.VFS("isabelle", VFSManager.getFileVFS.getCapabilities)
{
  private val base = VFSManager.getFileVFS

  private def map_file(path: String, file: VFSFile): VFSFile =
    if (file == null) null else new VFS.File(this, path, file)

  private def platform_path(path: String): String =
    Isabelle.system.platform_path(
      if (path.startsWith(Isabelle.VFS_PREFIX))
        path.substring(Isabelle.VFS_PREFIX.length)
      else path)

  override def getCapabilities = base.getCapabilities
  override def getExtendedAttributes = base.getExtendedAttributes

  override def getFileName(path: String) = base.getFileName(path)
  override def getParentOfPath(path: String) = super.getParentOfPath(path)

  override def constructPath(parent: String, path: String): String =
    if (parent.endsWith("/")) parent + path
    else parent + "/" + path

  override def getFileSeparator = '/'

  override def getTwoStageSaveName(path: String): String =
  {
    val dir = new java.io.File(platform_path(getParentOfPath(path)))
    if (dir.canWrite || OperatingSystem.isWindows)
      super.getTwoStageSaveName(path)
    else null
  }

  override def createVFSSession(path: String, comp: Component) = base.createVFSSession(path, comp)

  override def _canonPath(session: Object, path: String, comp: Component) = path  // FIXME expand?

  override def _listFiles(session: Object, path: String, comp: Component): Array[VFSFile] =
    base._listFiles(session, platform_path(path), comp).map(file =>
      map_file(constructPath(path, file.getName), file))

  override def _getFile(session: Object, path: String, comp: Component) =
    map_file(path, base._getFile(session, platform_path(path), comp))

  override def _delete(session: Object, path: String, comp: Component) =
    base._delete(session, platform_path(path), comp)

  override def _rename(session: Object, from: String, to: String, comp: Component) =
    base._rename(session, platform_path(from), platform_path(to), comp)

  override def _mkdir(session: Object, path: String, comp: Component) =
    base._mkdir(session, platform_path(path), comp)

  override def _backup(session: Object, path: String, comp: Component) =
    base._backup(session, platform_path(path), comp)

  override def _createInputStream(session: Object, path: String,
      ignoreErrors: Boolean, comp: Component) =
    VFS.input_converter(base._createInputStream(session, platform_path(path), ignoreErrors, comp))

  override def _createOutputStream(session: Object, path: String, comp: Component) =
    new VFS.OutputConverter(base._createOutputStream(session, platform_path(path), comp))

  override def _saveComplete(session: Object, buffer: Buffer, path: String, comp: Component) =
    base._saveComplete(session, buffer, platform_path(path), comp)
}
