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


import java.io.{InputStream, OutputStream, ByteArrayInputStream, ByteArrayOutputStream, InputStreamReader}
import java.awt.Component

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.io
import org.gjt.sp.jedit.io.VFSFile
import org.gjt.sp.jedit.io.VFSManager


object VFS {  
  val BUFFER_SIZE = 1024
  
  def input_converter(in: InputStream) = {
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
  
  class OutputConverter(out: OutputStream) extends ByteArrayOutputStream {
    override def close() {
      out.write(Isabelle.symbols.encode(new String(buf, 0, count)).getBytes)
      out.close()
    }
  }
  
  def map_file(vfs: VFS, base: VFSFile) =
    if (base == null) null else new File(vfs, base)
  
  class File(vfs: VFS, base: VFSFile) extends VFSFile {
    // FIXME redundant overriding (!??)
    
    override def getColor() = 
      base.getColor()
    
    override def getDeletePath() = 
      base.getDeletePath()
    
    override def getExtendedAttribute(name: String) =
      base.getExtendedAttribute(name)

    override def getIcon(expanded: Boolean, openBuffer: Boolean) = 
      base.getIcon(expanded, openBuffer)

    override def getLength() = 
      base.getLength()  

    override def getName() =
      base.getName()

    override def getPath() =
      Isabelle.VFS_PREFIX + base.getPath()

    override def getSymlinkPath() =
      base.getSymlinkPath()

    override def getType() =
      base.getType()

    override def getVFS() =
      vfs

    override def isBinary(session: Object) =
      base.isBinary(session)

    override def isHidden() =
      base.isHidden()

    override def isReadable() =
      base.isReadable()

    override def isWriteable() =
      base.isWriteable()

    override def setDeletePath(path: String) =
      base.setDeletePath(path)
    
    override def setHidden(hidden: Boolean) =
      base.setHidden(hidden)
      
    override def setLength(length: Long) =
      base.setLength(length)
      
    override def setName(name: String) =
      base.setName(name)
      
    override def setPath(path: String) =
      base.setPath(path)
      
    override def setReadable(readable: Boolean) =
      base.setReadable(readable)
      
    override def setWriteable(writeable: Boolean) =
      base.setWriteable(writeable)
      
    override def setSymlinkPath(symlinkPath: String) =
      base.setSymlinkPath(symlinkPath)
      
    override def setType(fType: Int) =
      base.setType(fType)
  }  
}


class VFS extends io.VFS("isabelle", VFSManager.getVFSForProtocol("file").getCapabilities) {
  private var baseVFS = VFSManager.getVFSForProtocol("file")

  private def cutPath(path: String) = 
    if (path.startsWith(Isabelle.VFS_PREFIX)) path.substring(Isabelle.VFS_PREFIX.length)
    else path
  
  override def createVFSSession(path: String, comp: Component) = 
    baseVFS.createVFSSession(cutPath(path), comp)
  
  override def getCapabilities() = 
    baseVFS.getCapabilities()
  
  override def getExtendedAttributes() = 
    baseVFS.getExtendedAttributes()
  
  override def getParentOfPath(path: String) = 
    Isabelle.VFS_PREFIX + baseVFS.getParentOfPath(cutPath(path))
  
  override def constructPath(parent: String, path: String) = 
    Isabelle.VFS_PREFIX + baseVFS.constructPath(cutPath(parent), path)
  
  override def getFileName(path: String) = 
    baseVFS.getFileName(path)
  
  override def getFileSeparator() = 
    baseVFS.getFileSeparator()
  
  override def getTwoStageSaveName(path: String) = 
    Isabelle.VFS_PREFIX + baseVFS.getTwoStageSaveName(cutPath(path))
  
  override def _canonPath(session: Object, path: String, comp: Component) =
    Isabelle.VFS_PREFIX + baseVFS._canonPath(session, cutPath(path), comp)
  
  override def _createInputStream(session: Object, path: String,
      ignoreErrors: Boolean, comp: Component) =
    VFS.input_converter(baseVFS._createInputStream(session, cutPath(path), ignoreErrors, comp))
  
  override def _createOutputStream(session: Object, path: String, comp: Component) =
    new VFS.OutputConverter(baseVFS._createOutputStream(session, cutPath(path), comp))
  
  override def _delete(session: Object, path: String, comp: Component) =
    baseVFS._delete(session, cutPath(path), comp)
  
  override def _getFile(session: Object, path: String, comp: Component) =
    VFS.map_file(this, baseVFS._getFile(session, cutPath(path), comp))

  override def _listFiles(session: Object, path: String, comp:  Component): Array[VFSFile] =
    (baseVFS._listFiles(session, cutPath(path), comp).map(file => VFS.map_file(this, file)))

  override def _mkdir(session: Object, path: String, comp: Component) =
    baseVFS._mkdir(session, cutPath(path), comp)

  override def _rename(session: Object, from: String, to: String, comp: Component) =
    baseVFS._rename(session, cutPath(from), cutPath(to), comp)

  override def _backup(session: Object, path: String, comp: Component) =
    baseVFS._backup(session, cutPath(path), comp)

  override def _saveComplete(session: Object, buffer: Buffer, path: String, comp: Component) =
    baseVFS._saveComplete(session, buffer, cutPath(path), comp)
}
