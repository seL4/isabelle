/*  Title:      Pure/General/download.scala
    Author:     Makarius

Download URLs -- with progress monitor.
*/

package isabelle


import java.io.{BufferedInputStream, BufferedOutputStream, FileOutputStream, File}
import java.net.{URL, URLConnection}
import java.awt.{Component, HeadlessException}
import javax.swing.ProgressMonitorInputStream


object Download
{
  def stream(parent: Component, url: URL): (URLConnection, BufferedInputStream) =
  {
    val connection = url.openConnection

    val stream = new ProgressMonitorInputStream(null, "Downloading", connection.getInputStream)
    val monitor = stream.getProgressMonitor
    monitor.setNote(connection.getURL.toString)

    val length = connection.getContentLength
    if (length != -1) monitor.setMaximum(length)

    (connection, new BufferedInputStream(stream))
  }

  // FIXME error handling (dialogs)
  def file(parent: Component, url: URL, file: File): Boolean =
  {
    val outstream = new BufferedOutputStream(new FileOutputStream(file))

    val (connection, instream) = stream(parent, url)
    val mod_time = connection.getLastModified

    var c: Int = 0
    while ({ c = instream.read; c != -1}) outstream.write(c)

    instream.close
    outstream.close
    file.setLastModified(mod_time)
  }
}

