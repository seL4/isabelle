/*  Title:      Pure/System/download.scala
    Module:     PIDE
    Author:     Makarius

Download URLs -- with progress monitor.
*/

package isabelle


import java.io.{BufferedInputStream, BufferedOutputStream, FileOutputStream,
  File, InterruptedIOException}
import java.net.{URL, URLConnection}
import java.awt.{Component, HeadlessException}
import javax.swing.ProgressMonitorInputStream


object Download
{
  def stream(parent: Component, title: String, url: URL): (URLConnection, BufferedInputStream) =
  {
    val connection = url.openConnection

    val stream = new ProgressMonitorInputStream(parent, title, connection.getInputStream)
    val monitor = stream.getProgressMonitor
    monitor.setNote(connection.getURL.toString)

    val length = connection.getContentLength
    if (length != -1) monitor.setMaximum(length)

    (connection, new BufferedInputStream(stream))
  }

  def file(parent: Component, title: String, url: URL, file: File)
  {
    val (connection, instream) = stream(parent, title, url)
    val mod_time = connection.getLastModified

    def read() =
      try { instream.read }
      catch { case _ : InterruptedIOException => error("Canceled by user") }
    try {
      val outstream = new BufferedOutputStream(new FileOutputStream(file))
      try {
        var c: Int = 0
        while ({ c = read(); c != -1 }) outstream.write(c)
      }
      finally { outstream.close }
      if (mod_time > 0) file.setLastModified(mod_time)
    }
    finally { instream.close }
  }
}

