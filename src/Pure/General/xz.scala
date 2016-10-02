/*  Title:      Pure/General/xz.scala
    Author:     Makarius

XZ data compression.
*/

package isabelle


import java.io.{File => JFile, BufferedOutputStream, OutputStream, InputStream, BufferedInputStream}

import org.tukaani.xz.{LZMA2Options, XZInputStream, XZOutputStream}


object XZ
{
  def options(preset: Int): LZMA2Options =
  {
    val opts = new LZMA2Options
    opts.setPreset(preset)
    opts
  }

  def write_file(file: JFile, text: Iterable[CharSequence], preset: Int = 3)
  {
    val opts = options(preset)
    File.write_file(file, text,
      (s: OutputStream) => new XZOutputStream(new BufferedOutputStream(s), opts))
  }

  def uncompress(s: InputStream): XZInputStream = new XZInputStream(new BufferedInputStream(s))
}
