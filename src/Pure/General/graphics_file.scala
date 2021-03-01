/*  Title:      Pure/General/graphics_file.scala
    Author:     Makarius

File system operations for Graphics2D output.
*/

package isabelle


import java.io.{FileOutputStream, BufferedOutputStream, File => JFile}
import java.awt.Graphics2D
import java.awt.geom.Rectangle2D
import java.awt.image.BufferedImage
import javax.imageio.ImageIO

import org.jfree.chart.JFreeChart

import com.lowagie.text.pdf.{PdfWriter, BaseFont, FontMapper, DefaultFontMapper}


object Graphics_File
{
  /* PNG */

  def write_png(
    file: JFile, paint: Graphics2D => Unit, width: Int, height: Int, dpi: Int = 72): Unit =
  {
    val scale = dpi / 72.0f
    val w = (width * scale).round
    val h = (height * scale).round

    val img = new BufferedImage(w, h, BufferedImage.TYPE_INT_ARGB)
    val gfx = img.createGraphics
    try {
      gfx.scale(scale, scale)
      paint(gfx)
      ImageIO.write(img, "png", file)
    }
    finally { gfx.dispose }
  }


  /* PDF */

  private def font_mapper(): FontMapper =
  {
    val mapper = new DefaultFontMapper
    for (entry <- Isabelle_Fonts.fonts()) {
      val params = new DefaultFontMapper.BaseFontParameters(File.platform_path(entry.path))
      params.encoding = BaseFont.IDENTITY_H
      params.embedded = true
      params.ttfAfm = entry.bytes.array
      mapper.putName(entry.name, params)
    }
    mapper
  }

  def write_pdf(file: JFile, paint: Graphics2D => Unit, width: Int, height: Int): Unit =
  {
    import com.lowagie.text.{Document, Rectangle}

    using(new BufferedOutputStream(new FileOutputStream(file)))(out =>
    {
      val document = new Document()
      try {
        document.setPageSize(new Rectangle(width.toFloat, height.toFloat))
        val writer = PdfWriter.getInstance(document, out)
        document.open()

        val cb = writer.getDirectContent()
        val tp = cb.createTemplate(width.toFloat, height.toFloat)
        val gfx = tp.createGraphics(width.toFloat, height.toFloat, font_mapper())

        paint(gfx)
        gfx.dispose

        cb.addTemplate(tp, 1, 0, 0, 1, 0, 0)
      }
      finally { document.close() }
    })
  }


  /* JFreeChart */

  def paint_chart(gfx: Graphics2D, chart: JFreeChart, width: Int, height: Int): Unit =
    chart.draw(gfx, new Rectangle2D.Double(0, 0, width, height))

  def write_chart_png(file: JFile, chart: JFreeChart, width: Int, height: Int): Unit =
    write_png(file, paint_chart(_, chart, width, height), width, height)

  def write_chart_pdf(file: JFile, chart: JFreeChart, width: Int, height: Int): Unit =
    write_pdf(file, paint_chart(_, chart, width, height), width, height)
}
