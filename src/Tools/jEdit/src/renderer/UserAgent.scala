/*
 * XML/CSS rendering -- user agent
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.renderer

import isabelle.jedit.Isabelle

import scala.io.Source

import java.io.{InputStream, ByteArrayInputStream, FileInputStream}

import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource


object UserAgent
{
  val base_URL = "file://localhost/dummy/"

  private val style = base_URL + "style"
  private val isabelle_css = base_URL + "isabelle.css"
  private val isabelle_user_css = base_URL + "isabelle_user.css"
  private val stylesheet = """
@import "isabelle.css";
@import 'isabelle_user.css';

messages, message {
  display: block;
  white-space: pre-wrap;
  font-family: Isabelle;
}
""" 
}

class UserAgent extends NaiveUserAgent
{
  private def string_content(text: String): Array[Byte] =
    text.getBytes(Isabelle_System.charset)
  
  private def try_file_content(name: String): Array[Byte] =
  {
    val file = Isabelle.system.platform_file(name)
    val text =
      if (file.exists) Source.fromFile(file).mkString
      else ""
    string_content(text)
  }

  private def CSS(content: Array[Byte]): CSSResource =
    new CSSResource(new ByteArrayInputStream(content))

  private val stylesheet = string_content(UserAgent.stylesheet)
  private val isabelle_css = try_file_content("~~/lib/html/isabelle.css")
  private val isabelle_user_css = try_file_content("$ISABELLE_HOME_USER/etc/isabelle.css")

  override def getCSSResource(uri: String): CSSResource =
  {
    uri match {
      case UserAgent.style => CSS(stylesheet)
      case UserAgent.isabelle_css => CSS(isabelle_css)
      case UserAgent.isabelle_user_css => CSS(isabelle_user_css)
      case _ =>
        val stream = resolveAndOpenStream(uri)
        val resource = new CSSResource(stream)
        if (stream == null)
          resource.getResourceInputSource().setByteStream(
            new ByteArrayInputStream(Array()))
        resource
    }
  }
}