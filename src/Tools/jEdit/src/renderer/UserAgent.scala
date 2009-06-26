/*
 * XML/CSS rendering -- user agent
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.renderer

import isabelle.jedit.Isabelle

import java.io.{InputStream, ByteArrayInputStream, FileInputStream}

import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource


object UserAgent
{
  // FIXME avoid static getenv
  val base_URL = "file://localhost/dummy/"
  val style = base_URL + "style"
  val isabelle_css = base_URL + "isabelle.css"
  val isabelle_user_css = base_URL + "isabelle_user.css"
  val stylesheet = """
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
  private def empty_stream(): InputStream =
    new ByteArrayInputStream(new Array[Byte](0))

  private def try_file_stream(name: String): InputStream =
  {
    val file = Isabelle.system.platform_file(name)
    if (file.exists) new FileInputStream(file)
    else empty_stream()
  }

  override def getCSSResource(uri: String): CSSResource =
  {
    uri match {
      case UserAgent.style =>
        new CSSResource(
          new ByteArrayInputStream(UserAgent.stylesheet.getBytes(Isabelle_System.charset)))
      case UserAgent.isabelle_css =>
        new CSSResource(try_file_stream("~~/lib/html/isabelle.css"))
      case UserAgent.isabelle_user_css =>
        new CSSResource(try_file_stream("$ISABELLE_HOME_USER/etc/isabelle.css"))
      case _ =>
        val stream = resolveAndOpenStream(uri)
        val resource = new CSSResource(stream)
        if (stream == null)
          resource.getResourceInputSource().setByteStream(empty_stream())
        resource
    }
  }
}