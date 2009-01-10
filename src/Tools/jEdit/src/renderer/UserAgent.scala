/*
 * XML/CSS rendering -- user agent
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.renderer


import java.io.ByteArrayInputStream
import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource


object UserAgent {
  // FIXME avoid static getenv
  val baseURL = "file://localhost" + System.getenv("ISABELLE_HOME") + "/lib/html/"
  val userStylesheet =  "file://localhost" + System.getenv("ISABELLE_HOME_USER") + "/etc/user.css"
  val stylesheet = """

@import "isabelle.css";

@import '""" + userStylesheet + """';

messages, message {
  display: block;
  white-space: pre-wrap;
  font-family: Isabelle;
}
""" 
}

class UserAgent extends NaiveUserAgent {
  override def getCSSResource(uri : String) : CSSResource = {
    if (uri == UserAgent.baseURL + "style")
      new CSSResource(
        new ByteArrayInputStream(UserAgent.stylesheet.getBytes()))
    else {
      val stream = resolveAndOpenStream(uri)
      val resource = new CSSResource(stream)
      if (stream == null)
        resource.getResourceInputSource().setByteStream(
          new ByteArrayInputStream(new Array[Byte](0)))
      resource
    }
  }
}