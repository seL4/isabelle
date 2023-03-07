/*  Title:      Pure/Tools/flarum.scala
    Author:     Makarius

Support for Flarum forum server: https://flarum.org
*/

package isabelle


import java.net.URL


object Flarum {
  // see RFC3339 in https://www.php.net/manual/en/class.datetimeinterface.php
  val Date_Format: Date.Format = Date.Format("uuuu-MM-dd'T'HH:mm:ssxxx")

  def server(url: URL): Server = new Server(url)

  class Server private[Flarum](url: URL) extends JSON_API.Service(url) {
    def get_api(route: String): JSON_API.Root = get_root(Url.append_path("api", route))
    val root: JSON_API.Root = get_api("")
    def users: JSON_API.Root = get_api("users")
    def groups: JSON_API.Root = get_api("groups")
    def discussions: JSON_API.Root = get_api("discussions")
  }
}
