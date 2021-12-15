/*  Title:      Pure/General/flarum.scala
    Author:     Makarius

Support for Flarum forum server: https://flarum.org
*/

package isabelle


import java.net.URL


object Flarum
{
  // see RFC3339 in https://www.php.net/manual/en/class.datetimeinterface.php
  val Date_Format = Date.Format("uuuu-MM-dd'T'HH:mm:ssxxx")

  def server(url: URL): Server = new Server(url)

  class Server private[Flarum](url: URL)
  {
    override def toString: String = url.toString

    def get(route: String): HTTP.Content =
      HTTP.Client.get(if (route.isEmpty) url else new URL(url, route))

    def get_api(route: String = ""): JSON_API.Root =
      JSON_API.Root(get("api" + (if (route.isEmpty) "" else "/" + route)).json)

    val api: JSON_API.Root = get_api()
  }
}
