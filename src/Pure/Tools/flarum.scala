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
      HTTP.Client.get(new URL(url, route))

    val api: JSON.T = get("api").json
  }
}
