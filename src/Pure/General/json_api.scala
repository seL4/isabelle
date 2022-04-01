/*  Title:      Pure/General/json_api.scala
    Author:     Makarius

Support for JSON:API: https://jsonapi.org/format
*/

package isabelle

import java.net.URL


object JSON_API {
  val mime_type = "application/vnd.api+json"

  def api_error(msg: String): Nothing = error("JSON API error: " + msg)
  def api_errors(msgs: List[String]): Nothing = error(("JSON API errors:" :: msgs).mkString("\n  "))

  class Service(val url: URL) {
    override def toString: String = url.toString

    def get(route: String): HTTP.Content =
      HTTP.Client.get(if (route.isEmpty) url else new URL(url, route))

    def get_root(route: String = ""): Root =
      Root(get(if (route.isEmpty) "" else "/" + route).json)
  }

  sealed case class Root(json: JSON.T) {
    def get_links: Option[Links] = JSON.value(json, "links").map(Links)
    def get_next: Option[Service] = get_links.flatMap(_.get_next)

    def get_included: List[Resource] = JSON.list(json, "included", Resource.some).getOrElse(Nil)
    def get_data: Option[Data] = JSON.value(json, "data").map(Data(_, get_included))

    def get_errors: Option[List[JSON.T]] = JSON.list(json, "errors", Some(_))

    def ok: Boolean = get_errors.isEmpty
    def check: Root =
      get_errors match {
        case None => this
        case Some(List(err)) => api_error(JSON.Format(err))
        case Some(errs) => api_errors(errs.map(JSON.Format.apply))
      }
    def check_data: Data = check.get_data getOrElse api_error("missing data")
    def check_resource: Resource = check_data.resource
    def check_resources: List[Resource] = check_data.resources

    def iterator: Iterator[Root] = {
      val init = Some(this)
      new Iterator[Root] {
        private var state: Option[Root] = init
        def hasNext: Boolean = state.nonEmpty
        def next(): Root =
          state match {
            case None => Iterator.empty.next()
            case Some(res) =>
              state = res.get_next.map(_.get_root())
              res
          }
      }
    }
    def iterator_data: Iterator[Data] = iterator.map(_.check_data)
    def iterator_resource: Iterator[Resource] = iterator.map(_.check_resource)
    def iterator_resources: Iterator[Resource] = iterator.flatMap(_.check_resources)

    override def toString: String = "Root(" + (if (ok) "ok" else "errors") + ")"
  }

  sealed case class Links(json: JSON.T) {
    def get_next: Option[Service] =
      for {
        JSON.Value.String(next) <- JSON.value(json, "next")
        if Url.is_wellformed(next)
      } yield new Service(Url(next))

    override def toString: String =
      if (get_next.isEmpty) "Links()" else "Links(next)"
  }

  sealed case class Data(data: JSON.T, included: List[Resource]) {
    def is_multi: Boolean = JSON.Value.List.unapply(data, Some(_)).nonEmpty

    def resource: Resource =
      if (is_multi) api_error("singleton resource expected")
      else Resource.some(data).get

    def resources: List[Resource] =
      JSON.Value.List.unapply(data, Resource.some)
        .getOrElse(api_error("multiple resources expected"))

    override def toString: String =
      if (is_multi) "Data(resources)" else "Data(resource)"
  }

  object Resource {
    def some(json: JSON.T): Some[Resource] = Some(Resource(json))
  }

  sealed case class Resource(json: JSON.T) {
    val id: JSON.T = JSON.value(json, "id") getOrElse api_error("missing id")
    val type_ : JSON.T = JSON.value(json, "type") getOrElse api_error("missing type")
    val fields: JSON.Object.T =
      JSON.value(json, "attributes", JSON.Object.unapply).getOrElse(JSON.Object.empty) ++
      JSON.value(json, "relationships", JSON.Object.unapply).getOrElse(JSON.Object.empty)

    override def toString: String = JSON.Format(json)
  }
}
