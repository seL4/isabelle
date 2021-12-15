/*  Title:      Pure/General/json_api.scala
    Author:     Makarius

Support for JSON:API: https://jsonapi.org/format
*/

package isabelle


object JSON_API
{
  val mime_type = "application/vnd.api+json"

  def api_error(msg: String): Nothing = error("JSON API error: " + msg)
  def api_errors(msgs: List[String]): Nothing = error(("JSON API errors:" :: msgs).mkString("\n  "))

  sealed case class Root(json: JSON.T)
  {
    def get_links: Option[Links] = JSON.value(json, "links").map(Links)
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

    override def toString: String = "Root(" + (if (ok) "ok" else "errors") + ")"
  }

  sealed case class Links(json: JSON.T)
  {
    def get_next: Option[Root] =
      for (next <- JSON.value(json, "next") if next != null) yield Root(next)

    override def toString: String =
      if (get_next.isEmpty) "Links()" else "Links(next)"
  }

  sealed case class Data(data: JSON.T, included: List[Resource])
  {
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

  object Resource
  {
    def some(json: JSON.T): Some[Resource] = Some(Resource(json))
  }

  sealed case class Resource(json: JSON.T)
  {
    val id: JSON.T = JSON.value(json, "id") getOrElse api_error("missing id")
    val type_ : JSON.T = JSON.value(json, "type") getOrElse api_error("missing type")
    val fields: JSON.Object.T =
      JSON.value(json, "attributes", JSON.Object.unapply).getOrElse(JSON.Object.empty) ++
      JSON.value(json, "relationships", JSON.Object.unapply).getOrElse(JSON.Object.empty)

    override def toString: String = JSON.Format(json)
  }
}
