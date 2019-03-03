/*  Title:      Pure/General/rdf.scala
    Author:     Makarius

Support for RDF/XML representation, see also:
  - https://www.w3.org/RDF
  - https://www.w3.org/TR/rdf-primer
*/

package isabelle


import java.net.URI


object RDF
{
  /* document */

  val rdf: XML.Namespace = XML.Namespace("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
  val dc: XML.Namespace = XML.Namespace("dc", "http://purl.org/dc/elements/1.1/")

  val default_namespaces: List[XML.Namespace] = List(rdf, dc)

  def document(body: XML.Body,
    namespaces: List[XML.Namespace] = default_namespaces,
    attributes: XML.Attributes = Nil): XML.Elem =
  {
    XML.Elem(Markup(rdf("RDF"), namespaces.map(_.attribute) ::: attributes), body)
  }


  /* multiple triples vs. compact description */

  sealed case class Triple(subject: String, predicate: String, `object`: XML.Body)
  {
    def property: XML.Elem = XML.elem(predicate, `object`)
  }

  def triples(args: List[Triple]): XML.Body =
    args.groupBy(_.subject).toList.map(
      { case (subject, ts) => description(subject, ts.map(_.property)) })

  def description(subject: String, body: XML.Body, attributes: XML.Attributes = Nil): XML.Elem =
    XML.Elem(Markup(rdf("Description"), (rdf("about"), subject) :: attributes), body)


  /* collections */

  def collection(kind: String, items: List[XML.Body]): XML.Elem =
    XML.elem(kind, items.map(item => XML.elem(rdf("li"), item)))

  def bag(items: List[XML.Body]): XML.Elem = collection(rdf("Bag"), items)
  def seq(items: List[XML.Body]): XML.Elem = collection(rdf("Seq"), items)
  def alt(items: List[XML.Body]): XML.Elem = collection(rdf("Alt"), items)


  /* datatypes */

  // see https://www.w3.org/TR/rdf11-concepts/#section-Datatypes
  // see https://www.w3.org/TR/xmlschema-2/#built-in-datatypes

  def string(x: String): XML.Body = if (x.isEmpty) Nil else List(XML.Text(x))
  def uri(x: URI): XML.Body = string(x.toString)
  def bool(x: Boolean): XML.Body = string(x.toString)
  def int(x: Int): XML.Body = string(Value.Int(x))
  def long(x: Long): XML.Body = string(Value.Long(x))
  def double(x: Double): XML.Body = string(Value.Double(x))
  def seconds(x: Time): XML.Body = double(x.seconds)
  def date_time_stamp(x: Date): XML.Body = string(Date.Format("uuuu-MM-dd'T'HH:mm:ss.SSSxxx")(x))


  /* predicates */

  object Property  // binary relation with plain value
  {
    val title: String = dc("title")
    val creator: String = dc("creator")
    val contributor: String = dc("contributor")
    val date: String = dc("date")
    val description: String = dc("description")
  }
}
