/*  Title:      Pure/General/rdf.scala
    Author:     Makarius

Support for RDF/XML representation, see also:
  - https://www.w3.org/RDF
  - https://www.w3.org/TR/rdf-primer
*/

package isabelle


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
}
