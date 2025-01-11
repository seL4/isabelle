/*  Author:     Fabian Huch, TU Muenchen

Support for full-text search via Solr. See also: https://solr.apache.org/
*/

package isabelle.find_facts


import isabelle._

import scala.jdk.CollectionConverters._

import org.apache.solr.client.solrj.embedded.EmbeddedSolrServer
import org.apache.solr.client.solrj.request.json.{JsonQueryRequest, TermsFacetMap, DomainMap}
import org.apache.solr.client.solrj.response.json.{BucketJsonFacet, NestableJsonFacet}
import org.apache.solr.client.solrj.response.QueryResponse
import org.apache.solr.client.solrj.SolrQuery
import org.apache.solr.common.params.CursorMarkParams
import org.apache.solr.common.{SolrDocument, SolrInputDocument}


object Solr {
  def init(solr_home: Path): Path = {
    File.write(Isabelle_System.make_directory(solr_home) + Path.basic("solr.xml"), "<solr/>")

    for (entry <- space_explode(':', Isabelle_System.getenv("SOLR_COMPONENTS")) if entry.nonEmpty)
      Isabelle_System.symlink(Path.explode(entry).absolute, solr_home, force = true)

    java.util.logging.LogManager.getLogManager.reset()
    solr_home
  }

  lazy val solr_home = init(Path.explode("$ISABELLE_HOME_USER/solr"))


  /** query language */

  val wildcard_char = Set('*', '?')
  val special =
    Set("+", "-", "&&", "||", "!", "(", ")", "{", "}", "[", "]", "^", "\"", "~", "*", "?", ":", "/")

  type Source = String

  val all: Source = "*"

  def enclose(s: Source): Source = "(" + s + ")"

  def escape(s: String, seqs: Set[String]): Source =
    seqs.foldLeft(s.replace("\\", "\\\\"))((s, seq) => s.replace(seq, "\\" + seq))

  def term(b: Boolean): Source = b.toString
  def term(i: Int): Source = i.toString
  def term(s: String): Source =
    "(\\s+)".r.replaceAllIn(escape(s, special), ws => "\\\\" + ws.matched)

  def range(from: Int, to: Int): Source = "[" + from + " TO " + to + "]"
  def phrase(s: String): Source = quote(escape(s, special))
  def wildcard(s: String): Source =
    if (!s.toList.exists(Symbol.is_ascii_blank)) escape(s, special -- wildcard_char.map(_.toString))
    else error("Invalid whitespace character in wildcard: " + quote(s))

  def filter(field: Field, x: Source): Source = field.name + ":" + x

  def infix(op: Source, args: Iterable[Source]): Source = {
    val body = args.iterator.filterNot(_.isBlank).mkString(" " + op + " ")
    if_proper(body, enclose(body))
  }

  def AND(args: Iterable[Source]): Source = infix("AND", args)
  def OR(args: Iterable[Source]): Source = infix("OR", args)

  def and(args: Source*): Source = AND(args)
  def or(args: Source*): Source = OR(args)

  def exclude(arg: Source): Source = if_proper(arg, "-" + arg)

  val query_all: Source = "*:" + all

  def tag(name: String, arg: Source): Source = "{!tag=" + name + "}" + arg


  /** solr schema **/

  object Class {
    def apply(
      markup: String,
      name: String,
      props: Properties.T = Nil,
      body: XML.Body = Nil
    ): XML.Elem = XML.Elem(Markup(markup, ("class" -> ("solr." + name)) :: props), body)
  }


  /* properties */

  val Indexed = new Properties.Boolean("indexed")
  val Stored = new Properties.Boolean("stored")
  val Column_Wise = new Properties.Boolean("docValues")
  val Multi_Valued = new Properties.Boolean("multiValued")


  /* types */

  object Type {
    val bool = Type("bool", "BoolField")
    val int = Type("int", "IntPointField")
    val long = Type("long", "LongPointField")
    val double = Type("double", "DoublePointField")
    val string = Type("string", "StrField")
    val bytes = Type("bytes", "BinaryField")
    val date = Type("date", "DatePointField")
  }

  case class Type(name: String, cls: String, props: Properties.T = Nil, body: XML.Body = Nil) {
    def defn: XML.Elem = Class("fieldType", cls, Markup.Name(name) ::: props, body)
  }


  /* fields */

  sealed case class Field(
    name: String,
    T: Type,
    props: Properties.T = Nil,
    unique_key: Boolean = false
  ) {
    def make_unique_key: Field = copy(unique_key = true)
    def defn: XML.Elem = XML.elem(Markup("field", ("name" -> name) :: ("type" -> T.name) :: props))
  }

  object Fields {
    def list(list: List[Field]): Fields = new Fields(list)
    def apply(args: Field*): Fields = list(args.toList)
  }

  final class Fields private(val list: List[Field]) extends Iterable[Field] {
    override def toString: String = list.mkString("Solr.Fields(", ", ", ")")
    def iterator: Iterator[Field] = list.iterator
  }


  /* data */

  abstract class Data(val name: String) {
    def fields: Fields
    def more_config: Map[Path, String] = Map.empty

    def stored_fields: List[Field] =
      fields.toList.filter(_.props match {
        case Stored(false) => false
        case _ => true
      })

    def unique_key: Field = Library.the_single(fields.filter(_.unique_key).toList)

    def solr_config: XML.Body = List(XML.elem("config", List(
      Class("schemaFactory", "ClassicIndexSchemaFactory"),
      XML.elem("luceneMatchVersion", XML.string(Isabelle_System.getenv("SOLR_LUCENE_VERSION"))),
      Class("updateHandler", "DirectUpdateHandler2", body = List(
        XML.elem("autoCommit", List(
          XML.elem("maxDocs", XML.string("-1")),
          XML.elem("maxTime", XML.string("-1")),
          XML.elem("maxSize", XML.string("-1")))))),
      Class("requestHandler", "SearchHandler", Markup.Name("/select")))))

    def schema: XML.Body =
      List(XML.Elem(Markup("schema",
        List(
          "name" -> "isabelle",
          "version" -> Isabelle_System.getenv("SOLR_SCHEMA_VERSION"))),
        List(
          XML.elem("uniqueKey", XML.string(unique_key.name)),
          XML.elem("fields", fields.toList.map(_.defn)),
          XML.elem("types", fields.map(_.T).toList.distinct.map(_.defn)))))
  }


  /** solr operations */

  /* documents */

  object Document {
    def empty: Document = new Document(new SolrInputDocument())
  }

  class Document private[Solr](val rep: SolrInputDocument) {
    private def obj[A](a: A): Object = a.asInstanceOf[Object]
    private def set[A](field: Field, x: A, f: A => Object = obj): Unit =
      rep.addField(field.name, f(x))
    private def set_option[A](field: Field, x: Option[A], f: A => Object = obj): Unit =
      rep.addField(field.name, x.map(f).orNull)
    private def set_list[A](field: Field, x: List[A], f: A => Object = obj): Unit =
      rep.addField(field.name, x.map(f).toArray)

    object bool {
      def update(field: Field, x: Boolean): Unit = set(field, x)
      def update(field: Field, x: Option[Boolean]): Unit = set_option(field, x)
      def update(field: Field, x: List[Boolean]): Unit = set_list(field, x)
    }
    object int {
      def update(field: Field, x: Int): Unit = set(field, x)
      def update(field: Field, x: Option[Int]): Unit = set_option(field, x)
      def update(field: Field, x: List[Int]): Unit = set_list(field, x)
    }
    object long {
      def update(field: Field, x: Long): Unit = set(field, x)
      def update(field: Field, x: Option[Long]): Unit = set_option(field, x)
      def update(field: Field, x: List[Long]): Unit = set_list(field, x)
    }
    object double {
      def update(field: Field, x: Double): Unit = set(field, x)
      def update(field: Field, x: Option[Double]): Unit = set_option(field, x)
      def update(field: Field, x: List[Double]): Unit = set_list(field, x)
    }
    object string {
      def update(field: Field, x: String): Unit = set(field, x)
      def update(field: Field, x: Option[String]): Unit = set_option(field, x)
      def update(field: Field, x: List[String]): Unit = set_list(field, x)
    }
    object bytes {
      private def value(bytes: Bytes): Array[Byte] =
        if (bytes.size > Int.MaxValue) throw new IllegalArgumentException else bytes.make_array
      def update(field: Field, x: Bytes): Unit = set(field, x, value)
      def update(field: Field, x: Option[Bytes]): Unit = set_option(field, x, value)
      def update(field: Field, x: List[Bytes]): Unit = set_list(field, x, value)
    }
    object date {
      private def value(date: Date): java.util.Date = java.util.Date.from(date.rep.toInstant)
      def update(field: Field, x: Date): Unit = set(field, x, value)
      def update(field: Field, x: Option[Date]): Unit = set_option(field, x, value)
      def update(field: Field, x: List[Date]): Unit = set_list(field, x, value)
    }
  }


  /* results */

  class Result private[Solr](rep: SolrDocument) {
    private def single[A](field: Field, f: Object => A): A = {
      val obj = rep.getFieldValue(field.name)
      if (obj == null) error("No such field: " + field.name) else f(obj)
    }
    private def get[A](field: Field, f: Object => A): Option[A] = {
      val obj = rep.getFieldValue(field.name)
      if (obj == null) None else Some(f(obj))
    }
    private def list[A](field: Field, f: Object => A): List[A] = {
      val objs = rep.getFieldValues(field.name)
      if (objs == null) Nil else objs.iterator().asScala.toList.map(f)
    }

    def bool_value(obj: Object): Boolean = obj.asInstanceOf[Boolean]
    def int_value(obj: Object): Int = obj.asInstanceOf[Int]
    def long_value(obj: Object): Long = obj.asInstanceOf[Long]
    def double_value(obj: Object): Double = obj.asInstanceOf[Double]
    def string_value(obj: Object): String = obj.asInstanceOf[String]
    def bytes_value(obj: Object): Bytes = Bytes(obj.asInstanceOf[Array[Byte]])
    def date_value(obj: Object): Date = Date.instant(obj.asInstanceOf[java.util.Date].toInstant)

    def bool(field: Field): Boolean = single(field, bool_value)
    def int(field: Field): Int = single(field, int_value)
    def long(field: Field): Long = single(field, long_value)
    def double(field: Field): Double = single(field, double_value)
    def string(field: Field): String = single(field, string_value)
    def bytes(field: Field): Bytes = single(field, bytes_value)
    def date(field: Field): Date = single(field, date_value)

    def get_bool(field: Field): Option[Boolean] = get(field, bool_value)
    def get_int(field: Field): Option[Int] = get(field, int_value)
    def get_long(field: Field): Option[Long] = get(field, long_value)
    def get_double(field: Field): Option[Double] = get(field, double_value)
    def get_string(field: Field): Option[String] = get(field, string_value)
    def get_bytes(field: Field): Option[Bytes] = get(field, bytes_value)
    def get_date(field: Field): Option[Date] = get(field, date_value)

    def list_bool(field: Field): List[Boolean] = list(field, bool_value)
    def list_int(field: Field): List[Int] = list(field, int_value)
    def list_long(field: Field): List[Long] = list(field, long_value)
    def list_double(field: Field): List[Double] = list(field, double_value)
    def list_string(field: Field): List[String] = list(field, string_value)
    def list_bytes(field: Field): List[Bytes] = list(field, bytes_value)
    def list_date(field: Field): List[Date] = list(field, date_value)
  }

  class Results private[Solr](
    solr: EmbeddedSolrServer,
    query: SolrQuery,
    private var cursor: String,
    private var more_chunks: Int = -1
  ) extends Iterator[Result] {
    private def response: QueryResponse =
      solr.query(query.set(CursorMarkParams.CURSOR_MARK_PARAM, cursor))

    private var _response = response
    private var _iterator = _response.getResults.iterator

    def num_found: Long = _response.getResults.getNumFound
    def next_cursor: String = _response.getNextCursorMark

    def hasNext: Boolean = _iterator.hasNext
    def next(): Result = {
      val res = new Result(_iterator.next())

      if (!_iterator.hasNext && next_cursor != cursor && more_chunks != 0) {
        cursor = next_cursor
        more_chunks = more_chunks - 1
        _response = response
        _iterator = _response.getResults.iterator
      }

      res
    }
  }


  /* facet results */

  class Facet_Result private[Solr](rep: NestableJsonFacet) {
    def count: Long = rep.getCount

    private def get_bucket[A](bucket: BucketJsonFacet): (A, Long) =
      bucket.getVal.asInstanceOf[A] -> bucket.getCount
    private def get_facet[A](field: Field): Map[A, Long] =
      rep.getBucketBasedFacets(field.name).getBuckets.asScala.map(get_bucket).toMap

    def bool(field: Field): Map[Boolean, Long] = get_facet(field)
    def int(field: Field): Map[Int, Long] = get_facet(field)
    def long(field: Field): Map[Long, Long] = get_facet(field)
    def string(field: Field): Map[String, Long] = get_facet(field)
  }


  /* stat results */

  private def count_field(field: Field): String = field.name + "/count"

  class Stat_Result private[Solr](rep: NestableJsonFacet) {
    def count: Long = rep.getCount
    def count(field: Field): Long = rep.getStatValue(count_field(field)).asInstanceOf[Long]
  }


  /* database */

  def database_dir(database: String): Path = solr_home + Path.basic(database)

  def init_database(database: String, data: Data, clean: Boolean = false): Database = {
    val db_dir = database_dir(database)

    if (clean) Isabelle_System.rm_tree(db_dir)

    val conf_dir = db_dir + Path.basic("conf")
    if (!conf_dir.is_dir) {
      Isabelle_System.make_directory(conf_dir)
      File.write(conf_dir + Path.basic("schema.xml"), XML.string_of_body(data.schema))
      File.write(conf_dir + Path.basic("solrconfig.xml"), XML.string_of_body(data.solr_config))
      data.more_config.foreach((path, content) => File.write(conf_dir + path, content))
    }

    open_database(database)
  }

  def open_database(database: String): Database = {
    val server = new EmbeddedSolrServer(solr_home.java_path, database)

    val cores = server.getCoreContainer.getAllCoreNames.asScala
    if (cores.contains(database)) server.getCoreContainer.reload(database)
    else server.getCoreContainer.create(database, Map.empty.asJava)

    new Database(server)
  }

  class Database private[Solr](solr: EmbeddedSolrServer) extends AutoCloseable {
    override def close(): Unit = solr.close()

    def execute_query[A](
      id: Field,
      fields: List[Field],
      cursor: Option[String],
      chunk_size: Int,
      make_result: Results => A,
      q: Source = query_all,
      fq: List[Source] = Nil,
      more_chunks: Int = -1
    ): A = {
      val query = new SolrQuery(proper_string(q).getOrElse(query_all))
        .setFields(fields.map(_.name): _*)
        .setFilterQueries(fq.filterNot(_.isBlank): _*)
        .setRows(chunk_size)
        .addSort("score", SolrQuery.ORDER.desc)
        .addSort(id.name, SolrQuery.ORDER.asc)

      val cursor1 = cursor.getOrElse(CursorMarkParams.CURSOR_MARK_START)
      make_result(new Results(solr, query, cursor1, more_chunks))
    }

    private val in_transaction = Synchronized(false)
    def transaction[A](body: => A): A = synchronized {
      in_transaction.change(b => { require(!b, "transaction already active"); true })
      try {
        val result = body
        solr.commit()
        result
      }
      catch { case exn: Throwable => solr.rollback(); throw exn }
      finally { in_transaction.change(_ => false) }
    }

    def execute_facet_query[A](
      fields: List[Field],
      make_result: Facet_Result => A,
      q: Source = query_all,
      fq: List[Source] = Nil,
      max_terms: Int = -1
    ): A = {
      val query = new JsonQueryRequest().setQuery(proper_string(q).getOrElse(query_all)).setLimit(0)
      fq.filterNot(_.isBlank).foreach(query.withFilter)

      for (field <- fields) {
        val facet =
          new TermsFacetMap(field.name).setLimit(max_terms).withDomain(
            new DomainMap().withTagsToExclude(field.name))
        query.withFacet(field.name, facet)
      }

      make_result(new Facet_Result(query.process(solr).getJsonFacetingResponse))
    }

    def execute_stats_query[A](
      fields: List[Field],
      make_result: Stat_Result => A,
      q: Source = query_all,
      fq: List[Source] = Nil
    ): A = {
      val query = new JsonQueryRequest().setQuery(proper_string(q).getOrElse(query_all)).setLimit(0)
      fq.filterNot(_.isBlank).foreach(query.withFilter)

      for (field <- fields) query.withStatFacet(count_field(field), "unique(" + field.name + ")")

      make_result(new Stat_Result(query.process(solr).getJsonFacetingResponse))
    }

    def execute_batch_insert(batch: IterableOnce[Document => Unit]): Unit = {
      val it =
        batch.iterator.map { fill =>
          val doc = Document.empty
          fill(doc)
          doc.rep
        }
      solr.add(it.asJava)
    }

    def execute_batch_delete(ids: List[String]): Unit = solr.deleteById(ids.asJava)
  }
}
