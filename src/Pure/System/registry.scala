/*  Title:      Pure/System/registry.scala
    Author:     Makarius

Hierarchic system configuration in TOML notation.
*/

package isabelle


object Registry {
  /* registry files */

  def load(files: Iterable[Path]): Registry = new Registry(TOML.parse_files(files))

  def global_files(): List[Path] =
    Path.split_permissive_files(Isabelle_System.getenv("ISABELLE_REGISTRY"))

  lazy val global: Registry = load(global_files())


  /* interpreted entries */

  def err(msg: String, name: String): Nothing =
    error(msg + " for registry entry " + quote(name))

  abstract class Category[A](val prefix: String) {
    override def toString: String = "Registry.Category(" + quote(prefix) + ")"
    def default_value: A
    def value(name: String, t: TOML.T): A
  }

  abstract class Table[A](prefix: String) extends Category[A](prefix) {
    def table_value(name: String, table: TOML.Table): A
    override def default_value: A = table_value("", TOML.Table.empty)
    override def value(name: String, t: TOML.T): A =
      t match {
        case table: TOML.Table => table_value(name, table)
        case _ => err("Table expected", Long_Name.qualify(prefix, name))
      }
  }


  /* build cluster resources */

  object Host extends Table[List[Options.Spec]]("host") {
    def options_spec(a: TOML.Key, b: TOML.T): Option[Options.Spec] =
      TOML.Scalar.unapply(b).map(Options.Spec.eq(a, _))

    override def table_value(a: String, t: TOML.Table): List[Options.Spec] =
      for ((a, b) <- t.any.values; s <- options_spec(a, b)) yield s
  }
}

class Registry private(val table: TOML.Table) {
  override def toString: String =
    (for (a <- table.domain.toList.sorted.iterator) yield {
      val size =
        table.any.get(a) match {
          case Some(t: TOML.Array) => "(" + t.length + ")"
          case Some(t: TOML.Table) => "(" + t.domain.size + ")"
          case _ => ""
        }
      a + size
    }).mkString("Registry(", ", ", ")")

  def get[A](category: Registry.Category[A], name: String): A = {
    table.any.get(category.prefix) match {
      case None => category.default_value
      case Some(t: TOML.Table) =>
        t.any.get(name) match {
          case None => category.default_value
          case Some(u) => category.value(name, u)
        }
      case Some(_) => Registry.err("Table expected", category.prefix)
    }
  }
}
