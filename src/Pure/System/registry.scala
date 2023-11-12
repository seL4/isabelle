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

  trait Category {
    def prefix: String
    override def toString: String = "Registry.Category(" + quote(prefix) + ")"
    def qualify(name: String): String = Long_Name.qualify(prefix, name)
    def try_unqualify(name: String): Option[String] = Long_Name.try_unqualify(prefix, name)

    type A
    def bad_value(name: String): Nothing = error("Bad registry entry " + quote(qualify(name)))
    def default_value(registry: Registry, name: String): A
    def value(registry: Registry, t: TOML.T, name: String): A

    def get(registry: Registry, name: String): A = {
      registry.root.any.get(prefix) match {
        case None => default_value(registry, name)
        case Some(t: TOML.Table) =>
          t.any.get(name) match {
            case None => default_value(registry, name)
            case Some(u) => value(registry, u, name)
          }
        case Some(_) => bad_value(name)
      }
    }
  }

  trait Strict extends Category {
    override def default_value(registry: Registry, name: String): A = bad_value(name)
  }

  trait Table extends Category {
    def table_value(registry: Registry, table: TOML.Table, name: String): A
    override def default_value(registry: Registry, name: String): A =
      table_value(registry, TOML.Table.empty, name)
    override def value(registry: Registry, t: TOML.T, name: String): A =
      t match {
        case table: TOML.Table => table_value(registry, table, name)
        case _ => bad_value(name)
      }
  }


  /* build cluster resources */

  trait Host extends Table {
    def prefix = "host"
    type A = List[Options.Spec]

    def options_spec(a: TOML.Key, b: TOML.T): Option[Options.Spec] =
      TOML.Scalar.unapply(b).map(Options.Spec.eq(a, _))

    override def table_value(registry: Registry, t: TOML.Table, a: String): A =
      for ((a, b) <- t.any.values; s <- options_spec(a, b)) yield s
  }
  object Host extends Host
  object Host_Strict extends Host with Strict
}

class Registry private(val root: TOML.Table) {
  override def toString: String =
    (for (a <- root.domain.toList.sorted.iterator) yield {
      val size =
        root.any.get(a) match {
          case Some(t: TOML.Array) => "(" + t.length + ")"
          case Some(t: TOML.Table) => "(" + t.domain.size + ")"
          case _ => ""
        }
      a + size
    }).mkString("Registry(", ", ", ")")
}
