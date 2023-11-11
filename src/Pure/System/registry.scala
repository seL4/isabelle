/*  Title:      Pure/System/registry.scala
    Author:     Makarius

Hierarchic system configuration in TOML notation.
*/

package isabelle


object Registry {
  def files(): List[Path] =
    Path.split_permissive_files(Isabelle_System.getenv("ISABELLE_REGISTRY"))

  lazy val global: Registry = new Registry(TOML.parse_files(files()))
}

class Registry private(val toml: TOML.Table) {
  override def toString: String = TOML.Format(toml)
}
