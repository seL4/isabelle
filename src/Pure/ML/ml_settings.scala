/*  Title:      Pure/ML/ml_settings.scala
    Author:     Makarius

ML system settings.
*/

package isabelle


object ML_Settings {
  def system(env: Isabelle_System.Settings = Isabelle_System.Settings()): System =
    new System(env)

  class System(env: Isabelle_System.Settings = Isabelle_System.Settings()) extends ML_Settings {
    override def ml_system: String = Isabelle_System.getenv_strict("ML_SYSTEM", env = env)
    override def ml_platform: String = Isabelle_System.getenv_strict("ML_PLATFORM", env = env)
  }
}

trait ML_Settings {
  def ml_system: String
  def ml_platform: String
  def ml_identifier: String = ml_system + "_" + ml_platform
}
