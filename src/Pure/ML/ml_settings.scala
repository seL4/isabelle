/*  Title:      Pure/ML/ml_settings.scala
    Author:     Makarius

ML system settings.
*/

package isabelle


object ML_Settings {
  def system(options: Options,
    env: Isabelle_System.Settings = Isabelle_System.Settings()
  ): ML_Settings =
    new ML_Settings {
      override def polyml_home: Path = Path.variable("POLYML_HOME").expand_env(env)
      override def ml_system: String = Isabelle_System.getenv_strict("ML_SYSTEM", env = env)
      override def ml_platform: String = {
        proper_string(options.string("ML_platform")) orElse
        proper_string(Isabelle_System.getenv("ML_PLATFORM", env = env)) getOrElse {
          val platform_64 =
            Isabelle_Platform.make(env = env)
              .ISABELLE_PLATFORM(windows = true, apple = options.bool("ML_system_apple"))
          if (options.bool("ML_system_64")) platform_64
          else platform_64.replace("64", "64_32")
        }
      }
      override def ml_options: String =
        proper_string(Isabelle_System.getenv("ML_OPTIONS", env = env)) getOrElse
          Isabelle_System.getenv(if (ml_platform_is_64_32) "ML_OPTIONS32" else "ML_OPTIONS64")
    }
}

abstract class ML_Settings {
  def polyml_home: Path
  def ml_system: String
  def ml_platform: String
  def ml_options: String

  def ml_identifier: String = ml_system + "_" + ml_platform
  def ml_home: Path = polyml_home + Path.basic(ml_platform)

  def ml_platform_is_arm: Boolean = ml_platform.containsSlice("arm64")
  def ml_platform_is_windows: Boolean = ml_platform.containsSlice("windows")
  def ml_platform_is_64_32: Boolean = ml_platform.containsSlice("64_32")

  def ml_sources: Path = polyml_home + Path.basic("src")
  def ml_sources_root: (String, String) =
    ("ML_SOURCES_ROOT", if (ml_platform_is_arm) "src/ROOT0.ML" else "src/ROOT.ML")

  def polyml_exe: Path =
    ml_home + Path.basic("poly").exe_if(ml_platform_is_windows)

  override def toString: String = ml_identifier
}
