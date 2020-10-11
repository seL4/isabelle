/*  Title:      Pure/Admin/build_sqlite.scala
    Author:     Makarius

Build Isabelle sqlite-jdbc component from official download.
*/

package isabelle


object Build_SQLite
{
  /* build sqlite */

  def build_sqlite(
    download_url: String,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    val Download_Name = """^.*/([^/]+)\.jar""".r
    val download_name =
      download_url match {
        case Download_Name(download_name) => download_name
        case _ => error("Malformed jar download URL: " + quote(download_url))
      }


    /* component */

    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(download_name))
    progress.echo("Component " + component_dir)


    /* README */

    File.write(component_dir + Path.basic("README"),
      "This is " + download_name + " from\n" + download_url +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))

    File.write(etc_dir + Path.basic("settings"),
"""# -*- shell-script -*- :mode=shellscript:

ISABELLE_SQLITE_HOME="$COMPONENT"

classpath "$ISABELLE_SQLITE_HOME/""" + download_name + """.jar"
""")


    /* jar */

    val jar = component_dir + Path.basic(download_name).ext("jar")
    Isabelle_System.download(download_url, jar, progress = progress)

    Isabelle_System.with_tmp_dir("sqlite")(jar_dir =>
    {
      progress.echo("Unpacking " + jar)
      Isabelle_System.bash("isabelle_jdk jar xf " + File.bash_path(jar.absolute),
        cwd = jar_dir.file).check

      val jar_files =
        List(
          "META-INF/maven/org.xerial/sqlite-jdbc/LICENSE" -> ".",
          "META-INF/maven/org.xerial/sqlite-jdbc/LICENSE.zentus" -> ".",
          "org/sqlite/native/Linux/aarch64/libsqlitejdbc.so" -> "arm64-linux",
          "org/sqlite/native/Linux/x86_64/libsqlitejdbc.so" -> "x86_64-linux",
          "org/sqlite/native/Mac/x86_64/libsqlitejdbc.jnilib" -> "x86_64-darwin",
          "org/sqlite/native/Windows/x86_64/sqlitejdbc.dll" -> "x86_64-windows")

      for ((file, dir) <- jar_files) {
        val target = Isabelle_System.make_directory(component_dir + Path.explode(dir))
        File.copy(jar_dir + Path.explode(file), target)
      }

      File.set_executable(component_dir + Path.explode("x86_64-windows/sqlitejdbc.dll"), true)
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_sqlite", "build Isabelle sqlite-jdbc component from official download",
    args =>
    {
      var target_dir = Path.current

      val getopts = Getopts("""
Usage: isabelle build_sqlite [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")

  Build sqlite-jdbc component from the specified download URL (JAR), see also
  https://github.com/xerial/sqlite-jdbc/releases
""",
        "D:" -> (arg => target_dir = Path.explode(arg)))

      val more_args = getopts(args)
      val download_url =
        more_args match {
          case List(download_url) => download_url
          case _ => getopts.usage()
        }

      val progress = new Console_Progress()

      build_sqlite(download_url, progress = progress, target_dir = target_dir)
    })
}
