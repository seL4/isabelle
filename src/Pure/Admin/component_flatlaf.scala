/*  Title:      Pure/Admin/component_flatlaf.scala
    Author:     Makarius

Build Isabelle flatlaf component from official downloads.
*/

package isabelle


object Component_FlatLaf {
  /* jars and native libraries */

  sealed case class Lib(template: String, exe: Boolean = false, build: Boolean = false) {
    def path(version: String): Path =
      Path.explode(template.replace("{V}", version))

    def jar_name(version: String): Option[String] =
      if (File.is_jar(template)) Some(path(version).file_name) else None
  }

  private val libs =
    List(
      Lib("flatlaf-core/build/libs/flatlaf-{V}-no-natives.jar", build = true),
      Lib("flatlaf/{V}/flatlaf-{V}-macos-arm64.dylib"),
      Lib("flatlaf/{V}/flatlaf-{V}-macos-x86_64.dylib"),
      Lib("flatlaf/{V}/flatlaf-{V}-linux-arm64.so"),
      Lib("flatlaf/{V}/flatlaf-{V}-linux-x86_64.so"),
      Lib("flatlaf/{V}/flatlaf-{V}-windows-x86_64.dll", exe = true),
      Lib("flatlaf-extras/{V}/flatlaf-extras-{V}.jar"))


  /* build flatlaf */

  val default_source_url = "https://github.com/JFormDesigner/FlatLaf/archive/refs/tags/{V}.tar.gz"
  val default_download_url = "https://repo1.maven.org/maven2/com/formdev"
  val default_version = "3.7"

  val build_script = "./gradlew -PskipFonts -Prelease -Dorg.gradle.parallel=false jarNoNatives"
  val build_patch =
"""
diff -Nru FlatLaf-3.7/flatlaf-core/src/main/java/com/formdev/flatlaf/ui/FlatMenuBarUI.java FlatLaf-3.7-patched/flatlaf-core/src/main/java/com/formdev/flatlaf/ui/FlatMenuBarUI.java
--- FlatLaf-3.7/flatlaf-core/src/main/java/com/formdev/flatlaf/ui/FlatMenuBarUI.java	2025-12-04 12:13:56.000000000 +0100
+++ FlatLaf-3.7-patched/flatlaf-core/src/main/java/com/formdev/flatlaf/ui/FlatMenuBarUI.java	2026-01-26 22:52:11.575570940 +0100
@@ -380,9 +380,8 @@
 			JMenuBar menuBar = (JMenuBar) e.getSource();
 			JMenu menu = menuBar.getMenu( 0 );
 			if( menu != null ) {
-				MenuSelectionManager.defaultManager().setSelectedPath( SystemInfo.isWindows
-					? new MenuElement[] { menuBar, menu }
-					: new MenuElement[] { menuBar, menu, menu.getPopupMenu() } );
+				MenuSelectionManager.defaultManager().setSelectedPath(
+					new MenuElement[] { menuBar, menu, menu.getPopupMenu() } );
 
 				FlatLaf.showMnemonics( menuBar );
 			}
"""

  def build_flatlaf(
    target_dir: Path = Path.current,
    source_url: String = default_source_url,
    download_url: String = default_download_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    Isabelle_System.require_command("patch")


    /* component */

    val component_name = "flatlaf-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* mixed build and download */

    Isabelle_System.make_directory(component_dir.lib)

    val archive_url = source_url.replace("{V}", version)

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      val archive_name =
        Url.get_base_name(archive_url) getOrElse
          error("Malformed source URL " + quote(archive_url))
      val archive_path = build_dir + Path.basic(archive_name)

      Isabelle_System.download_file(archive_url, archive_path, progress = progress)
      Isabelle_System.extract(archive_path, build_dir, strip = true)
      Isabelle_System.apply_patch(build_dir, build_patch, progress = progress)

      progress.echo("Building FlatLaf from source ...")
      Isabelle_System.bash(build_script, cwd = build_dir).check

      for (lib <- libs) {
        val lib_path = lib.path(version)
        val target = component_dir.lib + Path.basic(lib_path.file_name)
        if (lib.build) {
          Isabelle_System.copy_file(build_dir + lib_path, target)
        }
        else {
          Isabelle_System.download_file(
            download_url + "/" + lib_path.implode, target, progress = progress)
        }
        if (lib.exe) File.set_executable(target)
      }
    }


    /* settings */

    val classpath =
      libs.flatMap(_.jar_name(version)).map(a => "$ISABELLE_FLATLAF_HOME/lib/" + a)
        .mkString(":")

    component_dir.write_settings("""
ISABELLE_FLATLAF_HOME="$COMPONENT"

classpath """ + quote(classpath) + """

isabelle_scala_service "isabelle.FlatLightLaf"
isabelle_scala_service "isabelle.FlatDarkLaf"
isabelle_scala_service "isabelle.FlatMacLightLaf"
isabelle_scala_service "isabelle.FlatMacDarkLaf"
""")


    /* README */

    File.write(component_dir.README,
      """This is the FlatLaf Java/Swing look-and-feel from
https://mvnrepository.com/artifact/com.formdev and
""" + archive_url + """

It is covered by the Apache License 2.0 license.

The main jar has been built from source with the following patch:
""" + build_patch + """

See also the demo application (which may be run via "java -jar ..."):
https://download.formdev.com/flatlaf/flatlaf-demo-latest.jar


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_flatlaf", "build Isabelle flatlaf component from official downloads",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var source_url = default_source_url
        var download_url = default_download_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_flatlaf [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -S URL       source URL (default: """ + quote(default_source_url) + """)
    -U URL       download URL (default: """ + quote(default_download_url) + """)
    -V VERSION   version (default: """ + quote(default_version) + """)

  Build flatlaf component from official downloads.""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "S:" -> (arg => source_url = arg),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_flatlaf(target_dir = target_dir, source_url = source_url, download_url = download_url,
          version = version, progress = progress)
      })
}
