/*  Title:      Pure/System/java_launcher.scala
    Author:     Makarius

Java app launcher, based on resources of "jpackage".

See also:
  https://docs.oracle.com/en/java/javase/25/docs/specs/man/jpackage.html
  https://github.com/openjdk/jdk25u-dev/tree/master/src/jdk.jpackage
*/

package isabelle

import java.util.zip.{ZipFile, ZipEntry}


object Java_Launcher {
  private sealed case class Item(name: String, output: String, executable: Boolean = false) {
    def zip_entry: ZipEntry = new ZipEntry(name)
  }

  private sealed case class Info(
    home: String = "",
    resources: String = "",
    cfg_dir: String = "",
    splash: String = "",
    items: List[Item] = Nil,
    links: List[(String, String)] = Nil
  ) {
    def home_path: Path = Path.explode(home)
    def resources_path: Path = Path.explode(resources)
  }

  private val info_linux: Info =
    Info(
      cfg_dir = "lib/app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncher",
            "bin/{NAME}",
            executable = true),
          Item(
            "classes/jdk/jpackage/internal/resources/libjpackageapplauncheraux.so",
            "lib/libapplauncher.so")),
      links = List("bin/{NAME}" -> "{NAME}", "lib/app/{NAME}.cfg" -> "{NAME}.cfg"))

  private val info_macos: Info =
    Info(
      home = "Contents/Home",
      resources = "Contents/Resources",
      cfg_dir = "Contents/app",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncher",
            "Contents/MacOS/{NAME}",
            executable = true)),
      links = List("Contents/app/{NAME}.cfg" -> "{NAME}.cfg"))

  private val info_windows: Info =
    Info(
      cfg_dir = "app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncherw.exe",
            "{NAME}.exe",
            executable = true)))

  def app_ident(name: String): String = name.replacing("_" -> "--")

  private val app_info =
    """<?xml version="1.0" ?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "https://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
<key>CFBundleDevelopmentRegion</key>
<string>English</string>
<key>CFBundleExecutable</key>
<string>{NAME}</string>
<key>CFBundleIconFile</key>
<string>lib/logo/isabelle.icns</string>
<key>CFBundleIdentifier</key>
<string>{IDENT}</string>
<key>CFBundleDisplayName</key>
<string>{NAME}</string>
<key>CFBundleInfoDictionaryVersion</key>
<string>6.0</string>
<key>CFBundleName</key>
<string>{NAME}</string>
<key>CFBundlePackageType</key>
<string>APPL</string>
<key>CFBundleShortVersionString</key>
<string>1.0</string>
<key>CFBundleSignature</key>
<string>????</string>
<key>CFBundleVersion</key>
<string>1.0</string>
<key>NSHumanReadableCopyright</key>
<string>Isabelle contributors: various open-source licenses</string>
<key>LSMinimumSystemVersion</key>
<string>10.11</string>
<key>LSApplicationCategoryType</key>
<string>public.app-category.developer-tools</string>
<key>NSHighResolutionCapable</key>
<string>true</string>
<key>NSSupportsAutomaticGraphicsSwitching</key>
<string>true</string>
<key>NSMicrophoneUsageDescription</key>
<string>The application {NAME} is requesting access to the microphone.</string>
<key>CFBundleDocumentTypes</key>
<array>
<dict>
<key>CFBundleTypeExtensions</key>
<array>
<string>thy</string>
</array>
<key>CFBundleTypeIconFile</key>
<string>lib/logo/theory.icns</string>
<key>CFBundleTypeName</key>
<string>Isabelle theory file</string>
<key>CFBundleTypeRole</key>
<string>Editor</string>
<key>LSTypeIsPackage</key>
<false/>
</dict>
</array>
</dict>
</plist>
"""

  private val runtime_info =
"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "https://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
<key>CFBundleDevelopmentRegion</key>
<string>English</string>
<key>CFBundleExecutable</key>
<string>libjli.dylib</string>
<key>CFBundleIdentifier</key>
<string>isabelle.dummy</string>
<key>CFBundleInfoDictionaryVersion</key>
<string>6.0</string>
<key>CFBundleName</key>
<string>Dummy</string>
<key>CFBundlePackageType</key>
<string>BNDL</string>
<key>CFBundleShortVersionString</key>
<string>1.0</string>
<key>CFBundleSignature</key>
<string>????</string>
<key>CFBundleVersion</key>
<string>1.0</string>
</dict>
</plist>
"""

  def setup(
    platform: Platform_Family,
    app_root: Path,
    jdk_home: Path,
    classpath: List[String] = Nil,
    java_options: List[String] = Nil,
    main_class: String = "isabelle.jedit.JEdit_Main"
  ): Unit = {
    val launcher =
      if (platform.any_linux) info_linux
      else if (platform.any_macos) info_macos
      else info_windows
    val platform_root = Path.basic(platform.native)

    val app_name = app_root.drop_ext.file_name
    val isabelle_home = app_root + launcher.resources_path
    val java_root = isabelle_home + jdk_home + platform_root

    def app_path(s: String, relative: Boolean = false): Path =
      (if (relative) Path.current else app_root) + Path.explode(s.replacing("{NAME}" -> app_name))

    val zip_path = java_root + launcher.home_path + Path.explode("jmods/jdk.jpackage.jmod")
    using(new ZipFile(zip_path.file)) { zip_file =>
      for (item <- launcher.items) {
        val path = app_path(item.output)
        if (!path.is_file) {
          val bytes = using(zip_file.getInputStream(item.zip_entry))(Bytes.read_stream(_))
          Isabelle_System.make_directory(path.dir)
          Bytes.write(path, bytes)
          if (item.executable) File.set_executable(path)
        }
      }
    }

    if (platform.any_macos) {
      val app_contents = app_root + Path.explode("Contents")
      File.write(app_contents + Path.explode("Info.plist"),
        app_info.replacing("{NAME}" -> app_name, "{IDENT}" -> app_ident(app_name)))
      File.write(app_contents + Path.explode("PkgInfo"), "APPL????")

      val runtime_contents =
        Isabelle_System.new_directory(app_root + Path.explode("Contents/runtime/Contents"))
      File.write(runtime_contents + Path.explode("Info.plist"), runtime_info)
      Isabelle_System.copy_dir(java_root + Path.explode("Contents/MacOS"), runtime_contents)
    }

    val rootdir = "$ROOTDIR" + if_proper(launcher.resources, "/" + launcher.resources)
    val rootdir1 = rootdir + "/"

    val cfg_lines =
      List("[Application]") :::
      (if (launcher.splash.isEmpty) Nil else List("app.splash=" + rootdir1 + launcher.splash)) :::
      List("app.mainclass=" + main_class) :::
      List("app.runtime=$ROOTDIR/" + File.perhaps_relative_path(app_root, java_root).implode) :::
      classpath.map(cp => "app.classpath=" + rootdir1 + cp) :::
      List("", "[JavaOptions]") :::
      (("-Disabelle.root=" + rootdir) :: java_options).map("java-options=" + _)

    val cfg_path = app_root + Path.explode(launcher.cfg_dir) + Path.basic(app_name + ".cfg")
    Isabelle_System.make_directory(cfg_path.dir)
    File.write(cfg_path, Library.terminate_lines(cfg_lines))

    for ((a, b) <- launcher.links) {
      Isabelle_System.symlink(app_path(a, relative = true), app_path(b), force = true)
    }
  }
}
