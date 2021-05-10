/*  Title:      Pure/Admin/build_jedit.scala
    Author:     Makarius

Build auxiliary jEdit component.
*/

package isabelle


object Build_JEdit
{
  /* build jEdit component */

  private val download_jars: List[(String, String)] =
    List(
      "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.jar" ->
      "jsr305-3.0.2.jar")

  private val download_plugins: List[(String, String)] =
    List(
      "Code2HTML" -> "0.7",
      "CommonControls" -> "1.7.4",
      "Console" -> "5.1.4",
      "ErrorList" -> "2.4.0",
      "Highlight" -> "2.2",
      "Navigator" -> "2.7",
      "SideKick" -> "1.8")

  def build_jedit(
    component_dir: Path,
    version: String,
    original: Boolean = false,
    java_home: Path = default_java_home,
    progress: Progress = new Progress): Unit =
  {
    Isabelle_System.require_command("ant", test = "-version")
    Isabelle_System.require_command("patch")
    Isabelle_System.require_command("unzip", test = "-h")

    Isabelle_System.new_directory(component_dir)


    /* jEdit directory */

    val jedit = "jedit" + version
    val jedit_patched = jedit + "-patched"

    val jedit_dir = Isabelle_System.make_directory(component_dir + Path.basic(jedit))
    val jedit_patched_dir = component_dir + Path.basic(jedit_patched)

    def download_jedit(dir: Path, name: String): Path =
    {
      val jedit_name = jedit + name
      val url =
        "https://sourceforge.net/projects/jedit/files/jedit/" +
          version + "/" + jedit_name + "/download"
      val path = dir + Path.basic(jedit_name)
      Isabelle_System.download_file(url, path, progress = progress)
      path
    }

    Isabelle_System.with_tmp_dir("tmp")(tmp_dir =>
    {
      /* original version */

      val install_path = download_jedit(tmp_dir, "install.jar")
      Isabelle_System.bash("""export CLASSPATH=""
isabelle_java java -Duser.home=""" + File.bash_platform_path(tmp_dir) +
        " -jar " + File.bash_platform_path(install_path) + " auto " +
        File.bash_platform_path(jedit_dir) + " unix-script=off unix-man=off").check

      val source_path = download_jedit(tmp_dir, "source.tar.bz2")
      Isabelle_System.gnutar("-xjf " + File.bash_path(source_path), dir = jedit_dir).check


      /* patched version */

      Isabelle_System.copy_dir(jedit_dir, jedit_patched_dir)

      val source_dir = jedit_patched_dir + Path.basic("jEdit")
      val tmp_source_dir = tmp_dir + Path.basic("jEdit")

      progress.echo("Patching jEdit sources ...")
      for {
        file <- File.find_files(Path.explode("~~/src/Tools/jEdit/patches").file).iterator
        name = file.getName
        if !name.endsWith("~") && !name.endsWith(".orig")
      } {
        progress.bash("patch -p2 < " + File.bash_path(File.path(file)),
          cwd = source_dir.file, echo = true).check
      }

      progress.echo("Building jEdit ...")
      Isabelle_System.copy_dir(source_dir, tmp_source_dir)
      progress.bash("env JAVA_HOME=" + File.bash_platform_path(java_home) + " ant",
        cwd = tmp_source_dir.file, echo = true).check
      Isabelle_System.copy_file(tmp_source_dir + Path.explode("build/jedit.jar"), jedit_patched_dir)
    })


    /* jars */

    val jars_dir = Isabelle_System.make_directory(jedit_patched_dir + Path.basic("jars"))

    for { (url, name) <- download_jars } {
      Isabelle_System.download_file(url, jars_dir + Path.basic(name), progress = progress)
    }

    for { (name, vers) <- download_plugins } {
      Isabelle_System.with_tmp_file("tmp", ext = "zip")(zip_path =>
      {
        val url =
          "https://sourceforge.net/projects/jedit-plugins/files/" + name + "/" + vers + "/" +
            name + "-" + vers + "-bin.zip/download"
        Isabelle_System.download_file(url, zip_path, progress = progress)
        Isabelle_System.bash("unzip -x " + File.bash_path(zip_path), cwd = jars_dir.file).check
      })
    }



    /* diff */

    Isabelle_System.bash(
      "diff -ru " + Bash.string(jedit) + " " + Bash.string(jedit_patched) +
        " > " + Bash.string(jedit + ".patch"),
      cwd = component_dir.file).check_rc(_ <= 1)

    if (!original) Isabelle_System.rm_tree(jedit_dir)


    /* doc */

    val doc_dir = Isabelle_System.make_directory(component_dir + Path.explode("doc"))

    download_jedit(doc_dir, "manual-a4.pdf")
    download_jedit(doc_dir, "manual-letter.pdf")


    /* etc */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.explode("etc"))

    File.write(etc_dir + Path.explode("settings"),
      """# -*- shell-script -*- :mode=shellscript:

ISABELLE_JEDIT_BUILD_HOME="$COMPONENT"
ISABELLE_JEDIT_BUILD_VERSION=""" + quote(jedit_patched) + """
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
"""This is a slightly patched version of jEdit """ + version + """ from
https://sourceforge.net/projects/jedit/files/jedit with some
additional plugins jars from
https://sourceforge.net/projects/jedit-plugins/files


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val default_version = "5.6.0"
  def default_java_home: Path = Path.explode("$JAVA_HOME").expand

  val isabelle_tool =
    Isabelle_Tool("build_jedit", "build auxiliary jEdit component", Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var java_home = default_java_home
      var original = false
      var version = default_version

      val getopts = Getopts("""
Usage: isabelle build_jedit [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -J JAVA_HOME Java version for building jedit.jar (e.g. version 11)
    -O           retain copy of original jEdit directory
    -V VERSION   jEdit version (default: """ + quote(default_version) + """)

  Build auxiliary jEdit component from original sources, with some patches.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "J:" -> (arg => java_home = Path.explode(arg)),
        "O" -> (arg => original = true),
        "V:" -> (arg => version = arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val component_dir =
        target_dir + Path.basic("jedit_build-" + Date.Format.alt_date(Date.now()))

      val progress = new Console_Progress()

      build_jedit(component_dir, version, original = original,
        java_home = java_home, progress = progress)
    })
}
