/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  /** release info **/

  sealed case class Bundle_Info(
    platform_family: String,
    platform_description: String,
    main: String,
    fallback: Option[String])
  {
    def names: List[String] = main :: fallback.toList
  }

  class Release private[Build_Release](
    val date: Date,
    val dist_name: String,
    val dist_dir: Path,
    val dist_version: String,
    val ident: String)
  {
    val isabelle_dir: Path = dist_dir + Path.explode(dist_name)
    val isabelle_archive: Path = dist_dir + Path.explode(dist_name + ".tar.gz")
    val isabelle_library_archive: Path = dist_dir + Path.explode(dist_name + "_library.tar.gz")

    val other_isabelle_identifier: String = dist_name + "-build"

    def bundle_info(platform_family: String): Bundle_Info =
      platform_family match {
        case "linux" => Bundle_Info("linux", "Linux", dist_name + "_app.tar.gz", None)
        case "windows" => Bundle_Info("windows", "Windows", dist_name + ".exe", None)
        case "macos" =>
          Bundle_Info("macos", "Mac OS X", dist_name + ".dmg", Some(dist_name + "_dmg.tar.gz"))
        case _ => error("Unknown platform family " + quote(platform_family))
      }
  }



  /** generated content **/

  /* patch release */

  private def change_file(dir: Path, name: String, f: String => String)
  {
    val file = dir + Path.explode(name)
    File.write(file, f(File.read(file)))
  }

  private val getsettings_file: String = "lib/scripts/getsettings"

  private val ISABELLE_ID = """ISABELLE_ID="(.+)"""".r

  def patch_release(release: Release, is_official: Boolean)
  {
    val dir = release.isabelle_dir

    for (name <- List("src/Pure/System/distribution.ML", "src/Pure/System/distribution.scala"))
    {
      change_file(dir, name,
        s =>
          s.replaceAllLiterally("val is_identified = false", "val is_identified = true")
           .replaceAllLiterally("val is_official = false", "val is_official = " + is_official))
    }

    change_file(dir, getsettings_file,
      s =>
        s.replaceAllLiterally("ISABELLE_ID=\"\"", "ISABELLE_ID=" + quote(release.ident))
         .replaceAllLiterally("ISABELLE_IDENTIFIER=\"\"",
            "ISABELLE_IDENTIFIER=" + quote(release.dist_name)))

    change_file(dir, "lib/html/library_index_header.template",
      s => s.replaceAllLiterally("{ISABELLE}", release.dist_name))

    for {
      name <-
        List(
          "src/Pure/System/distribution.ML",
          "src/Pure/System/distribution.scala",
          "lib/Tools/version") }
    {
      change_file(dir, name,
        s => s.replaceAllLiterally("repository version", release.dist_version))
    }

    change_file(dir, "README",
      s => s.replaceAllLiterally("some repository version of Isabelle", release.dist_version))
  }


  /* ANNOUNCE */

  def make_announce(release: Release)
  {
    File.write(release.isabelle_dir + Path.explode("ANNOUNCE"),
"""
IMPORTANT NOTE
==============

This is a snapshot of Isabelle/""" + release.ident + """ from the repository.

""")
  }


  /* NEWS */

  def make_news(other_isabelle: Other_Isabelle, dist_version: String)
  {
    val target = other_isabelle.isabelle_home + Path.explode("doc")
    val target_fonts = target + Path.explode("fonts")
    Isabelle_System.mkdirs(target_fonts)
    other_isabelle.copy_fonts(target_fonts)

    HTML.write_document(target, "NEWS.html",
      List(HTML.title("NEWS (" + dist_version + ")")),
      List(
        HTML.chapter("NEWS"),
        HTML.source(
          Symbol.decode(File.read(other_isabelle.isabelle_home + Path.explode("NEWS"))))))
  }


  /* bundled components */

  class Bundled(platform: String = "")
  {
    def detect(s: String): Boolean =
      s.startsWith("#bundled") && !s.startsWith("#bundled ")

    def apply(name: String): String =
      "#bundled" + (if (platform == "") "" else "-" + platform) + ":" + name

    private val Pattern1 = ("""^#bundled:(.*)$""").r
    private val Pattern2 = ("""^#bundled-(.*):(.*)$""").r

    def unapply(s: String): Option[String] =
      s match {
        case Pattern1(name) => Some(name)
        case Pattern2(platform1, name) if platform == platform1 => Some(name)
        case _ => None
      }
  }

  def record_bundled_components(dir: Path)
  {
    val catalogs =
      List("main", "bundled").map((_, new Bundled())) :::
      default_platform_families.flatMap(platform =>
        List(platform, "bundled-" + platform).map((_, new Bundled(platform = platform))))

    File.append(Components.components(dir),
      terminate_lines("#bundled components" ::
        (for {
          (catalog, bundled) <- catalogs.iterator
          val path = Components.admin(dir) + Path.basic(catalog)
          if path.is_file
          line <- split_lines(File.read(path))
          if line.nonEmpty && !line.startsWith("#") && !line.startsWith("jedit_build")
        } yield bundled(line)).toList))
  }

  def get_bundled_components(dir: Path, platform: String): List[String] =
  {
    val Bundled = new Bundled(platform)
    for (Bundled(name) <- Components.read_components(dir)) yield name
  }

  def activate_bundled_components(dir: Path, platform: String)
  {
    val Bundled = new Bundled(platform)
    Components.write_components(dir,
      Components.read_components(dir).flatMap(line =>
        line match {
          case Bundled(name) =>
            if (Components.check_dir(Components.contrib(dir, name)))
              Some(Components.contrib(name = name).implode)
            else None
          case _ => if (Bundled.detect(line)) None else Some(line)
        }))
  }

  def make_contrib(dir: Path)
  {
    Isabelle_System.mkdirs(Components.contrib(dir))
    File.write(Components.contrib(dir, "README"),
"""This directory contains add-on components that contribute to the main
Isabelle distribution.  Separate licensing conditions apply, see each
directory individually.
""")
  }



  /** build_release **/

  def distribution_classpath(
    components_base: Path,
    isabelle_home: Path,
    isabelle_classpath: String): List[Path] =
  {
    val base = isabelle_home.absolute
    val contrib_base = components_base.absolute

    Path.split(isabelle_classpath).map(path =>
    {
      val abs_path = path.absolute
      File.relative_path(base, abs_path) match {
        case Some(rel_path) => rel_path
        case None =>
          File.relative_path(contrib_base, abs_path) match {
            case Some(rel_path) => Components.contrib() + rel_path
            case None => error("Bad ISABELLE_CLASSPATH element: " + path)
          }
      }
    }) ::: List(Path.explode("src/Tools/jEdit/dist/jedit.jar"))
  }

  private def execute(dir: Path, script: String): Unit =
    Isabelle_System.bash(script, cwd = dir.file).check

  private def execute_tar(dir: Path, args: String): Unit =
    Isabelle_System.gnutar(args, cwd = dir.file).check

  private def tar_options: String =
    if (Platform.is_macos) "--owner=root --group=staff" else "--owner=root --group=root"

  private val default_platform_families = List("linux", "windows", "macos")

  def build_release(base_dir: Path,
    progress: Progress = No_Progress,
    rev: String = "",
    afp_rev: String = "",
    official_release: Boolean = false,
    proper_release_name: Option[String] = None,
    platform_families: List[String] = default_platform_families,
    website: Option[Path] = None,
    build_library: Boolean = false,
    parallel_jobs: Int = 1,
    remote_mac: String = ""): Release =
  {
    val hg = Mercurial.repository(Path.explode("$ISABELLE_HOME"))

    val release =
    {
      val date = Date.now()
      val dist_name = proper_release_name getOrElse ("Isabelle_" + Date.Format.date(date))
      val dist_dir = (base_dir + Path.explode("dist-" + dist_name)).absolute

      val version = proper_release_name orElse proper_string(rev) getOrElse "tip"
      val ident =
        try { hg.id(version) }
        catch { case ERROR(_) => error("Bad repository version: " + version) }

      val dist_version =
        proper_release_name match {
          case Some(name) => name + ": " + Date.Format("LLLL uuuu")(date)
          case None => "Isabelle repository snapshot " + ident + " " + Date.Format.date(date)
        }

      new Release(date, dist_name, dist_dir, dist_version, ident)
    }


    /* make distribution */

    if (release.isabelle_archive.is_file) {
      progress.echo("### Release archive already exists: " + release.isabelle_archive)

      val archive_ident =
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val getsettings = Path.explode(release.dist_name + "/" + getsettings_file)
            execute_tar(tmp_dir, "-xzf " +
              File.bash_path(release.isabelle_archive) + " " + File.bash_path(getsettings))
            split_lines(File.read(tmp_dir + getsettings))
              .collectFirst({ case ISABELLE_ID(ident) => ident })
              .getOrElse(error("Failed to read ISABELLE_ID from " + release.isabelle_archive))
          })

      if (release.ident != archive_ident) {
        error("Mismatch of release identification " + release.ident +
          " vs. archive " + archive_ident)
      }
    }
    else {
      progress.echo("### Producing release archive " + release.isabelle_archive + " ...")

      Isabelle_System.mkdirs(release.dist_dir)

      if (release.isabelle_dir.is_dir)
        error("Directory " + release.isabelle_dir + " already exists")


      progress.echo("### Retrieving Mercurial repository version " + release.ident)

      hg.archive(release.isabelle_dir.expand.implode, rev = release.ident, options = "--type files")

      for (name <- List(".hg_archival.txt", ".hgtags", ".hgignore", "README_REPOSITORY")) {
        (release.isabelle_dir + Path.explode(name)).file.delete
      }


      progress.echo("### Preparing distribution " + quote(release.dist_name))

      patch_release(release, proper_release_name.isDefined && official_release)

      if (proper_release_name.isEmpty) make_announce(release)

      make_contrib(release.isabelle_dir)

      execute(release.isabelle_dir, """find . -print | xargs chmod -f u+rw""")


      /* build tools and documentation */

      val other_isabelle =
        Other_Isabelle(release.isabelle_dir,
          isabelle_identifier = release.other_isabelle_identifier,
          progress = progress)

      other_isabelle.init_settings(
        other_isabelle.init_components(base = Components.contrib(base_dir.absolute)))
      other_isabelle.resolve_components(echo = true)

      try {
        val export_classpath =
          "export CLASSPATH=" + Bash.string(other_isabelle.getenv("ISABELLE_CLASSPATH")) + "\n"
        other_isabelle.bash(export_classpath + "./Admin/build all", echo = true).check
        other_isabelle.bash(export_classpath + "./bin/isabelle jedit -b", echo = true).check
      }
      catch { case ERROR(_) => error("Failed to build tools") }

      try {
        other_isabelle.bash(
          "./bin/isabelle build_doc -a -s -j " + parallel_jobs, echo = true).check
      }
      catch { case ERROR(_) => error("Failed to build documentation") }

      make_news(other_isabelle, release.dist_version)

      for (name <- List("Admin", "browser_info", "heaps")) {
        Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode(name))
      }

      other_isabelle.cleanup()


      progress.echo("### Creating distribution archive " + release.isabelle_archive)

      def execute_dist_name(script: String): Unit =
        Isabelle_System.bash(script, cwd = release.dist_dir.file,
          env = Isabelle_System.settings() + ("DIST_NAME" -> release.dist_name)).check

      execute_dist_name("""
set -e

chmod -R a+r "$DIST_NAME"
chmod -R u+w "$DIST_NAME"
chmod -R g=o "$DIST_NAME"
find "$DIST_NAME" -type f "(" -name "*.thy" -o -name "*.ML" -o -name "*.scala" ")" -print | xargs chmod -f u-w
""")

      execute_tar(release.dist_dir, tar_options + " -czf " +
        File.bash_path(release.isabelle_archive) + " " + Bash.string(release.dist_name))

      execute_dist_name("""
set -e

mv "$DIST_NAME" "${DIST_NAME}-old"
mkdir "$DIST_NAME"

mv "${DIST_NAME}-old/README" "${DIST_NAME}-old/NEWS" "${DIST_NAME}-old/ANNOUNCE" \
  "${DIST_NAME}-old/COPYRIGHT" "${DIST_NAME}-old/CONTRIBUTORS" "$DIST_NAME"
mkdir "$DIST_NAME/doc"
mv "${DIST_NAME}-old/doc/"*.pdf \
  "${DIST_NAME}-old/doc/"*.html \
  "${DIST_NAME}-old/doc/"*.css \
  "${DIST_NAME}-old/doc/fonts" \
  "${DIST_NAME}-old/doc/Contents" "$DIST_NAME/doc"

rm -f Isabelle && ln -sf "$DIST_NAME" Isabelle

rm -rf "${DIST_NAME}-old"
""")
    }


    /* make application bundles */

    val bundle_infos = platform_families.map(release.bundle_info)

    for (bundle_info <- bundle_infos) {
      val bundle =
        (if (remote_mac.isEmpty) bundle_info.fallback else None) getOrElse bundle_info.main
      val bundle_archive = release.dist_dir + Path.explode(bundle)
      if (bundle_archive.is_file)
        progress.echo("### Application bundle already exists: " + bundle_archive)
      else {
        progress.echo(
          "\nApplication bundle for " + bundle_info.platform_family + ": " + bundle_archive)
        progress.bash(
          "isabelle makedist_bundle " + File.bash_path(release.isabelle_archive) +
            " " + Bash.string(bundle_info.platform_family) +
            (if (remote_mac == "") "" else " " + Bash.string(remote_mac)),
          echo = true).check
      }
    }


    /* minimal website */

    for (dir <- website) {
      val website_platform_bundles =
        for {
          bundle_info <- bundle_infos
          bundle <- bundle_info.names.find(name => (release.dist_dir + Path.explode(name)).is_file)
        } yield (bundle, bundle_info)

      val afp_link =
        HTML.link(AFP.repos_source + "/commits/" + afp_rev, HTML.text("AFP/" + afp_rev))

      HTML.write_document(dir, "index.html",
        List(HTML.title(release.dist_name)),
        List(
          HTML.chapter(release.dist_name + " (" + release.ident + ")"),
          HTML.itemize(
            website_platform_bundles.map({ case (bundle, bundle_info) =>
              List(HTML.link(bundle, HTML.text(bundle_info.platform_description))) }))) :::
        (if (afp_rev == "") Nil else List(HTML.par(HTML.text("See also ") ::: List(afp_link)))))

      for ((bundle, _) <- website_platform_bundles)
        File.copy(release.dist_dir + Path.explode(bundle), dir)
    }


    /* HTML library */

    if (build_library) {
      if (release.isabelle_library_archive.is_file) {
        progress.echo("### Library archive already exists: " + release.isabelle_library_archive)
      }
      else {
        Isabelle_System.with_tmp_dir("build_release")(tmp_dir =>
          {
            val name = release.dist_name
            val platform = Isabelle_System.getenv_strict("ISABELLE_PLATFORM_FAMILY")
            val bundle = release.dist_dir + Path.explode(name + "_" + platform + ".tar.gz")
            execute_tar(tmp_dir, "-xzf " + File.bash_path(bundle))

            val other_isabelle =
              Other_Isabelle(tmp_dir + Path.explode(name),
                isabelle_identifier = release.other_isabelle_identifier, progress = progress)

            Isabelle_System.mkdirs(other_isabelle.etc)
            File.write(other_isabelle.etc_preferences, "ML_system_64 = true\n")

            other_isabelle.bash("bin/isabelle build -j " + parallel_jobs +
                " -o browser_info -o document=pdf -o document_variants=document:outline=/proof,/ML" +
                " -s -c -a -d '~~/src/Benchmarks'", echo = true).check
            other_isabelle.isabelle_home_user.file.delete

            execute(tmp_dir, "chmod -R a+r " + Bash.string(name))
            execute(tmp_dir, "chmod -R g=o " + Bash.string(name))
            execute_tar(tmp_dir,
              tar_options + " -czf " + File.bash_path(release.isabelle_library_archive) +
              " " + Bash.string(name + "/browser_info"))
          })
      }
    }

    release
  }



  /** command line entry point **/

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var afp_rev = ""
      var remote_mac = ""
      var official_release = false
      var proper_release_name: Option[String] = None
      var website: Option[Path] = None
      var parallel_jobs = 1
      var build_library = false
      var platform_families = default_platform_families
      var rev = ""

      val getopts = Getopts("""
Usage: Admin/build_release [OPTIONS] BASE_DIR

  Options are:
    -A REV       corresponding AFP changeset id
    -M USER@HOST remote Mac OS X for dmg build
    -O           official release (not release-candidate)
    -R RELEASE   proper release with name
    -W WEBSITE   produce minimal website in given directory
    -j INT       maximum number of parallel jobs (default 1)
    -l           build library
    -p NAMES     platform families (default: """ + default_platform_families.mkString(",") + """)
    -r REV       Mercurial changeset id (default: RELEASE or tip)

  Build Isabelle release in base directory, using the local repository clone.
""",
        "A:" -> (arg => afp_rev = arg),
        "M:" -> (arg => remote_mac = arg),
        "O" -> (_ => official_release = true),
        "R:" -> (arg => proper_release_name = Some(arg)),
        "W:" -> (arg => website = Some(Path.explode(arg))),
        "j:" -> (arg => parallel_jobs = Value.Int.parse(arg)),
        "l" -> (_ => build_library = true),
        "p:" -> (arg => platform_families = space_explode(',', arg)),
        "r:" -> (arg => rev = arg))

      val more_args = getopts(args)
      val base_dir = more_args match { case List(base_dir) => base_dir case _ => getopts.usage() }

      val progress = new Console_Progress()

      build_release(Path.explode(base_dir), progress = progress, rev = rev, afp_rev = afp_rev,
        official_release = official_release, proper_release_name = proper_release_name,
        website = website,
        platform_families =
          if (platform_families.isEmpty) default_platform_families
          else platform_families,
        build_library = build_library, parallel_jobs = parallel_jobs, remote_mac = remote_mac)
    }
  }
}
