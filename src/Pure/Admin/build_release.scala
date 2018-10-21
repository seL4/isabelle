/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  /** generated content **/

  /* patch release */

  private def change_file(dir: Path, name: String, f: String => String)
  {
    val file = dir + Path.explode(name)
    File.write(file, f(File.read(file)))
  }

  def patch_release(
    dir: Path, ident: String, is_official: Boolean, dist_name: String, dist_version: String)
  {
    for (name <- List("src/Pure/System/distribution.ML", "src/Pure/System/distribution.scala"))
    {
      change_file(dir, name,
        s =>
          s.replaceAll("val is_identified = false", "val is_identified = true")
           .replaceAll("val is_official = false", "val is_official = " + is_official))
    }

    change_file(dir, "lib/scripts/getsettings",
      s =>
        s.replaceAll("ISABELLE_ID=\"\"", "ISABELLE_ID=" + quote(ident))
         .replaceAll("ISABELLE_IDENTIFIER=\"\"", "ISABELLE_IDENTIFIER=" + quote(dist_name)))

    change_file(dir, "lib/html/library_index_header.template",
      s => s.replaceAll("""\{ISABELLE\}""", dist_name))

    for {
      name <-
        List(
          "src/Pure/System/distribution.ML",
          "src/Pure/System/distribution.scala",
          "lib/Tools/version") }
    {
      change_file(dir, name, s => s.replaceAll("repository version", dist_version))
    }

    change_file(dir, "README",
      s => s.replaceAll("some repository version of Isabelle", dist_version))
  }


  /* ANNOUNCE */

  def make_announce(dir: Path, ident: String)
  {
    File.write(dir + Path.explode("ANNOUNCE"),
"""
IMPORTANT NOTE
==============

This is a snapshot of Isabelle/""" + ident + """ from the repository.

""")
  }


  /* NEWS */

  def make_news(other_isabelle: Other_Isabelle, dist_version: String)
  {
    val target = other_isabelle.isabelle_home + Path.explode("doc")
    val target_fonts = target + Path.explode("fonts")
    Isabelle_System.mkdirs(target_fonts)

    for (font <- other_isabelle.fonts(html = true))
      File.copy(font, target_fonts)

    HTML.write_document(target, "NEWS.html",
      List(HTML.title("NEWS (" + dist_version + ")")),
      List(
        HTML.chapter("NEWS"),
        HTML.source(
          Symbol.decode(File.read(other_isabelle.isabelle_home + Path.explode("NEWS"))))))
  }


  /* contrib */

  def make_contrib(dir: Path)
  {
    Isabelle_System.mkdirs(dir + Path.explode("contrib"))
    File.write(dir + Path.explode("contrib/README"),
"""This directory contains add-on components that contribute to the main
Isabelle distribution.  Separate licensing conditions apply, see each
directory individually.
""")
  }



  /** build_release **/

  sealed case class Bundle_Info(
    platform_family: String,
    platform_description: String,
    main: String,
    fallback: Option[String])
  {
    def names: List[String] = main :: fallback.toList
  }

  sealed case class Release(
    date: Date,
    dist_name: String,
    dist_dir: Path,
    ident: String)
  {
    val isabelle_dir: Path = dist_dir + Path.explode(dist_name)
    val isabelle_archive: Path = dist_dir + Path.explode(dist_name + ".tar.gz")
    val isabelle_library_archive: Path = dist_dir + Path.explode(dist_name + "_library.tar.gz")

    val other_isabelle_identifier: String = dist_name + "-build"

    val bundle_infos: List[Bundle_Info] =
      List(Bundle_Info("linux", "Linux", dist_name + "_app.tar.gz", None),
        Bundle_Info("windows", "Windows", dist_name + ".exe", None),
        Bundle_Info("macos", "Mac OS X", dist_name + ".dmg", Some(dist_name + "_dmg.tar.gz")))

    def bundle_info(platform_family: String): Bundle_Info =
      bundle_infos.find(bundle_info => bundle_info.platform_family == platform_family) getOrElse
        error("Unknown platform family " + quote(platform_family))

    def execute_dist_name(dir: Path, script: String): Unit =
      Isabelle_System.bash(script, cwd = dir.file,
        env = Isabelle_System.settings() + ("DIST_NAME" -> dist_name)).check
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
    /* make distribution */

    val release =
    {
      val release =
      {
        val date = Date.now()
        val dist_name = proper_release_name getOrElse ("Isabelle_" + Date.Format.date(date))
        val dist_dir = (base_dir + Path.explode("dist-" + dist_name)).absolute
        Release(date, dist_name, dist_dir, "")
      }

      val isabelle_ident_file = base_dir + Path.explode("ISABELLE_IDENT")
      val isabelle_dist_file = base_dir + Path.explode("ISABELLE_DIST")

      val release_ident =
        if (release.isabelle_archive.is_file &&
            isabelle_ident_file.is_file && isabelle_dist_file.is_file &&
            File.eq(Path.explode(Library.trim_line(File.read(isabelle_dist_file))),
              release.isabelle_archive)) {
          progress.echo("### Release archive already exists: " + release.isabelle_archive.implode)
          File.read(isabelle_ident_file)
        }
        else {
          progress.echo("Producing release archive " + release.isabelle_archive.implode + " ...")

          Isabelle_System.mkdirs(release.dist_dir)

          val hg = Mercurial.repository(Path.explode("$ISABELLE_HOME"))
          val version = proper_release_name orElse proper_string(rev) getOrElse "tip"
          val ident =
            try { hg.id(version) }
            catch { case ERROR(_) => error("Bad repository version: " + quote(version)) }

          val dist_version =
            if (proper_release_name.isDefined) {
              proper_release_name.get + ": " + Date.Format("LLLL uuuu")(release.date)
            }
            else "Isabelle repository snapshot " + ident + " " + Date.Format.date(release.date)

          if (release.isabelle_dir.is_dir)
            error("Directory " + release.isabelle_dir + " already exists")

          isabelle_ident_file.file.delete
          isabelle_dist_file.file.delete


          progress.echo("### Retrieving Mercurial repository version " + quote(version))

          try {
            hg.archive(release.isabelle_dir.expand.implode, rev = ident, options = "--type files")
          }
          catch { case ERROR(_) => error("Failed to retrieve " + version + "(" + ident + ")") }

          for (name <- List(".hg_archival.txt", ".hgtags", ".hgignore", "README_REPOSITORY")) {
            (release.isabelle_dir + Path.explode(name)).file.delete
          }


          progress.echo("### Preparing distribution " + quote(release.dist_name))

          patch_release(release.isabelle_dir, ident,
            proper_release_name.isDefined && official_release, release.dist_name, dist_version)

          if (proper_release_name.isEmpty) make_announce(release.isabelle_dir, ident)

          make_contrib(release.isabelle_dir)

          execute(release.isabelle_dir, """find . -print | xargs chmod -f u+rw""")


          /* build tools and documentation */

          val other_isabelle =
            Other_Isabelle(release.isabelle_dir,
              isabelle_identifier = release.other_isabelle_identifier,
              progress = progress)

          other_isabelle.init_settings(
            (base_dir.absolute + Path.explode("contrib")).implode, nonfree = false, Nil)
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

          make_news(other_isabelle, dist_version)

          for (name <- List("Admin", "browser_info", "heaps")) {
            Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode(name))
          }

          other_isabelle.cleanup()


          progress.echo("### Creating distribution archive " + release.isabelle_archive)

          release.execute_dist_name(release.dist_dir, """
set -e

chmod -R a+r "$DIST_NAME"
chmod -R u+w "$DIST_NAME"
chmod -R g=o "$DIST_NAME"
find "$DIST_NAME" -type f "(" -name "*.thy" -o -name "*.ML" -o -name "*.scala" ")" -print | xargs chmod -f u-w
""")

          execute_tar(release.dist_dir, tar_options + " -czf " +
            File.bash_path(release.isabelle_archive) + " " + Bash.string(release.dist_name))

          release.execute_dist_name(release.dist_dir, """
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

          File.write(isabelle_dist_file, release.isabelle_archive.implode)
          File.write(isabelle_ident_file, ident)
          ident
        }

      release.copy(ident = release_ident)
    }


    /* make application bundles */

    val bundle_infos = platform_families.map(release.bundle_info(_))

    for (bundle_info <- bundle_infos) {
      val bundle =
        (if (remote_mac.isEmpty) bundle_info.fallback else None) getOrElse bundle_info.main
      val bundle_archive = release.dist_dir + Path.explode(bundle)
      if (bundle_archive.is_file)
        progress.echo("### Application bundle already exists: " + bundle_archive.implode)
      else {
        progress.echo(
          "\nApplication bundle for " + bundle_info.platform_family + ": " + bundle_archive.implode)
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
        progress.echo(
          "### Library archive already exists: " + release.isabelle_library_archive.implode)
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
