/*  Title:      Pure/Tools/docker_build.scala
    Author:     Makarius

Build docker image from Isabelle application bundle for Linux.
*/

package isabelle


object Docker_Build {
  private val default_base = "ubuntu:22.04"
  private val default_work_dir = Path.current

  private val Isabelle_Name = """^.*?(Isabelle[^/\\:]+)_linux(?:_arm)?\.tar\.gz$""".r

  val packages: List[String] =
    List("curl", "less", "libfontconfig1", "libgomp1", "openssh-client", "perl", "pwgen", "rlwrap")

  val package_collections: Map[String, List[String]] =
    Map("X11" -> List("libx11-6", "libxext6", "libxrender1", "libxtst6", "libxi6"),
      "latex" ->
        List(
          "texlive-bibtex-extra",
          "texlive-fonts-extra",
          "texlive-font-utils",
          "texlive-latex-extra",
          "texlive-science"))

  def all_packages: List[String] =
    packages ::: package_collections.valuesIterator.flatten.toList

  def docker_build(progress: Progress,
    app_archive: String,
    base: String = default_base,
    work_dir: Path = default_work_dir,
    logic: String = Isabelle_System.default_logic(),
    no_build: Boolean = false,
    entrypoint: Boolean = false,
    output: Option[Path] = None,
    more_packages: List[String] = Nil,
    tag: String = ""
  ): Unit = {
    val isabelle_name =
      app_archive match {
        case Isabelle_Name(name) => name
        case _ => error("Cannot determine Isabelle distribution name from " + app_archive)
      }
    val is_remote = Url.is_wellformed(app_archive)

    val dockerfile =
      """## Dockerfile for """ + isabelle_name + """

FROM """ + base + """
SHELL ["/bin/bash", "-c"]

# packages
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update && \
  apt-get install -y """ + Bash.strings(packages ::: more_packages) + """ && \
  apt-get clean

# user
RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

# Isabelle
WORKDIR /home/isabelle
""" + (if (is_remote)
       "RUN curl --fail --silent --location " + Bash.string(app_archive) + " > Isabelle.tar.gz"
      else "COPY Isabelle.tar.gz .") + """
RUN tar xzf Isabelle.tar.gz && \
  mv """ + isabelle_name + """ Isabelle && \
  perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings && \
  perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=""" + logic + """,g;' Isabelle/etc/settings && \
  Isabelle/bin/isabelle build -o system_heaps -b """ + logic + """ && \
  rm Isabelle.tar.gz""" + (if (entrypoint) """

ENTRYPOINT ["Isabelle/bin/isabelle"]
""" else "")

    for (path <- output) {
      progress.echo("Dockerfile: " + path.absolute)
      File.write(path, dockerfile)
    }

    if (!no_build) {
      Isabelle_System.make_directory(work_dir)
      progress.echo("Docker working directory: " + work_dir.absolute)

      Isabelle_System.with_tmp_dir("docker_build", base_dir = work_dir.file) { tmp_dir =>
        progress.echo("Docker temporary directory: " + tmp_dir.absolute)

        File.write(tmp_dir + Path.explode("Dockerfile"), dockerfile)

        if (is_remote) {
          if (!Url.is_readable(app_archive))
            error("Cannot access remote archive " + app_archive)
        }
        else {
          Isabelle_System.copy_file(Path.explode(app_archive),
            tmp_dir + Path.explode("Isabelle.tar.gz"))
        }

        val quiet_option = if (progress.verbose) "" else " -q"
        val tag_option = if_proper(tag, " -t " + Bash.string(tag))
        progress.bash("docker build" + quiet_option + tag_option + " " + File.bash_path(tmp_dir),
          echo = true).check
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("docker_build", "build Isabelle docker image",
      Scala_Project.here,
      { args =>
        var base = default_base
        var entrypoint = false
        var work_dir = default_work_dir
        var logic = Isabelle_System.default_logic()
        var no_build = false
        var output: Option[Path] = None
        var more_packages: List[String] = Nil
        var verbose = false
        var tag = ""

        val getopts = Getopts("""
Usage: isabelle docker_build [OPTIONS] APP_ARCHIVE

  Options are:
    -B NAME      base image (default """ + quote(default_base) + """)
    -E           set Isabelle/bin/isabelle as entrypoint
    -P NAME      additional Ubuntu package collection (""" +
          package_collections.keySet.toList.sorted.map(quote(_)).mkString(", ") + """)
    -W DIR       working directory that is accessible to docker,
                 potentially via snap (default: """ + default_work_dir + """)
    -l NAME      default logic (default ISABELLE_LOGIC=""" +
          quote(Isabelle_System.default_logic()) + """)
    -n           no docker build
    -o FILE      output generated Dockerfile
    -p NAME      additional Ubuntu package
    -t TAG       docker build tag
    -v           verbose

  Build Isabelle docker image with default logic image, using a standard
  Isabelle application archive for Linux (local file or remote URL).
""",
          "B:" -> (arg => base = arg),
          "E" -> (_ => entrypoint = true),
          "P:" -> (arg =>
            package_collections.get(arg) match {
              case Some(ps) => more_packages :::= ps
              case None => error("Unknown package collection " + quote(arg))
            }),
          "W:" -> (arg => work_dir = Path.explode(arg)),
          "l:" -> (arg => logic = arg),
          "n" -> (_ => no_build = true),
          "o:" -> (arg => output = Some(Path.explode(arg))),
          "p:" -> (arg => more_packages ::= arg),
          "t:" -> (arg => tag = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val app_archive =
          more_args match {
            case List(arg) => arg
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = verbose)

        docker_build(progress, app_archive, base = base, work_dir = work_dir,
          logic = logic, no_build = no_build, entrypoint = entrypoint, output = output,
          more_packages = more_packages, tag = tag)
      })
}
