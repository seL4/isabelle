/*  Title:      Pure/Admin/build_docker.scala
    Author:     Makarius

Build docker image from Isabelle application bundle for Linux.
*/

package isabelle


object Build_Docker
{
  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  val packages: List[String] =
    List("less", "lib32stdc++6", "libgomp1", "libwww-perl", "rlwrap", "unzip")

  val package_collections: Map[String, List[String]] =
    Map("X11" -> List("libx11-6", "libxext6", "libxrender1", "libxtst6", "libxi6"),
      "latex" -> List("texlive-fonts-extra", "texlive-latex-extra", "texlive-math-extra"))

  def build_docker(progress: Progress,
    app_archive: Path,
    logic: String = default_logic,
    output: Option[Path] = None,
    more_packages: List[String] = Nil,
    tag: String = "",
    verbose: Boolean = false)
  {
    val distname =
    {
      val Name = "^(Isabelle[^/]*)/?.*$".r
      Isabelle_System.bash("tar tzf " + File.bash_path(app_archive)).check.out_lines match {
        case Name(name) :: _ => name
        case _ => error("Cannot determine Isabelle distribution name from " + app_archive)
      }
    }

    val dockerfile =
      """## Dockerfile for """ + distname + """

FROM ubuntu
SHELL ["/bin/bash", "-c"]

# packages
RUN apt-get -y update && \
  apt-get install -y  """ + (packages ::: more_packages).map(Bash.string(_)).mkString(" ") + """ && \
  apt-get clean

# user
RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

# Isabelle
WORKDIR /home/isabelle
COPY Isabelle.tar.gz .
RUN tar xzf Isabelle.tar.gz && \
  mv """ + distname + """ Isabelle && \
  rm -rf Isabelle.tar.gz Isabelle/contrib/jdk/x86-linux && \
  perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings && \
  perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=""" + logic + """,g;' Isabelle/etc/settings && \
  Isabelle/bin/isabelle build -s -b """ + logic + """

ENTRYPOINT ["Isabelle/bin/isabelle"]
"""

    output.foreach(File.write(_, dockerfile))

    Isabelle_System.with_tmp_dir("docker")(tmp_dir =>
      {
        File.write(tmp_dir + Path.explode("Dockerfile"), dockerfile)
        File.copy(app_archive, tmp_dir + Path.explode("Isabelle.tar.gz"))

        val quiet_option = if (verbose) "" else " -q"
        val tag_option = if (tag == "") "" else " -t " + Bash.string(tag)
        progress.bash("docker build" + quiet_option + tag_option + " " + File.bash_path(tmp_dir),
          echo = true).check
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_docker", "build Isabelle docker image", args =>
    {
      var logic = default_logic
      var output: Option[Path] = None
      var more_packages: List[String] = Nil
      var verbose = false
      var tag = ""

      val getopts =
        Getopts("""
Usage: isabelle build_docker [OPTIONS] APP_ARCHIVE

  Options are:
    -P NAME      additional Ubuntu package collection (""" +
          package_collections.keySet.toList.sorted.map(quote(_)).mkString(", ") + """)
    -l NAME      default logic (default ISABELLE_LOGIC=""" + quote(default_logic) + """)
    -o FILE      output generated Dockerfile
    -p NAME      additional Ubuntu package
    -t TAG       docker build tag
    -v           verbose

  Build Isabelle docker image with default logic image, using a standard
  Isabelle application archive for Linux.

  Example:

    isabelle build_docker -t test/isabelle:Isabelle2016-1 Isabelle2016-1_app.tar.gz
""",
          "P:" -> (arg =>
            package_collections.get(arg) match {
              case Some(ps) => more_packages :::= ps
              case None => error("Unknown package collection " + quote(arg))
            }),
          "l:" -> (arg => logic = arg),
          "o:" -> (arg => output = Some(Path.explode(arg))),
          "p:" -> (arg => more_packages ::= arg),
          "t:" -> (arg => tag = arg),
          "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      val app_archive =
        more_args match {
          case List(arg) => Path.explode(arg)
          case _ => getopts.usage()
        }

      build_docker(new Console_Progress(), app_archive, logic = logic, output = output,
        more_packages = more_packages, tag = tag, verbose = verbose)
    }, admin = true)
}
