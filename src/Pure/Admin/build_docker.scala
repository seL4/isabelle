/*  Title:      Pure/Admin/build_docker.scala
    Author:     Makarius

Build docker image from Isabelle application bundle for Linux.
*/

package isabelle


object Build_Docker
{
  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  def build_docker(progress: Progress,
    app_archive: Path,
    logic: String = default_logic,
    output: Option[Path] = None,
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
  apt-get install -y less lib32stdc++6 libwww-perl rlwrap unzip && \
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
      var verbose = false
      var tag = ""

      val getopts =
        Getopts("""
Usage: isabelle build_docker [OPTIONS] APP_ARCHIVE

  Options are:
    -l NAME      default logic (default ISABELLE_LOGIC=""" + quote(default_logic) + """)
    -o FILE      output generated Dockerfile
    -t TAG       docker build tag
    -v           verbose

  Build Isabelle docker image with default logic image, using a standard
  Isabelle application archive for Linux.

  The remaining DOCKER_ARGS are passed directly to "docker build".
""",
          "l:" -> (arg => logic = arg),
          "o:" -> (arg => output = Some(Path.explode(arg))),
          "t:" -> (arg => tag = arg),
          "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      val app_archive =
        more_args match {
          case List(arg) => Path.explode(arg)
          case _ => getopts.usage()
        }

      build_docker(new Console_Progress(), app_archive, logic, output, tag, verbose)
    }, admin = true)
}
