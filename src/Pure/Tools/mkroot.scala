/*  Title:      Pure/Tools/mkroot.scala
    Author:     Makarius

Prepare session root directory.
*/

package isabelle


object Mkroot
{
  /** mkroot **/

  def root_name(name: String): String =
    Token.quote_name(Sessions.root_syntax.keywords, name)

  def latex_name(name: String): String =
    (for (c <- name.iterator if c != '\\')
     yield if (c == '_') '-' else c).mkString

  def mkroot(
    session_name: String = "",
    session_dir: Path = Path.current,
    session_parent: String = "",
    init_repos: Boolean = false,
    title: String = "",
    author: String = "",
    progress: Progress = new Progress): Unit =
  {
    Isabelle_System.make_directory(session_dir)

    val name = proper_string(session_name) getOrElse session_dir.absolute_file.getName
    val parent = proper_string(session_parent) getOrElse Isabelle_System.getenv("ISABELLE_LOGIC")

    val root_path = session_dir + Sessions.ROOT
    if (root_path.file.exists) error("Cannot overwrite existing " + root_path)

    val document_path = session_dir + Path.explode("document")
    if (document_path.file.exists) error("Cannot overwrite existing " + document_path)

    val root_tex = session_dir + Path.explode("document/root.tex")


    progress.echo("\nPreparing session " + quote(name) + " in " + session_dir)


    /* ROOT */

    progress.echo("  creating " + root_path)

    File.write(root_path,
      "session " + root_name(name) + " = " + root_name(parent) + """ +
  options [document = pdf, document_output = "output"]
(*theories [document = false]
    A
    B
  theories
    C
    D*)
  document_files
    "root.tex"
""")


    /* document directory */

    {
      progress.echo("  creating " + root_tex)

      Isabelle_System.make_directory(root_tex.dir)

      File.write(root_tex,
"""\documentclass[11pt,a4paper]{article}
\""" + """usepackage[T1]{fontenc}
\""" + """usepackage{isabelle,isabellesym}

% further packages required for unusual symbols (see also
% isabellesym.sty), use only when needed

%\""" + """usepackage{amssymb}
  %for \<leadsto>, \<box>, \<diamond>, \<sqsupset>, \<mho>, \<Join>,
  %\<lhd>, \<lesssim>, \<greatersim>, \<lessapprox>, \<greaterapprox>,
  %\<triangleq>, \<yen>, \<lozenge>

%\""" + """usepackage{eurosym}
  %for \<euro>

%\""" + """usepackage[only,bigsqcap,bigparallel,fatsemi,interleave,sslash]{stmaryrd}
  %for \<Sqinter>, \<Parallel>, \<Zsemi>, \<Parallel>, \<sslash>

%\""" + """usepackage{eufrak}
  %for \<AA> ... \<ZZ>, \<aa> ... \<zz> (also included in amssymb)

%\""" + """usepackage{textcomp}
  %for \<onequarter>, \<onehalf>, \<threequarters>, \<degree>, \<cent>,
  %\<currency>

% this should be the last package used
\""" + """usepackage{pdfsetup}

% urls in roman style, theory text in math-similar italics
\""" + """urlstyle{rm}
\isabellestyle{it}

% for uniform font size
%\renewcommand{\isastyle}{\isastyleminor}


\begin{document}

\title{""" + (proper_string(title) getOrElse latex_name(name)) + """}
\author{""" + (proper_string(author) getOrElse latex_name(System.getProperty("user.name"))) + """}
\maketitle

\tableofcontents

% sane default for proof documents
\parindent 0pt\parskip 0.5ex

% generated text of all theories
\input{session}

% optional bibliography
%\bibliographystyle{abbrv}
%\bibliography{root}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
""")
    }


    /* Mercurial repository */

    if (init_repos) {
      progress.echo("  \nInitializing Mercurial repository " + session_dir)

      val hg = Mercurial.init_repository(session_dir)

      val hg_ignore = session_dir + Path.explode(".hgignore")
      File.write(hg_ignore,
"""syntax: glob

*~
*.marks
*.orig
*.rej
.DS_Store
.swp

syntax: regexp

^output/
""")

      hg.add(List(root_path, root_tex, hg_ignore))
    }


    /* notes */

    {
      val print_dir = session_dir.implode
      progress.echo("""
Now use the following command line to build the session:

  isabelle build -D """ +
        (if (Bash.string(print_dir) == print_dir) print_dir else quote(print_dir)) + "\n")
    }
  }



  /** Isabelle tool wrapper **/

  val isabelle_tool = Isabelle_Tool("mkroot", "prepare session root directory",
    Scala_Project.here, args =>
  {
    var author = ""
    var init_repos = false
    var title = ""
    var session_name = ""

    val getopts = Getopts("""
Usage: isabelle mkroot [OPTIONS] [DIRECTORY]

  Options are:
    -A LATEX     provide author in LaTeX notation (default: user name)
    -I           init Mercurial repository and add generated files
    -T LATEX     provide title in LaTeX notation (default: session name)
    -n NAME      alternative session name (default: directory base name)

  Prepare session root directory (default: current directory).
""",
      "A:" -> (arg => author = arg),
      "I" -> (arg => init_repos = true),
      "T:" -> (arg => title = arg),
      "n:" -> (arg => session_name = arg))

    val more_args = getopts(args)

    val session_dir =
      more_args match {
        case Nil => Path.current
        case List(dir) => Path.explode(dir)
        case _ => getopts.usage()
      }

    mkroot(session_name = session_name, session_dir = session_dir, init_repos = init_repos,
      author = author, title = title, progress = new Console_Progress)
  })
}
