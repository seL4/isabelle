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
    document: Boolean = false,
    title: String = "",
    author: String = "",
    progress: Progress = No_Progress)
  {
    Isabelle_System.mkdirs(session_dir)

    val name = proper_string(session_name) getOrElse session_dir.absolute_file.getName
    val parent = proper_string(session_parent) getOrElse Isabelle_System.getenv("ISABELLE_LOGIC")

    val root_path = session_dir + Path.explode("ROOT")
    if (root_path.file.exists) error("Cannot overwrite existing " + root_path)

    val document_path = session_dir + Path.explode("document")
    if (document && document_path.file.exists) error("Cannot overwrite existing " + document_path)

    progress.echo("\nPreparing session " + quote(name) + " in " + session_dir)


    /* ROOT */

    progress.echo("  creating " + root_path)

    File.write(root_path,
      "session " + root_name(name) + " = " + root_name(parent) + " +" +
      (if (document) """
  options [document = pdf, document_output = "output"]
  theories [document = false]
    (* Foo *)
    (* Bar *)
  theories
    (* Baz *)
  document_files
    "root.tex"
"""
      else """
  options [document = false]
  theories
    (* Foo *)
    (* Bar *)
    (* Baz *)
"""))


    /* document directory */

    if (document) {
      val root_tex = session_dir + Path.explode("document/root.tex")
      progress.echo("  creating " + root_tex)

      Isabelle_System.mkdirs(root_tex.dir)

      File.write(root_tex,
"""\documentclass[11pt,a4paper]{article}
\""" + """usepackage{isabelle,isabellesym}

% further packages required for unusual symbols (see also
% isabellesym.sty), use only when needed

%\""" + """usepackage{amssymb}
  %for \<leadsto>, \<box>, \<diamond>, \<sqsupset>, \<mho>, \<Join>,
  %\<lhd>, \<lesssim>, \<greatersim>, \<lessapprox>, \<greaterapprox>,
  %\<triangleq>, \<yen>, \<lozenge>

%\""" + """usepackage{eurosym}
  %for \<euro>

%\""" + """usepackage[only,bigsqcap]{stmaryrd}
  %for \<Sqinter>

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
\author{""" +
  (proper_string(author) getOrElse ("By " + latex_name(Isabelle_System.getenv("USER")))) + """}
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

  val isabelle_tool = Isabelle_Tool("mkroot", "prepare session root directory", args =>
  {
    var document = false
    var session_name = ""

    val getopts = Getopts("""
Usage: isabelle mkroot [OPTIONS] [DIR]

  Options are:
    -d           enable document preparation
    -n NAME      alternative session name (default: DIR base name)

  Prepare session root DIR (default: current directory).
""",
      "d" -> (_ => document = true),
      "n:" -> (arg => session_name = arg))

    val more_args = getopts(args)

    val session_dir =
      more_args match {
        case Nil => Path.current
        case List(dir) => Path.explode(dir)
        case _ => getopts.usage()
      }

    mkroot(session_name = session_name, session_dir = session_dir, document = document,
      progress = new Console_Progress)
  })
}
