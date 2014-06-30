theory Misc
imports Base
begin

chapter {* Miscellaneous tools \label{ch:tools} *}

text {*
  Subsequently we describe various Isabelle related utilities, given
  in alphabetical order.
*}


section {* Theory graph browser \label{sec:browse} *}

text {* The Isabelle graph browser is a general tool for visualizing
  dependency graphs.  Certain nodes of the graph (i.e.\ theories) can
  be grouped together in ``directories'', whose contents may be
  hidden, thus enabling the user to collapse irrelevant portions of
  information.  The browser is written in Java, it can be used both as
  a stand-alone application and as an applet.  *}


subsection {* Invoking the graph browser *}

text {* The stand-alone version of the graph browser is wrapped up as
  @{tool_def browser}:
\begin{ttbox}
Usage: isabelle browser [OPTIONS] [GRAPHFILE]

  Options are:
    -b           Admin/build only
    -c           cleanup -- remove GRAPHFILE after use
    -o FILE      output to FILE (ps, eps, pdf)
\end{ttbox}
  When no file name is specified, the browser automatically changes to
  the directory @{setting ISABELLE_BROWSER_INFO}.

  \medskip The @{verbatim "-b"} option indicates that this is for
  administrative build only, i.e.\ no browser popup if no files are
  given.

  The @{verbatim "-c"} option causes the input file to be removed
  after use.

  The @{verbatim "-o"} option indicates batch-mode operation, with the
  output written to the indicated file; note that @{verbatim pdf}
  produces an @{verbatim eps} copy as well.

  \medskip The applet version of the browser is part of the standard
  WWW theory presentation, see the link ``theory dependencies'' within
  each session index.
*}


subsection {* Using the graph browser *}

text {*
  The browser's main window, which is shown in
  \figref{fig:browserwindow}, consists of two sub-windows.  In the
  left sub-window, the directory tree is displayed. The graph itself
  is displayed in the right sub-window.

  \begin{figure}[ht]
  \includegraphics[width=\textwidth]{browser_screenshot}
  \caption{\label{fig:browserwindow} Browser main window}
  \end{figure}
*}


subsubsection {* The directory tree window *}

text {*
  We describe the usage of the directory browser and the meaning of
  the different items in the browser window.

  \begin{itemize}

  \item A red arrow before a directory name indicates that the
  directory is currently ``folded'', i.e.~the nodes in this directory
  are collapsed to one single node. In the right sub-window, the names
  of nodes corresponding to folded directories are enclosed in square
  brackets and displayed in red color.

  \item A green downward arrow before a directory name indicates that
  the directory is currently ``unfolded''. It can be folded by
  clicking on the directory name.  Clicking on the name for a second
  time unfolds the directory again.  Alternatively, a directory can
  also be unfolded by clicking on the corresponding node in the right
  sub-window.

  \item Blue arrows stand before ordinary node names. When clicking on
  such a name (i.e.\ that of a theory), the graph display window
  focuses to the corresponding node. Double clicking invokes a text
  viewer window in which the contents of the theory file are
  displayed.

  \end{itemize}
*}


subsubsection {* The graph display window *}

text {*
  When pointing on an ordinary node, an upward and a downward arrow is
  shown.  Initially, both of these arrows are green. Clicking on the
  upward or downward arrow collapses all predecessor or successor
  nodes, respectively. The arrow's color then changes to red,
  indicating that the predecessor or successor nodes are currently
  collapsed. The node corresponding to the collapsed nodes has the
  name ``@{verbatim "[....]"}''. To uncollapse the nodes again, simply
  click on the red arrow or on the node with the name ``@{verbatim
  "[....]"}''. Similar to the directory browser, the contents of
  theory files can be displayed by double clicking on the
  corresponding node.
*}


subsubsection {* The ``File'' menu *}

text {*
  Due to Java Applet security restrictions this menu is only available
  in the full application version. The meaning of the menu items is as
  follows:

  \begin{description}

  \item[Open \dots] Open a new graph file.

  \item[Export to PostScript] Outputs the current graph in Postscript
  format, appropriately scaled to fit on one single sheet of A4 paper.
  The resulting file can be printed directly.

  \item[Export to EPS] Outputs the current graph in Encapsulated
  Postscript format. The resulting file can be included in other
  documents.

  \item[Quit] Quit the graph browser.

  \end{description}
*}


subsection {* Syntax of graph definition files *}

text {*
  A graph definition file has the following syntax:

  \begin{center}\small
  \begin{tabular}{rcl}
    @{text graph} & @{text "="} & @{text "{ vertex"}~@{verbatim ";"}~@{text "}+"} \\
    @{text vertex} & @{text "="} & @{text "vertex_name vertex_ID dir_name ["}~@{verbatim "+"}~@{text "] path ["}~@{verbatim "<"}~@{text "|"}~@{verbatim ">"}~@{text "] { vertex_ID }*"}
  \end{tabular}
  \end{center}

  The meaning of the items in a vertex description is as follows:

  \begin{description}

  \item[@{text vertex_name}] The name of the vertex.

  \item[@{text vertex_ID}] The vertex identifier. Note that there may
  be several vertices with equal names, whereas identifiers must be
  unique.

  \item[@{text dir_name}] The name of the ``directory'' the vertex
  should be placed in.  A ``@{verbatim "+"}'' sign after @{text
  dir_name} indicates that the nodes in the directory are initially
  visible. Directories are initially invisible by default.

  \item[@{text path}] The path of the corresponding theory file. This
  is specified relatively to the path of the graph definition file.

  \item[List of successor/predecessor nodes] A ``@{verbatim "<"}''
  sign before the list means that successor nodes are listed, a
  ``@{verbatim ">"}'' sign means that predecessor nodes are listed. If
  neither ``@{verbatim "<"}'' nor ``@{verbatim ">"}'' is found, the
  browser assumes that successor nodes are listed.

  \end{description}
*}


section {* Resolving Isabelle components \label{sec:tool-components} *}

text {*
  The @{tool_def components} tool resolves Isabelle components:
\begin{ttbox}
Usage: isabelle components [OPTIONS] [COMPONENTS ...]

  Options are:
    -I           init user settings
    -R URL       component repository
                 (default $ISABELLE_COMPONENT_REPOSITORY)
    -a           resolve all missing components
    -l           list status

  Resolve Isabelle components via download and installation.
  COMPONENTS are identified via base name.

  ISABELLE_COMPONENT_REPOSITORY="http://isabelle.in.tum.de/components"
\end{ttbox}

  Components are initialized as described in \secref{sec:components}
  in a permissive manner, which can mark components as ``missing''.
  This state is amended by letting @{tool "components"} download and
  unpack components that are published on the default component
  repository @{url "http://isabelle.in.tum.de/components/"} in
  particular.

  Option @{verbatim "-R"} specifies an alternative component
  repository.  Note that @{verbatim "file:///"} URLs can be used for
  local directories.

  Option @{verbatim "-a"} selects all missing components to be
  resolved.  Explicit components may be named as command
  line-arguments as well.  Note that components are uniquely
  identified by their base name, while the installation takes place in
  the location that was specified in the attempt to initialize the
  component before.

  Option @{verbatim "-l"} lists the current state of available and
  missing components with their location (full name) within the
  file-system.

  Option @{verbatim "-I"} initializes the user settings file to
  subscribe to the standard components specified in the Isabelle
  repository clone --- this does not make any sense for regular
  Isabelle releases.  If the file already exists, it needs to be
  edited manually according to the printed explanation.
*}


section {* Raw ML console *}

text {*
  The @{tool_def console} tool runs the Isabelle process with raw ML console:
\begin{ttbox}
Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode for session image

  Run Isabelle process with raw ML console and line editor
  (default ISABELLE_LINE_EDITOR).
\end{ttbox}

  The @{verbatim "-l"} option specifies the logic session name. By default,
  its heap image is checked and built on demand, but the option @{verbatim
  "-n"} skips that.

  Options @{verbatim "-d"}, @{verbatim "-o"}, @{verbatim "-s"} are passed
  directly to @{tool build} (\secref{sec:tool-build}).

  Options @{verbatim "-m"}, @{verbatim "-o"} are passed directly to the
  underlying Isabelle process (\secref{sec:isabelle-process}).

  The Isabelle process is run through the line editor that is specified via
  the settings variable @{setting ISABELLE_LINE_EDITOR} (e.g.\
  @{executable_def rlwrap} for GNU readline); the fall-back is to use plain
  standard input/output.

  Interaction works via the raw ML toplevel loop: this is neither
  Isabelle/Isar nor Isabelle/ML within the usual formal context. Some useful
  ML commands at this stage are @{ML cd}, @{ML pwd}, @{ML use}, @{ML use_thy},
  @{ML use_thys}.
*}


section {* Displaying documents \label{sec:tool-display} *}

text {* The @{tool_def display} tool displays documents in DVI or PDF
  format:
\begin{ttbox}
Usage: isabelle display DOCUMENT

  Display DOCUMENT (in DVI or PDF format).
\end{ttbox}

  \medskip The settings @{setting DVI_VIEWER} and @{setting
  PDF_VIEWER} determine the programs for viewing the corresponding
  file formats.  Normally this opens the document via the desktop
  environment, potentially in an asynchronous manner with re-use of
  previews views.
*}


section {* Viewing documentation \label{sec:tool-doc} *}

text {*
  The @{tool_def doc} tool displays Isabelle documentation:
\begin{ttbox}
Usage: isabelle doc [DOC ...]

  View Isabelle documentation.
\end{ttbox}
  If called without arguments, it lists all available documents. Each
  line starts with an identifier, followed by a short description. Any
  of these identifiers may be specified as arguments, in order to
  display the corresponding document (see also
  \secref{sec:tool-display}).

  \medskip The @{setting ISABELLE_DOCS} setting specifies the list of
  directories (separated by colons) to be scanned for documentations.
*}


section {* Proof General / Emacs *}

text {* The @{tool_def emacs} tool invokes a version of Emacs and
  Proof General\footnote{@{url "http://proofgeneral.inf.ed.ac.uk/"}} within the
  regular Isabelle settings environment (\secref{sec:settings}).  This
  is more convenient than starting Emacs separately, loading the Proof
  General LISP files, and then attempting to start Isabelle with
  dynamic @{setting PATH} lookup etc., although it might fail if a
  different version of Proof General is already part of the Emacs
  installation of the operating system.

  The actual interface script is part of the Proof General
  distribution; its usage depends on the particular version.  There
  are some options available, such as @{verbatim "-l"} for passing the
  logic image to be used by default, or @{verbatim "-m"} to tune the
  standard print mode of the prover process.  The following Isabelle
  settings are particularly important for Proof General:

  \begin{description}

  \item[@{setting_def PROOFGENERAL_HOME}] points to the main
  installation directory of the Proof General distribution.  This is
  implicitly provided for versions of Proof General that are
  distributed as Isabelle component, see also \secref{sec:components};
  otherwise it needs to be configured manually.

  \item[@{setting_def PROOFGENERAL_OPTIONS}] is implicitly prefixed to
  the command line of any invocation of the Proof General @{verbatim
  interface} script.  This allows to provide persistent default
  options for the invocation of \texttt{isabelle emacs}.

  \end{description}
*}


section {* Shell commands within the settings environment \label{sec:tool-env} *}

text {* The @{tool_def env} tool is a direct wrapper for the standard
  @{verbatim "/usr/bin/env"} command on POSIX systems, running within
  the Isabelle settings environment (\secref{sec:settings}).

  The command-line arguments are that of the underlying version of
  @{verbatim env}.  For example, the following invokes an instance of
  the GNU Bash shell within the Isabelle environment:
\begin{alltt}
  isabelle env bash
\end{alltt}
*}


section {* Inspecting the settings environment \label{sec:tool-getenv} *}

text {* The Isabelle settings environment --- as provided by the
  site-default and user-specific settings files --- can be inspected
  with the @{tool_def getenv} tool:
\begin{ttbox}
Usage: isabelle getenv [OPTIONS] [VARNAMES ...]

  Options are:
    -a           display complete environment
    -b           print values only (doesn't work for -a)
    -d FILE      dump complete environment to FILE
                 (null terminated entries)

  Get value of VARNAMES from the Isabelle settings.
\end{ttbox}

  With the @{verbatim "-a"} option, one may inspect the full process
  environment that Isabelle related programs are run in. This usually
  contains much more variables than are actually Isabelle settings.
  Normally, output is a list of lines of the form @{text
  name}@{verbatim "="}@{text value}. The @{verbatim "-b"} option
  causes only the values to be printed.

  Option @{verbatim "-d"} produces a dump of the complete environment
  to the specified file.  Entries are terminated by the ASCII null
  character, i.e.\ the C string terminator.
*}


subsubsection {* Examples *}

text {* Get the location of @{setting ISABELLE_HOME_USER} where
  user-specific information is stored:
\begin{ttbox}
isabelle getenv ISABELLE_HOME_USER
\end{ttbox}

  \medskip Get the value only of the same settings variable, which is
particularly useful in shell scripts:
\begin{ttbox}
isabelle getenv -b ISABELLE_OUTPUT
\end{ttbox}
*}


section {* Installing standalone Isabelle executables \label{sec:tool-install} *}

text {* By default, the main Isabelle binaries (@{executable
  "isabelle"} etc.)  are just run from their location within the
  distribution directory, probably indirectly by the shell through its
  @{setting PATH}.  Other schemes of installation are supported by the
  @{tool_def install} tool:
\begin{ttbox}
Usage: isabelle install [OPTIONS] BINDIR

  Options are:
    -d DISTDIR   refer to DISTDIR as Isabelle distribution
                 (default ISABELLE_HOME)

  Install Isabelle executables with absolute references to the
  distribution directory.
\end{ttbox}

  The @{verbatim "-d"} option overrides the current Isabelle
  distribution directory as determined by @{setting ISABELLE_HOME}.

  The @{text BINDIR} argument tells where executable wrapper scripts
  for @{executable "isabelle_process"} and @{executable isabelle}
  should be placed, which is typically a directory in the shell's
  @{setting PATH}, such as @{verbatim "$HOME/bin"}.

  \medskip It is also possible to make symbolic links of the main
  Isabelle executables manually, but making separate copies outside
  the Isabelle distribution directory will not work!  *}


section {* Creating instances of the Isabelle logo *}

text {* The @{tool_def logo} tool creates instances of the generic
  Isabelle logo as EPS and PDF, for inclusion in {\LaTeX} documents.
\begin{ttbox}
Usage: isabelle logo [OPTIONS] XYZ

  Create instance XYZ of the Isabelle logo (as EPS and PDF).

  Options are:
    -n NAME      alternative output base name (default "isabelle_xyx")
    -q           quiet mode
\end{ttbox}

  Option @{verbatim "-n"} specifies an altenative (base) name for the
  generated files.  The default is @{verbatim "isabelle_"}@{text xyz}
  in lower-case.

  Option @{verbatim "-q"} omits printing of the result file name.

  \medskip Implementors of Isabelle tools and applications are
  encouraged to make derived Isabelle logos for their own projects
  using this template.  *}


section {* Output the version identifier of the Isabelle distribution *}

text {*
  The @{tool_def version} tool displays Isabelle version information:
\begin{ttbox}
Usage: isabelle version [OPTIONS]

  Options are:
    -i           short identification (derived from Mercurial id)

  Display Isabelle version information.
\end{ttbox}

  \medskip The default is to output the full version string of the
  Isabelle distribution, e.g.\ ``@{verbatim "Isabelle2012: May 2012"}.

  The @{verbatim "-i"} option produces a short identification derived
  from the Mercurial id of the @{setting ISABELLE_HOME} directory.
*}


section {* Convert XML to YXML *}

text {*
  The @{tool_def yxml} tool converts a standard XML document (stdin)
  to the much simpler and more efficient YXML format of Isabelle
  (stdout).  The YXML format is defined as follows.

  \begin{enumerate}

  \item The encoding is always UTF-8.

  \item Body text is represented verbatim (no escaping, no special
  treatment of white space, no named entities, no CDATA chunks, no
  comments).

  \item Markup elements are represented via ASCII control characters
  @{text "\<^bold>X = 5"} and @{text "\<^bold>Y = 6"} as follows:

  \begin{tabular}{ll}
    XML & YXML \\\hline
    @{verbatim "<"}@{text "name attribute"}@{verbatim "="}@{text "value \<dots>"}@{verbatim ">"} &
    @{text "\<^bold>X\<^bold>Yname\<^bold>Yattribute"}@{verbatim "="}@{text "value\<dots>\<^bold>X"} \\
    @{verbatim "</"}@{text name}@{verbatim ">"} & @{text "\<^bold>X\<^bold>Y\<^bold>X"} \\
  \end{tabular}

  There is no special case for empty body text, i.e.\ @{verbatim
  "<foo/>"} is treated like @{verbatim "<foo></foo>"}.  Also note that
  @{text "\<^bold>X"} and @{text "\<^bold>Y"} may never occur in
  well-formed XML documents.

  \end{enumerate}

  Parsing YXML is pretty straight-forward: split the text into chunks
  separated by @{text "\<^bold>X"}, then split each chunk into
  sub-chunks separated by @{text "\<^bold>Y"}.  Markup chunks start
  with an empty sub-chunk, and a second empty sub-chunk indicates
  close of an element.  Any other non-empty chunk consists of plain
  text.  For example, see @{file "~~/src/Pure/PIDE/yxml.ML"} or
  @{file "~~/src/Pure/PIDE/yxml.scala"}.

  YXML documents may be detected quickly by checking that the first
  two characters are @{text "\<^bold>X\<^bold>Y"}.
*}

end