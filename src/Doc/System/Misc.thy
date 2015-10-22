theory Misc
imports Base
begin

chapter \<open>Miscellaneous tools \label{ch:tools}\<close>

text \<open>
  Subsequently we describe various Isabelle related utilities, given
  in alphabetical order.
\<close>


section \<open>Theory graph browser \label{sec:browse}\<close>

text \<open>The Isabelle graph browser is a general tool for visualizing
  dependency graphs.  Certain nodes of the graph (i.e.\ theories) can
  be grouped together in ``directories'', whose contents may be
  hidden, thus enabling the user to collapse irrelevant portions of
  information.  The browser is written in Java, it can be used both as
  a stand-alone application and as an applet.\<close>


subsection \<open>Invoking the graph browser\<close>

text \<open>The stand-alone version of the graph browser is wrapped up as
  @{tool_def browser}:
  @{verbatim [display]
\<open>Usage: isabelle browser [OPTIONS] [GRAPHFILE]

  Options are:
    -b           Admin/build only
    -c           cleanup -- remove GRAPHFILE after use
    -o FILE      output to FILE (ps, eps, pdf)\<close>}

  When no file name is specified, the browser automatically changes to
  the directory @{setting ISABELLE_BROWSER_INFO}.

  \<^medskip>
  The \<^verbatim>\<open>-b\<close> option indicates that this is for
  administrative build only, i.e.\ no browser popup if no files are
  given.

  The \<^verbatim>\<open>-c\<close> option causes the input file to be removed
  after use.

  The \<^verbatim>\<open>-o\<close> option indicates batch-mode operation, with the
  output written to the indicated file; note that \<^verbatim>\<open>pdf\<close>
  produces an \<^verbatim>\<open>eps\<close> copy as well.

  \<^medskip>
  The applet version of the browser is part of the standard
  WWW theory presentation, see the link ``theory dependencies'' within
  each session index.
\<close>


subsection \<open>Using the graph browser\<close>

text \<open>
  The browser's main window, which is shown in
  \figref{fig:browserwindow}, consists of two sub-windows.  In the
  left sub-window, the directory tree is displayed. The graph itself
  is displayed in the right sub-window.

  \begin{figure}[ht]
  \includegraphics[width=\textwidth]{browser_screenshot}
  \caption{\label{fig:browserwindow} Browser main window}
  \end{figure}
\<close>


subsubsection \<open>The directory tree window\<close>

text \<open>
  We describe the usage of the directory browser and the meaning of
  the different items in the browser window.

  \<^item> A red arrow before a directory name indicates that the
  directory is currently ``folded'', i.e.~the nodes in this directory
  are collapsed to one single node. In the right sub-window, the names
  of nodes corresponding to folded directories are enclosed in square
  brackets and displayed in red color.

  \<^item> A green downward arrow before a directory name indicates that
  the directory is currently ``unfolded''. It can be folded by
  clicking on the directory name.  Clicking on the name for a second
  time unfolds the directory again.  Alternatively, a directory can
  also be unfolded by clicking on the corresponding node in the right
  sub-window.

  \<^item> Blue arrows stand before ordinary node names. When clicking on
  such a name (i.e.\ that of a theory), the graph display window
  focuses to the corresponding node. Double clicking invokes a text
  viewer window in which the contents of the theory file are
  displayed.
\<close>


subsubsection \<open>The graph display window\<close>

text \<open>
  When pointing on an ordinary node, an upward and a downward arrow is
  shown.  Initially, both of these arrows are green. Clicking on the
  upward or downward arrow collapses all predecessor or successor
  nodes, respectively. The arrow's color then changes to red,
  indicating that the predecessor or successor nodes are currently
  collapsed. The node corresponding to the collapsed nodes has the
  name ``\<^verbatim>\<open>[....]\<close>''. To uncollapse the nodes again, simply
  click on the red arrow or on the node with the name ``\<^verbatim>\<open>[....]\<close>''.
  Similar to the directory browser, the contents of
  theory files can be displayed by double clicking on the
  corresponding node.
\<close>


subsubsection \<open>The ``File'' menu\<close>

text \<open>
  Due to Java Applet security restrictions this menu is only available
  in the full application version. The meaning of the menu items is as
  follows:

  \<^descr>[Open \dots] Open a new graph file.

  \<^descr>[Export to PostScript] Outputs the current graph in Postscript
  format, appropriately scaled to fit on one single sheet of A4 paper.
  The resulting file can be printed directly.

  \<^descr>[Export to EPS] Outputs the current graph in Encapsulated
  Postscript format. The resulting file can be included in other
  documents.

  \<^descr>[Quit] Quit the graph browser.
\<close>


subsection \<open>Syntax of graph definition files\<close>

text \<open>
  A graph definition file has the following syntax:

  \begin{center}\small
  \begin{tabular}{rcl}
    \<open>graph\<close> & \<open>=\<close> & \<open>{ vertex\<close>~\<^verbatim>\<open>;\<close>~\<open>}+\<close> \\
    \<open>vertex\<close> & \<open>=\<close> & \<open>vertex_name vertex_ID dir_name [\<close>~\<^verbatim>\<open>+\<close>~\<open>] path [\<close>~\<^verbatim>\<open><\<close>~\<open>|\<close>~\<^verbatim>\<open>>\<close>~\<open>] { vertex_ID }*\<close>
  \end{tabular}
  \end{center}

  The meaning of the items in a vertex description is as follows:

  \<^descr>[\<open>vertex_name\<close>] The name of the vertex.

  \<^descr>[\<open>vertex_ID\<close>] The vertex identifier. Note that there may
  be several vertices with equal names, whereas identifiers must be
  unique.

  \<^descr>[\<open>dir_name\<close>] The name of the ``directory'' the vertex
  should be placed in.  A ``\<^verbatim>\<open>+\<close>'' sign after \<open>dir_name\<close> indicates that the nodes in the directory are initially
  visible. Directories are initially invisible by default.

  \<^descr>[\<open>path\<close>] The path of the corresponding theory file. This
  is specified relatively to the path of the graph definition file.

  \<^descr>[List of successor/predecessor nodes] A ``\<^verbatim>\<open><\<close>''
  sign before the list means that successor nodes are listed, a
  ``\<^verbatim>\<open>>\<close>'' sign means that predecessor nodes are listed. If
  neither ``\<^verbatim>\<open><\<close>'' nor ``\<^verbatim>\<open>>\<close>'' is found, the
  browser assumes that successor nodes are listed.
\<close>


section \<open>Resolving Isabelle components \label{sec:tool-components}\<close>

text \<open>
  The @{tool_def components} tool resolves Isabelle components:
  @{verbatim [display]
\<open>Usage: isabelle components [OPTIONS] [COMPONENTS ...]

  Options are:
    -I           init user settings
    -R URL       component repository
                 (default $ISABELLE_COMPONENT_REPOSITORY)
    -a           resolve all missing components
    -l           list status

  Resolve Isabelle components via download and installation.
  COMPONENTS are identified via base name.

  ISABELLE_COMPONENT_REPOSITORY="http://isabelle.in.tum.de/components"\<close>}

  Components are initialized as described in \secref{sec:components}
  in a permissive manner, which can mark components as ``missing''.
  This state is amended by letting @{tool "components"} download and
  unpack components that are published on the default component
  repository @{url "http://isabelle.in.tum.de/components/"} in
  particular.

  Option \<^verbatim>\<open>-R\<close> specifies an alternative component
  repository.  Note that \<^verbatim>\<open>file:///\<close> URLs can be used for
  local directories.

  Option \<^verbatim>\<open>-a\<close> selects all missing components to be
  resolved.  Explicit components may be named as command
  line-arguments as well.  Note that components are uniquely
  identified by their base name, while the installation takes place in
  the location that was specified in the attempt to initialize the
  component before.

  Option \<^verbatim>\<open>-l\<close> lists the current state of available and
  missing components with their location (full name) within the
  file-system.

  Option \<^verbatim>\<open>-I\<close> initializes the user settings file to
  subscribe to the standard components specified in the Isabelle
  repository clone --- this does not make any sense for regular
  Isabelle releases.  If the file already exists, it needs to be
  edited manually according to the printed explanation.
\<close>


section \<open>Raw ML console\<close>

text \<open>
  The @{tool_def console} tool runs the Isabelle process with raw ML console:
  @{verbatim [display]
\<open>Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode for session image

  Run Isabelle process with raw ML console and line editor
  (default ISABELLE_LINE_EDITOR).\<close>}

  The \<^verbatim>\<open>-l\<close> option specifies the logic session name. By default,
  its heap image is checked and built on demand, but the option \<^verbatim>\<open>-n\<close> skips that.

  Options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-o\<close>, \<^verbatim>\<open>-s\<close> are passed
  directly to @{tool build} (\secref{sec:tool-build}).

  Options \<^verbatim>\<open>-m\<close>, \<^verbatim>\<open>-o\<close> are passed directly to the
  underlying Isabelle process (\secref{sec:isabelle-process}).

  The Isabelle process is run through the line editor that is specified via
  the settings variable @{setting ISABELLE_LINE_EDITOR} (e.g.\
  @{executable_def rlwrap} for GNU readline); the fall-back is to use plain
  standard input/output.

  Interaction works via the raw ML toplevel loop: this is neither
  Isabelle/Isar nor Isabelle/ML within the usual formal context. Some useful
  ML commands at this stage are @{ML cd}, @{ML pwd}, @{ML use}, @{ML use_thy},
  @{ML use_thys}.
\<close>


section \<open>Displaying documents \label{sec:tool-display}\<close>

text \<open>The @{tool_def display} tool displays documents in DVI or PDF
  format:
  @{verbatim [display]
\<open>Usage: isabelle display DOCUMENT

  Display DOCUMENT (in DVI or PDF format).\<close>}

  \<^medskip>
  The settings @{setting DVI_VIEWER} and @{setting
  PDF_VIEWER} determine the programs for viewing the corresponding
  file formats.  Normally this opens the document via the desktop
  environment, potentially in an asynchronous manner with re-use of
  previews views.
\<close>


section \<open>Viewing documentation \label{sec:tool-doc}\<close>

text \<open>
  The @{tool_def doc} tool displays Isabelle documentation:
  @{verbatim [display]
\<open>Usage: isabelle doc [DOC ...]

  View Isabelle documentation.\<close>}

  If called without arguments, it lists all available documents. Each
  line starts with an identifier, followed by a short description. Any
  of these identifiers may be specified as arguments, in order to
  display the corresponding document (see also
  \secref{sec:tool-display}).

  \<^medskip>
  The @{setting ISABELLE_DOCS} setting specifies the list of
  directories (separated by colons) to be scanned for documentations.
\<close>


section \<open>Shell commands within the settings environment \label{sec:tool-env}\<close>

text \<open>The @{tool_def env} tool is a direct wrapper for the standard
  \<^verbatim>\<open>/usr/bin/env\<close> command on POSIX systems, running within
  the Isabelle settings environment (\secref{sec:settings}).

  The command-line arguments are that of the underlying version of
  \<^verbatim>\<open>env\<close>.  For example, the following invokes an instance of
  the GNU Bash shell within the Isabelle environment:
  @{verbatim [display] \<open>isabelle env bash\<close>}
\<close>


section \<open>Inspecting the settings environment \label{sec:tool-getenv}\<close>

text \<open>The Isabelle settings environment --- as provided by the
  site-default and user-specific settings files --- can be inspected
  with the @{tool_def getenv} tool:
  @{verbatim [display]
\<open>Usage: isabelle getenv [OPTIONS] [VARNAMES ...]

  Options are:
    -a           display complete environment
    -b           print values only (doesn't work for -a)
    -d FILE      dump complete environment to FILE
                 (null terminated entries)

  Get value of VARNAMES from the Isabelle settings.\<close>}

  With the \<^verbatim>\<open>-a\<close> option, one may inspect the full process
  environment that Isabelle related programs are run in. This usually
  contains much more variables than are actually Isabelle settings.
  Normally, output is a list of lines of the form \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close>. The \<^verbatim>\<open>-b\<close> option
  causes only the values to be printed.

  Option \<^verbatim>\<open>-d\<close> produces a dump of the complete environment
  to the specified file.  Entries are terminated by the ASCII null
  character, i.e.\ the C string terminator.
\<close>


subsubsection \<open>Examples\<close>

text \<open>Get the location of @{setting ISABELLE_HOME_USER} where
  user-specific information is stored:
  @{verbatim [display] \<open>isabelle getenv ISABELLE_HOME_USER\<close>}

  \<^medskip>
  Get the value only of the same settings variable, which is
  particularly useful in shell scripts:
  @{verbatim [display] \<open>isabelle getenv -b ISABELLE_OUTPUT\<close>}
\<close>


section \<open>Installing standalone Isabelle executables \label{sec:tool-install}\<close>

text \<open>By default, the main Isabelle binaries (@{executable
  "isabelle"} etc.)  are just run from their location within the
  distribution directory, probably indirectly by the shell through its
  @{setting PATH}.  Other schemes of installation are supported by the
  @{tool_def install} tool:
  @{verbatim [display]
\<open>Usage: isabelle install [OPTIONS] BINDIR

  Options are:
    -d DISTDIR   refer to DISTDIR as Isabelle distribution
                 (default ISABELLE_HOME)

  Install Isabelle executables with absolute references to the
  distribution directory.\<close>}

  The \<^verbatim>\<open>-d\<close> option overrides the current Isabelle
  distribution directory as determined by @{setting ISABELLE_HOME}.

  The \<open>BINDIR\<close> argument tells where executable wrapper scripts
  for @{executable "isabelle_process"} and @{executable isabelle}
  should be placed, which is typically a directory in the shell's
  @{setting PATH}, such as \<^verbatim>\<open>$HOME/bin\<close>.

  \<^medskip>
  It is also possible to make symbolic links of the main
  Isabelle executables manually, but making separate copies outside
  the Isabelle distribution directory will not work!\<close>


section \<open>Creating instances of the Isabelle logo\<close>

text \<open>The @{tool_def logo} tool creates instances of the generic
  Isabelle logo as EPS and PDF, for inclusion in {\LaTeX} documents.
  @{verbatim [display]
\<open>Usage: isabelle logo [OPTIONS] XYZ

  Create instance XYZ of the Isabelle logo (as EPS and PDF).

  Options are:
    -n NAME      alternative output base name (default "isabelle_xyx")
    -q           quiet mode\<close>}

  Option \<^verbatim>\<open>-n\<close> specifies an alternative (base) name for the
  generated files.  The default is \<^verbatim>\<open>isabelle_\<close>\<open>xyz\<close>
  in lower-case.

  Option \<^verbatim>\<open>-q\<close> omits printing of the result file name.

  \<^medskip>
  Implementors of Isabelle tools and applications are
  encouraged to make derived Isabelle logos for their own projects
  using this template.\<close>


section \<open>Output the version identifier of the Isabelle distribution\<close>

text \<open>
  The @{tool_def version} tool displays Isabelle version information:
  @{verbatim [display]
\<open>Usage: isabelle version [OPTIONS]

  Options are:
    -i           short identification (derived from Mercurial id)

  Display Isabelle version information.\<close>}

  \<^medskip>
  The default is to output the full version string of the
  Isabelle distribution, e.g.\ ``\<^verbatim>\<open>Isabelle2012: May 2012\<close>.

  The \<^verbatim>\<open>-i\<close> option produces a short identification derived
  from the Mercurial id of the @{setting ISABELLE_HOME} directory.
\<close>


section \<open>Convert XML to YXML\<close>

text \<open>
  The @{tool_def yxml} tool converts a standard XML document (stdin)
  to the much simpler and more efficient YXML format of Isabelle
  (stdout).  The YXML format is defined as follows.

  \<^enum> The encoding is always UTF-8.

  \<^enum> Body text is represented verbatim (no escaping, no special
  treatment of white space, no named entities, no CDATA chunks, no
  comments).

  \<^enum> Markup elements are represented via ASCII control characters
  \<open>\<^bold>X = 5\<close> and \<open>\<^bold>Y = 6\<close> as follows:

  \begin{tabular}{ll}
    XML & YXML \\\hline
    \<^verbatim>\<open><\<close>\<open>name attribute\<close>\<^verbatim>\<open>=\<close>\<open>value \<dots>\<close>\<^verbatim>\<open>>\<close> &
    \<open>\<^bold>X\<^bold>Yname\<^bold>Yattribute\<close>\<^verbatim>\<open>=\<close>\<open>value\<dots>\<^bold>X\<close> \\
    \<^verbatim>\<open></\<close>\<open>name\<close>\<^verbatim>\<open>>\<close> & \<open>\<^bold>X\<^bold>Y\<^bold>X\<close> \\
  \end{tabular}

  There is no special case for empty body text, i.e.\ \<^verbatim>\<open><foo/>\<close>
  is treated like \<^verbatim>\<open><foo></foo>\<close>.  Also note that
  \<open>\<^bold>X\<close> and \<open>\<^bold>Y\<close> may never occur in
  well-formed XML documents.


  Parsing YXML is pretty straight-forward: split the text into chunks
  separated by \<open>\<^bold>X\<close>, then split each chunk into
  sub-chunks separated by \<open>\<^bold>Y\<close>.  Markup chunks start
  with an empty sub-chunk, and a second empty sub-chunk indicates
  close of an element.  Any other non-empty chunk consists of plain
  text.  For example, see @{file "~~/src/Pure/PIDE/yxml.ML"} or
  @{file "~~/src/Pure/PIDE/yxml.scala"}.

  YXML documents may be detected quickly by checking that the first
  two characters are \<open>\<^bold>X\<^bold>Y\<close>.
\<close>

end