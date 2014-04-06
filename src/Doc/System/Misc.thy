theory Misc
imports Base
begin

chapter {* Miscellaneous tools \label{ch:tools} *}

text {*
  Subsequently we describe various Isabelle related utilities, given
  in alphabetical order.
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


section {* Getting logic images *}

text {* The @{tool_def findlogics} tool traverses all directories
  specified in @{setting ISABELLE_PATH}, looking for Isabelle logic
  images. Its usage is:
\begin{ttbox}
Usage: isabelle findlogics

  Collect heap file names from ISABELLE_PATH.
\end{ttbox}

  The base names of all files found on the path are printed --- sorted
  and with duplicates removed. Also note that lookup in @{setting
  ISABELLE_PATH} includes the current values of @{setting ML_SYSTEM}
  and @{setting ML_PLATFORM}. Thus switching to another ML compiler
  may change the set of logic images available.
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


section {* Remove awkward symbol names from theory sources *}

text {*
  The @{tool_def unsymbolize} tool tunes Isabelle theory sources to
  improve readability for plain ASCII output (e.g.\ in email
  communication).  Most notably, @{tool unsymbolize} replaces awkward
  arrow symbols such as @{verbatim "\\"}@{verbatim "<Longrightarrow>"}
  by @{verbatim "==>"}.
\begin{ttbox}
Usage: isabelle unsymbolize [FILES|DIRS...]

  Recursively find .thy/.ML files, removing unreadable symbol names.
  Note: this is an ad-hoc script; there is no systematic way to replace
  symbols independently of the inner syntax of a theory!

  Renames old versions of FILES by appending "~~".
\end{ttbox}
*}


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