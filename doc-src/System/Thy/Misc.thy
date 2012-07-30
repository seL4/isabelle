theory Misc
imports Base
begin

chapter {* Miscellaneous tools \label{ch:tools} *}

text {*
  Subsequently we describe various Isabelle related utilities, given
  in alphabetical order.
*}


section {* Displaying documents *}

text {* The @{tool_def display} tool displays documents in DVI or PDF
  format:
\begin{ttbox}
Usage: isabelle display [OPTIONS] FILE

  Options are:
    -c           cleanup -- remove FILE after use

  Display document FILE (in DVI format).
\end{ttbox}

  \medskip The @{verbatim "-c"} option causes the input file to be
  removed after use.  The program for viewing @{verbatim dvi} files is
  determined by the @{setting DVI_VIEWER} setting.
*}


section {* Viewing documentation \label{sec:tool-doc} *}

text {*
  The @{tool_def doc} tool displays online documentation:
\begin{ttbox}
Usage: isabelle doc [DOC]

  View Isabelle documentation DOC, or show list of available documents.
\end{ttbox}
  If called without arguments, it lists all available documents. Each
  line starts with an identifier, followed by a short description. Any
  of these identifiers may be specified as the first argument in order
  to have the corresponding document displayed.

  \medskip The @{setting ISABELLE_DOCS} setting specifies the list of
  directories (separated by colons) to be scanned for documentations.
  The program for viewing @{verbatim dvi} files is determined by the
  @{setting DVI_VIEWER} setting.
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

text {*
  Get the ML system name and the location where the compiler binaries
  are supposed to reside as follows:
\begin{ttbox}
isabelle getenv ML_SYSTEM ML_HOME
{\out ML_SYSTEM=polyml}
{\out ML_HOME=/usr/share/polyml/x86-linux}
\end{ttbox}

  The next one peeks at the output directory for Isabelle logic
  images:
\begin{ttbox}
isabelle getenv -b ISABELLE_OUTPUT
{\out /home/me/isabelle/heaps/polyml_x86-linux}
\end{ttbox}
  Here we have used the @{verbatim "-b"} option to suppress the
  @{verbatim "ISABELLE_OUTPUT="} prefix.  The value above is what
  became of the following assignment in the default settings file:
\begin{ttbox}
ISABELLE_OUTPUT="\$ISABELLE_HOME_USER/heaps"
\end{ttbox}

  Note how the @{setting ML_IDENTIFIER} value got appended
  automatically to each path component. This is a special feature of
  @{setting ISABELLE_OUTPUT}.
*}


section {* Installing standalone Isabelle executables \label{sec:tool-install} *}

text {* By default, the main Isabelle binaries (@{executable
  "isabelle"} etc.)  are just run from their location within the
  distribution directory, probably indirectly by the shell through its
  @{setting PATH}.  Other schemes of installation are supported by the
  @{tool_def install} tool:
\begin{ttbox}
Usage: isabelle install [OPTIONS]

  Options are:
    -d DISTDIR   use DISTDIR as Isabelle distribution
                 (default ISABELLE_HOME)
    -p DIR       install standalone binaries in DIR

  Install Isabelle executables with absolute references to the current
  distribution directory.
\end{ttbox}

  The @{verbatim "-d"} option overrides the current Isabelle
  distribution directory as determined by @{setting ISABELLE_HOME}.

  The @{verbatim "-p"} option installs executable wrapper scripts for
  @{executable "isabelle-process"}, @{executable isabelle},
  @{executable Isabelle}, containing proper absolute references to the
  Isabelle distribution directory.  A typical @{verbatim DIR}
  specification would be some directory expected to be in the shell's
  @{setting PATH}, such as @{verbatim "/usr/local/bin"}.  It is
  important to note that a plain manual copy of the original Isabelle
  executables does not work, since it disrupts the integrity of the
  Isabelle distribution.
*}


section {* Creating instances of the Isabelle logo *}

text {* The @{tool_def logo} tool creates any instance of the generic
  Isabelle logo as an Encapsuled Postscript file (EPS):
\begin{ttbox}
Usage: isabelle logo [OPTIONS] NAME

  Create instance NAME of the Isabelle logo (as EPS).

  Options are:
    -o OUTFILE   set output file (default determined from NAME)
    -q           quiet mode
\end{ttbox}
  You are encouraged to use this to create a derived logo for your
  Isabelle project.  For example, @{tool logo}~@{verbatim Bali}
  creates @{verbatim isabelle_bali.eps}.  *}


section {* Isabelle's version of make \label{sec:tool-make} *}

text {* The @{tool_def make} tool is a very simple wrapper for
  ordinary Unix @{executable make}:
\begin{ttbox}
Usage: isabelle make [ARGS ...]

  Compile the logic in current directory using IsaMakefile.
  ARGS are directly passed to the system make program.
\end{ttbox}

  Note that the Isabelle settings environment is also active. Thus one
  may refer to its values within the @{verbatim IsaMakefile}, e.g.\
  @{verbatim "$(ISABELLE_OUTPUT)"}. Furthermore, programs started from
  the make file also inherit this environment.  Typically, @{verbatim
  IsaMakefile}s defer the real work to @{tool_ref usedir}.

  \medskip The basic @{verbatim IsaMakefile} convention is that the
  default target builds the actual logic, including its parents if
  appropriate.  The @{verbatim images} target is intended to build all
  local logic images, while the @{verbatim test} target shall build
  all related examples.  The @{verbatim all} target shall do
  @{verbatim images} and @{verbatim test}.
*}


subsubsection {* Examples *}

text {*
  Refer to the @{verbatim IsaMakefile}s of the Isabelle distribution's
  object-logics as a model for your own developments.  For example,
  see @{file "~~/src/FOL/IsaMakefile"}.
*}


section {* Make all logics *}

text {* The @{tool_def makeall} tool applies Isabelle make to any
  Isabelle component (cf.\ \secref{sec:components}) that contains an
  @{verbatim IsaMakefile}:
\begin{ttbox}
Usage: isabelle makeall [ARGS ...]

  Apply isabelle make to all components with IsaMakefile (passing ARGS).
\end{ttbox}

  The arguments @{verbatim ARGS} are just passed verbatim to each
  @{tool make} invocation.
*}


section {* Printing documents *}

text {*
  The @{tool_def print} tool prints documents:
\begin{ttbox}
Usage: isabelle print [OPTIONS] FILE

  Options are:
    -c           cleanup -- remove FILE after use

  Print document FILE.
\end{ttbox}

  The @{verbatim "-c"} option causes the input file to be removed
  after use.  The printer spool command is determined by the @{setting
  PRINT_COMMAND} setting.
*}


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