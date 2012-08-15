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


section {* Isabelle wrapper for make \label{sec:tool-make} *}

text {* The old @{tool_def make} tool is a very simple wrapper for
  ordinary Unix @{executable make}:
\begin{ttbox}
Usage: isabelle make [ARGS ...]

  Compile the logic in current directory using IsaMakefile.
  ARGS are directly passed to the system make program.
\end{ttbox}

  Note that the Isabelle settings environment is also active. Thus one
  may refer to its values within the @{verbatim IsaMakefile}, e.g.\
  @{verbatim "$(ISABELLE_HOME)"}. Furthermore, programs started from
  the make file also inherit this environment.
*}


section {* Creating Isabelle session directories
  \label{sec:tool-mkdir} *}

text {* The old @{tool_def mkdir} tool prepares Isabelle session
  source directories, including a sensible default setup of @{verbatim
  IsaMakefile}, @{verbatim ROOT.ML}, and a @{verbatim document}
  directory with a minimal @{verbatim root.tex} that is sufficient to
  print all theories of the session (in the order of appearance); see
  \secref{sec:tool-document} for further information on Isabelle
  document preparation.  The usage of @{tool mkdir} is:

\begin{ttbox}
Usage: isabelle mkdir [OPTIONS] [LOGIC] NAME

  Options are:
    -I FILE      alternative IsaMakefile output
    -P           include parent logic target
    -b           setup build mode (session outputs heap image)
    -q           quiet mode

  Prepare session directory, including IsaMakefile and document source,
  with parent LOGIC (default ISABELLE_LOGIC=\$ISABELLE_LOGIC)
\end{ttbox}

  The @{tool mkdir} tool is conservative in the sense that any
  existing @{verbatim IsaMakefile} etc.\ is left unchanged.  Thus it
  is safe to invoke it multiple times, although later runs may not
  have the desired effect.

  Note that @{tool mkdir} is unable to change @{verbatim IsaMakefile}
  incrementally --- manual changes are required for multiple
  sub-sessions.  On order to get an initial working session, the only
  editing needed is to add appropriate @{ML use_thy} calls to the
  generated @{verbatim ROOT.ML} file.
*}


subsubsection {* Options *}

text {*
  The @{verbatim "-I"} option specifies an alternative to @{verbatim
  IsaMakefile} for dependencies.  Note that ``@{verbatim "-"}'' refers
  to \emph{stdout}, i.e.\ ``@{verbatim "-I-"}'' provides an easy way
  to peek at @{tool mkdir}'s idea of @{tool make} setup required for
  some particular of Isabelle session.

  \medskip The @{verbatim "-P"} option includes a target for the
  parent @{verbatim LOGIC} session in the generated @{verbatim
  IsaMakefile}.  The corresponding sources are assumed to be located
  within the Isabelle distribution.

  \medskip The @{verbatim "-b"} option sets up the current directory
  as the base for a new session that provides an actual logic image,
  as opposed to one that only runs several theories based on an
  existing image.  Note that in the latter case, everything except
  @{verbatim IsaMakefile} would be placed into a separate directory
  @{verbatim NAME}, rather than the current one.  See
  \secref{sec:tool-usedir} for further information on \emph{build
  mode} vs.\ \emph{example mode} of @{tool usedir}.

  \medskip The @{verbatim "-q"} option enables quiet mode, suppressing
  further notes on how to proceed.
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


section {* Running Isabelle sessions \label{sec:tool-usedir} *}

text {* The old @{tool_def usedir} tool builds object-logic images, or
  runs example sessions based on existing logics. Its usage is:
\begin{ttbox}
Usage: isabelle usedir [OPTIONS] LOGIC NAME

  Options are:
    -C BOOL      copy existing document directory to -D PATH (default true)
    -D PATH      dump generated document sources into PATH
    -M MAX       multithreading: maximum number of worker threads (default 1)
    -P PATH      set path for remote theory browsing information
    -Q INT       set threshold for sub-proof parallelization (default 50)
    -T LEVEL     multithreading: trace level (default 0)
    -V VARIANT   declare alternative document VARIANT
    -b           build mode (output heap image, using current dir)
    -d FORMAT    build document as FORMAT (default false)
    -f NAME      use ML file NAME (default ROOT.ML)
    -g BOOL      generate session graph image for document (default false)
    -i BOOL      generate theory browser information (default false)
    -m MODE      add print mode for output
    -p LEVEL     set level of detail for proof objects (default 0)
    -q LEVEL     set level of parallel proof checking (default 1)
    -r           reset session path
    -s NAME      override session NAME
    -t BOOL      internal session timing (default false)
    -v BOOL      be verbose (default false)

  Build object-logic or run examples. Also creates browsing
  information (HTML etc.) according to settings.

  ISABELLE_USEDIR_OPTIONS=...

  ML_PLATFORM=...
  ML_HOME=...
  ML_SYSTEM=...
  ML_OPTIONS=...
\end{ttbox}

  Note that the value of the @{setting_ref ISABELLE_USEDIR_OPTIONS}
  setting is implicitly prefixed to \emph{any} @{tool usedir}
  call. Since the @{verbatim IsaMakefile}s of all object-logics
  distributed with Isabelle just invoke @{tool usedir} for the real
  work, one may control compilation options globally via above
  variable. In particular, generation of \rmindex{HTML} browsing
  information and document preparation is controlled here.
*}


subsubsection {* Options *}

text {*
  Basically, there are two different modes of operation: \emph{build
  mode} (enabled through the @{verbatim "-b"} option) and
  \emph{example mode} (default).

  Calling @{tool usedir} with @{verbatim "-b"} runs @{executable
  "isabelle-process"} with input image @{verbatim LOGIC} and output to
  @{verbatim NAME}, as provided on the command line. This will be a
  batch session, running @{verbatim ROOT.ML} from the current
  directory and then quitting.  It is assumed that @{verbatim ROOT.ML}
  contains all ML commands required to build the logic.

  In example mode, @{tool usedir} runs a read-only session of
  @{verbatim LOGIC} and automatically runs @{verbatim ROOT.ML} from
  within directory @{verbatim NAME}.  It assumes that this file
  contains appropriate ML commands to run the desired examples.

  \medskip The @{verbatim "-i"} option controls theory browser data
  generation. It may be explicitly turned on or off --- as usual, the
  last occurrence of @{verbatim "-i"} on the command line wins.

  The @{verbatim "-P"} option specifies a path (or actual URL) to be
  prefixed to any \emph{non-local} reference of existing theories.
  Thus user sessions may easily link to existing Isabelle libraries
  already present on the WWW.

  The @{verbatim "-m"} options specifies additional print modes to be
  activated temporarily while the session is processed.

  \medskip The @{verbatim "-d"} option controls document preparation.
  Valid arguments are @{verbatim false} (do not prepare any document;
  this is default), or any of @{verbatim dvi}, @{verbatim dvi.gz},
  @{verbatim ps}, @{verbatim ps.gz}, @{verbatim pdf}.  The logic
  session has to provide a properly setup @{verbatim document}
  directory.  See \secref{sec:tool-document} and
  \secref{sec:tool-latex} for more details.

  \medskip The @{verbatim "-V"} option declares alternative document
  variants, consisting of name/tags pairs (cf.\ options @{verbatim
  "-n"} and @{verbatim "-t"} of @{tool_ref document}).  The standard
  document is equivalent to ``@{verbatim
  "document=theory,proof,ML"}'', which means that all theory begin/end
  commands, proof body texts, and ML code will be presented
  faithfully.

  An alternative variant ``@{verbatim "outline=/proof/ML"}'' would
  fold proof and ML parts, replacing the original text by a short
  place-holder.  The form ``@{text name}@{verbatim "=-"},'' means to
  remove document @{text name} from the list of variants to be
  processed.  Any number of @{verbatim "-V"} options may be given;
  later declarations have precedence over earlier ones.

  Some document variant @{text name} may use an alternative {\LaTeX}
  entry point called @{verbatim "document/root_"}@{text
  "name"}@{verbatim ".tex"} if that file exists; otherwise the common
  @{verbatim "document/root.tex"} is used.

  \medskip The @{verbatim "-g"} option produces images of the theory
  dependency graph (cf.\ \secref{sec:browse}) for inclusion in the
  generated document, both as @{verbatim session_graph.eps} and
  @{verbatim session_graph.pdf} at the same time.  To include this in
  the final {\LaTeX} document one could say @{verbatim
  "\\includegraphics{session_graph}"} in @{verbatim
  "document/root.tex"} (omitting the file-name extension enables
  {\LaTeX} to select to correct version, either for the DVI or PDF
  output path).

  \medskip The @{verbatim "-D"} option causes the generated document
  sources to be dumped at location @{verbatim PATH}; this path is
  relative to the session's main directory.  If the @{verbatim "-C"}
  option is true, this will include a copy of an existing @{verbatim
  document} directory as provided by the user.  For example, @{tool
  usedir}~@{verbatim "-D generated HOL Foo"} produces a complete set
  of document sources at @{verbatim "Foo/generated"}.  Subsequent
  invocation of @{tool document}~@{verbatim "Foo/generated"} (see also
  \secref{sec:tool-document}) will process the final result
  independently of an Isabelle job.  This decoupled mode of operation
  facilitates debugging of serious {\LaTeX} errors, for example.

  \medskip The @{verbatim "-p"} option determines the level of detail
  for internal proof objects, see also the \emph{Isabelle Reference
  Manual}~\cite{isabelle-ref}.

  \medskip The @{verbatim "-q"} option specifies the level of parallel
  proof checking: @{verbatim 0} no proofs, @{verbatim 1} toplevel
  proofs (default), @{verbatim 2} toplevel and nested Isar proofs.
  The option @{verbatim "-Q"} specifies a threshold for @{verbatim
  "-q2"}: nested proofs are only parallelized when the current number
  of forked proofs falls below the given value (default 50),
  multiplied by the number of worker threads (see option @{verbatim
  "-M"}).

  \medskip The @{verbatim "-t"} option produces a more detailed
  internal timing report of the session.

  \medskip The @{verbatim "-v"} option causes additional information
  to be printed while running the session, notably the location of
  prepared documents.

  \medskip The @{verbatim "-M"} option specifies the maximum number of
  parallel worker threads used for processing independent tasks when
  checking theory sources (multithreading only works on suitable ML
  platforms).  The special value of @{verbatim 0} or @{verbatim max}
  refers to the number of actual CPU cores of the underlying machine,
  which is a good starting point for optimal performance tuning.  The
  @{verbatim "-T"} option determines the level of detail in tracing
  output concerning the internal locking and scheduling in
  multithreaded operation.  This may be helpful in isolating
  performance bottle-necks, e.g.\ due to excessive wait states when
  locking critical code sections.

  \medskip Any @{tool usedir} session is named by some \emph{session
  identifier}. These accumulate, documenting the way sessions depend
  on others. For example, consider @{verbatim "Pure/FOL/ex"}, which
  refers to the examples of FOL, which in turn is built upon Pure.

  The current session's identifier is by default just the base name of
  the @{verbatim LOGIC} argument (in build mode), or of the @{verbatim
  NAME} argument (in example mode). This may be overridden explicitly
  via the @{verbatim "-s"} option.
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