(* $Id$ *)

theory Basics
imports Pure
begin

chapter {* The Isabelle system environment *}

text {*
  This manual describes Isabelle together with related tools and user
  interfaces as seen from an outside (system oriented) view.  See also
  the \emph{Isabelle/Isar Reference Manual}~\cite{isabelle-isar-ref}
  and the \emph{Isabelle Reference Manual}~\cite{isabelle-ref} for the
  actual Isabelle commands and related functions.

  \medskip The Isabelle system environment emerges from a few general
  concepts.

  \begin{itemize}

  \item The \emph{Isabelle settings mechanism} provides environment variables to
  all Isabelle programs (including tools and user interfaces).

  \item The \emph{Isabelle tools wrapper} (@{executable_def isatool})
  provides a generic startup platform for Isabelle related utilities.
  Thus tools automatically benefit from the settings mechanism.

  \item The raw \emph{Isabelle process} (@{executable_def isabelle} or
  @{executable_def "isabelle-process"}) runs logic sessions either
  interactively or in batch mode.  In particular, this view abstracts
  over the invocation of the actual ML system to be used.

  \item The \emph{Isabelle interface wrapper} (@{executable_def
  Isabelle} or @{executable_def "isabelle-interface"}) provides some
  abstraction over the actual user interface to be used.  The de-facto
  standard interface for Isabelle is Proof~General
  \cite{proofgeneral}.

  \end{itemize}

  \medskip The beginning user would probably just run the default user
  interface (by invoking the capital @{executable Isabelle}).  This
  assumes that the system has already been installed, of course.  In
  case you have to do this yourself, see the @{verbatim INSTALL} file
  in the top-level directory of the distribution of how to proceed;
  binary packages for various system components are available as well.
*}


section {* Isabelle settings \label{sec:settings} *}

text {*
  The Isabelle system heavily depends on the \emph{settings
  mechanism}\indexbold{settings}.  Essentially, this is a statically
  scoped collection of environment variables, such as @{setting
  ISABELLE_HOME}, @{setting ML_SYSTEM}, @{setting ML_HOME}.  These
  variables are \emph{not} intended to be set directly from the shell,
  though.  Isabelle employs a somewhat more sophisticated scheme of
  \emph{settings files} --- one for site-wide defaults, another for
  additional user-specific modifications.  With all configuration
  variables in at most two places, this scheme is more maintainable
  and user-friendly than global shell environment variables.

  In particular, we avoid the typical situation where prospective
  users of a software package are told to put several things into
  their shell startup scripts, before being able to actually run the
  program. Isabelle requires none such administrative chores of its
  end-users --- the executables can be invoked straight away.
  Occasionally, users would still want to put the Isabelle @{verbatim
  bin} directory into their shell's search path, but this is not
  required.
*}


subsection {* Building the environment *}

text {*
  Whenever any of the Isabelle executables is run, their settings
  environment is put together as follows.

  \begin{enumerate}

  \item The special variable @{setting_def ISABELLE_HOME} is
  determined automatically from the location of the binary that has
  been run.
  
  You should not try to set @{setting ISABELLE_HOME} manually. Also
  note that the Isabelle executables either have to be run from their
  original location in the distribution directory, or via the
  executable objects created by the @{tool install} utility (see
  \secref{sec:tool-install}).  Just doing a plain copy of the
  @{verbatim bin} files will not work!
  
  \item The file @{verbatim "$ISABELLE_HOME/etc/settings"} ist run as
  a shell script with the auto-export option for variables enabled.
  
  This file holds a rather long list of shell variable assigments,
  thus providing the site-wide default settings.  The Isabelle
  distribution already contains a global settings file with sensible
  defaults for most variables.  When installing the system, only a few
  of these may have to be adapted (probably @{setting ML_SYSTEM}
  etc.).
  
  \item The file @{verbatim "$ISABELLE_HOME_USER/etc/settings"} (if it
  exists) is run in the same way as the site default settings. Note
  that the variable @{setting ISABELLE_HOME_USER} has already been set
  before --- usually to @{verbatim "~/isabelle"}.
  
  Thus individual users may override the site-wide defaults.  See also
  file @{verbatim "etc/user-settings.sample"} in the distribution.
  Typically, a user settings file would contain only a few lines, just
  the assigments that are really changed.  One should definitely
  \emph{not} start with a full copy the basic @{verbatim
  "$ISABELLE_HOME/etc/settings"}. This could cause very annoying
  maintainance problems later, when the Isabelle installation is
  updated or changed otherwise.
  
  \end{enumerate}

  Note that settings files are actually full GNU bash scripts. So one
  may use complex shell commands, such as @{verbatim "if"} or
  @{verbatim "case"} statements to set variables depending on the
  system architecture or other environment variables.  Such advanced
  features should be added only with great care, though. In
  particular, external environment references should be kept at a
  minimum.

  \medskip A few variables are somewhat special:

  \begin{itemize}

  \item @{setting_def ISABELLE} and @{setting_def ISATOOL} are set
  automatically to the absolute path names of the @{executable
  "isabelle-process"} and @{executable isatool} executables,
  respectively.
  
  \item @{setting_def ISABELLE_OUTPUT} will have the identifiers of
  the Isabelle distribution (cf.\ @{setting ISABELLE_IDENTIFIER}) and
  the ML system (cf.\ @{setting ML_IDENTIFIER}) appended automatically
  to its value.

  \end{itemize}

  \medskip The Isabelle settings scheme is conceptually simple, but
  not completely trivial.  For debugging purposes, the resulting
  environment may be inspected with the @{tool getenv} utility, see
  \secref{sec:tool-getenv}.
*}


subsection{* Common variables *}

text {*
  This is a reference of common Isabelle settings variables. Note that
  the list is somewhat open-ended. Third-party utilities or interfaces
  may add their own selection. Variables that are special in some
  sense are marked with @{text "\<^sup>*"}.

  \begin{description}

  \item[@{setting_def ISABELLE_HOME}@{text "\<^sup>*"}] is the
  location of the top-level Isabelle distribution directory. This is
  automatically determined from the Isabelle executable that has been
  invoked.  Do not attempt to set @{setting ISABELLE_HOME} yourself
  from the shell.
  
  \item[@{setting_def ISABELLE_HOME_USER}] is the user-specific
  counterpart of @{setting ISABELLE_HOME}. The default value is
  @{verbatim "~/isabelle"}, under rare circumstances this may be
  changed in the global setting file.  Typically, the @{setting
  ISABELLE_HOME_USER} directory mimics @{setting ISABELLE_HOME} to
  some extend. In particular, site-wide defaults may be overridden by
  a private @{verbatim "etc/settings"}.
  
  \item[@{setting_def ISABELLE}@{text "\<^sup>*"}, @{setting
  ISATOOL}@{text "\<^sup>*"}] are automatically set to the full path
  names of the @{executable "isabelle-process"} and @{executable
  isatool} executables, respectively.  Thus other tools and scripts
  need not assume that the Isabelle @{verbatim bin} directory is on
  the current search path of the shell.
  
  \item[@{setting_def ISABELLE_IDENTIFIER}@{text "\<^sup>*"}] refers
  to the name of this Isabelle distribution, e.g.\ ``@{verbatim
  Isabelle2008}''.

  \item[@{setting_def ML_SYSTEM}, @{setting_def ML_HOME},
  @{setting_def ML_OPTIONS}, @{setting_def ML_PLATFORM}, @{setting_def
  ML_IDENTIFIER}@{text "\<^sup>*"}] specify the underlying ML system
  to be used for Isabelle.  There is only a fixed set of admissable
  @{setting ML_SYSTEM} names (see the @{verbatim "etc/settings"} file
  of the distribution).
  
  The actual compiler binary will be run from the directory @{setting
  ML_HOME}, with @{setting ML_OPTIONS} as first arguments on the
  command line.  The optional @{setting ML_PLATFORM} may specify the
  binary format of ML heap images, which is useful for cross-platform
  installations.  The value of @{setting ML_IDENTIFIER} is
  automatically obtained by composing the values of @{setting
  ML_SYSTEM}, @{setting ML_PLATFORM} and the Isabelle version values.
  
  \item[@{setting_def ISABELLE_PATH}] is a list of directories
  (separated by colons) where Isabelle logic images may reside.  When
  looking up heaps files, the value of @{setting ML_IDENTIFIER} is
  appended to each component internally.
  
  \item[@{setting_def ISABELLE_OUTPUT}@{text "\<^sup>*"}] is a
  directory where output heap files should be stored by default. The
  ML system and Isabelle version identifier is appended here, too.
  
  \item[@{setting_def ISABELLE_BROWSER_INFO}] is the directory where
  theory browser information (HTML text, graph data, and printable
  documents) is stored (see also \secref{sec:info}).  The default
  value is @{verbatim "$ISABELLE_HOME_USER/browser_info"}.
  
  \item[@{setting_def ISABELLE_LOGIC}] specifies the default logic to
  load if none is given explicitely by the user.  The default value is
  @{verbatim HOL}.
  
  \item[@{setting_def ISABELLE_LINE_EDITOR}] specifies the default
  line editor for @{verbatim "isatool tty"} (see also
  \secref{sec:tool-tty}).

  \item[@{setting_def ISABELLE_USEDIR_OPTIONS}] is implicitly prefixed
  to the command line of any @{verbatim "isatool usedir"} invocation
  (see also \secref{sec:tool-usedir}). This typically contains
  compilation options for object-logics --- @{tool usedir} is the
  basic utility for managing logic sessions (cf.\ the @{verbatim
  IsaMakefile}s in the distribution).

  \item[@{setting_def ISABELLE_FILE_IDENT}] specifies a shell command
  for producing a source file identification, based on the actual
  content instead of the full physical path and date stamp (which is
  the default). A typical identification would produce a ``digest'' of
  the text, using a cryptographic hash function like SHA-1, for
  example.
  
  \item[@{setting_def ISABELLE_LATEX}, @{setting_def
  ISABELLE_PDFLATEX}, @{setting_def ISABELLE_BIBTEX}, @{setting_def
  ISABELLE_DVIPS}] refer to {\LaTeX} related tools for Isabelle
  document preparation (see also \secref{sec:tool-latex}).
  
  \item[@{setting_def ISABELLE_TOOLS}] is a colon separated list of
  directories that are scanned by @{executable isatool} for external
  utility programs (see also \secref{sec:isatool}).
  
  \item[@{setting_def ISABELLE_DOCS}] is a colon separated list of
  directories with documentation files.
  
  \item[@{setting_def ISABELLE_DOC_FORMAT}] specifies the preferred
  document format, typically @{verbatim dvi} or @{verbatim pdf}.
  
  \item[@{setting_def DVI_VIEWER}] specifies the command to be used
  for displaying @{verbatim dvi} files.
  
  \item[@{setting_def PDF_VIEWER}] specifies the command to be used
  for displaying @{verbatim pdf} files.
  
  \item[@{setting_def PRINT_COMMAND}] specifies the standard printer
  spool command, which is expected to accept @{verbatim ps} files.
  
  \item[@{setting_def ISABELLE_TMP_PREFIX}@{text "\<^sup>*"}] is the
  prefix from which any running @{executable isabelle} process derives
  an individual directory for temporary files.  The default is
  somewhere in @{verbatim "/tmp"}.
  
  \item[@{setting_def ISABELLE_INTERFACE}] is an identifier that
  specifies the actual user interface that the capital @{executable
  Isabelle} or @{executable "isabelle-interface"} should invoke.  See
  \secref{sec:interface} for more details.

  \end{description}
*}


section {* The Isabelle tools wrapper \label{sec:isatool} *}

text {*
  All Isabelle related utilities are called via a common wrapper ---
  \ttindex{isatool}:

\begin{ttbox}
Usage: isatool TOOL [ARGS ...]

  Start Isabelle utility program TOOL with ARGS. Pass "-?" to TOOL
  for more specific help.

  Available tools are:

    browser - Isabelle graph browser
    \dots
\end{ttbox}

  In principle, Isabelle tools are ordinary executable scripts that
  are run within the Isabelle settings environment, see
  \secref{sec:settings}.  The set of available tools is collected by
  @{executable isatool} from the directories listed in the @{setting
  ISABELLE_TOOLS} setting.  Do not try to call the scripts directly
  from the shell.  Neither should you add the tool directories to your
  shell's search path!
*}


subsubsection {* Examples *}

text {*
  Show the list of available documentation of the current Isabelle
  installation like this:

\begin{ttbox}
  isatool doc
\end{ttbox}

  View a certain document as follows:
\begin{ttbox}
  isatool doc isar-ref
\end{ttbox}

  Create an Isabelle session derived from HOL (see also
  \secref{sec:tool-mkdir} and \secref{sec:tool-make}):
\begin{ttbox}
  isatool mkdir HOL Test && isatool make
\end{ttbox}
  Note that @{verbatim "isatool mkdir"} is usually only invoked once;
  existing sessions (including document output etc.) are then updated
  by @{verbatim "isatool make"} alone.
*}


section {* The raw Isabelle process *}

text {*
  The @{executable_ref isabelle} (or @{executable_ref
  "isabelle-process"}) executable runs bare-bones Isabelle logic
  sessions --- either interactively or in batch mode.  It provides an
  abstraction over the underlying ML system, and over the actual heap
  file locations.  Its usage is:

\begin{ttbox}
Usage: isabelle [OPTIONS] [INPUT] [OUTPUT]

  Options are:
    -C           tell ML system to copy output image
    -I           startup Isar interaction mode
    -P           startup Proof General interaction mode
    -S           secure mode -- disallow critical operations
    -W OUTPUT    startup process wrapper, with messages going to OUTPUT stream
    -X           startup PGIP interaction mode
    -c           tell ML system to compress output image
    -e MLTEXT    pass MLTEXT to the ML session
    -f           pass 'Session.finish();' to the ML session
    -m MODE      add print mode for output
    -q           non-interactive session
    -r           open heap file read-only
    -u           pass 'use"ROOT.ML";' to the ML session
    -w           reset write permissions on OUTPUT

  INPUT (default "\$ISABELLE_LOGIC") and OUTPUT specify in/out heaps.
  These are either names to be searched in the Isabelle path, or
  actual file names (containing at least one /).
  If INPUT is "RAW_ML_SYSTEM", just start the bare bones ML system.
\end{ttbox}

  Input files without path specifications are looked up in the
  @{setting ISABELLE_PATH} setting, which may consist of multiple
  components separated by colons --- these are tried in the given
  order with the value of @{setting ML_IDENTIFIER} appended
  internally.  In a similar way, base names are relative to the
  directory specified by @{setting ISABELLE_OUTPUT}.  In any case,
  actual file locations may also be given by including at least one
  slash (@{verbatim "/"}) in the name (hint: use @{verbatim "./"} to
  refer to the current directory).
*}


subsection {* Options *}

text {*
  If the input heap file does not have write permission bits set, or
  the @{verbatim "-r"} option is given explicitely, then the session
  started will be read-only.  That is, the ML world cannot be
  committed back into the image file.  Otherwise, a writable session
  enables commits into either the input file, or into another output
  heap file (if that is given as the second argument on the command
  line).

  The read-write state of sessions is determined at startup only, it
  cannot be changed intermediately. Also note that heap images may
  require considerable amounts of disk space (approximately
  50--200~MB). Users are responsible for themselves to dispose their
  heap files when they are no longer needed.

  \medskip The @{verbatim "-w"} option makes the output heap file
  read-only after terminating.  Thus subsequent invocations cause the
  logic image to be read-only automatically.

  \medskip The @{verbatim "-c"} option tells the underlying ML system
  to compress the output heap (fully transparently).  On Poly/ML for
  example, the image is garbage collected and all stored values are
  maximally shared, resulting in up to @{text "50%"} less disk space
  consumption.

  \medskip The @{verbatim "-C"} option tells the ML system to produce
  a completely self-contained output image, probably including a copy
  of the ML runtime system itself.

  \medskip Using the @{verbatim "-e"} option, arbitrary ML code may be
  passed to the Isabelle session from the command line. Multiple
  @{verbatim "-e"}'s are evaluated in the given order. Strange things
  may happen when errorneous ML code is provided. Also make sure that
  the ML commands are terminated properly by semicolon.

  \medskip The @{verbatim "-u"} option is a shortcut for @{verbatim
  "-e"} passing ``@{verbatim "use \"ROOT.ML\";"}'' to the ML session.
  The @{verbatim "-f"} option passes ``@{verbatim "Session.finish ();"}'',
  which is intended mainly for administrative purposes.

  \medskip The @{verbatim "-m"} option adds identifiers of print modes
  to be made active for this session. Typically, this is used by some
  user interface, e.g.\ to enable output of proper mathematical
  symbols.

  \medskip Isabelle normally enters an interactive top-level loop
  (after processing the @{verbatim "-e"} texts). The @{verbatim "-q"}
  option inhibits interaction, thus providing a pure batch mode
  facility.

  \medskip The @{verbatim "-I"} option makes Isabelle enter Isar
  interaction mode on startup, instead of the primitive ML top-level.
  The @{verbatim "-P"} option configures the top-level loop for
  interaction with the Proof General user interface, and the
  @{verbatim "-X"} option enables XML-based PGIP communication.  The
  @{verbatim "-W"} option makes Isabelle enter a special process
  wrapper for interaction via an external program; the protocol is a
  stripped-down version of Proof General the interaction mode.

  \medskip The @{verbatim "-S"} option makes the Isabelle process more
  secure by disabling some critical operations, notably runtime
  compilation and evaluation of ML source code.
*}


subsection {* Examples *}

text {*
  Run an interactive session of the default object-logic (as specified
  by the @{setting ISABELLE_LOGIC} setting) like this:
\begin{ttbox}
isabelle
\end{ttbox}

  Usually @{setting ISABELLE_LOGIC} refers to one of the standard
  logic images, which are read-only by default.  A writable session
  --- based on @{verbatim FOL}, but output to @{verbatim Foo} (in the
  directory specified by the @{verbatim ISABELLE_OUTPUT} setting) ---
  may be invoked as follows:
\begin{ttbox}
isabelle FOL Foo
\end{ttbox}
  Ending this session normally (e.g.\ by typing control-D) dumps the
  whole ML system state into @{verbatim Foo}. Be prepared for several
  tens of megabytes.

  The @{verbatim Foo} session may be continued later (still in
  writable state) by:
\begin{ttbox}
isabelle Foo
\end{ttbox}
  A read-only @{verbatim Foo} session may be started by:
\begin{ttbox}
isabelle -r Foo
\end{ttbox}

  \medskip Note that manual session management like this does
  \emph{not} provide proper setup for theory presentation.  This would
  require the @{tool usedir} utility, see \secref{sec:tool-usedir}.

  \bigskip The next example demonstrates batch execution of
  Isabelle. We print a certain theorem of @{verbatim FOL}:
\begin{ttbox}
isabelle -e "prth allE;" -q -r FOL
\end{ttbox}
  Note that the output text will be interspersed with additional junk
  messages by the ML runtime environment.
*}


section {* The Isabelle interface wrapper \label{sec:interface} *}

text {*
  Isabelle is a generic theorem prover, even w.r.t.\ its user
  interface.  The @{executable_ref Isabelle} (or @{executable_ref
  "isabelle-interface"}) executable provides a uniform way for
  end-users to invoke a certain interface; which one to start is
  determined by the @{setting_ref ISABELLE_INTERFACE} setting
  variable, which should give a full path specification to the actual
  executable.  Also note that the @{tool install} utility provides
  some options to install desktop environment icons (see
  \secref{sec:tool-install}).

  Presently, the most prominent Isabelle interface is Proof
  General~\cite{proofgeneral}\index{user interface!Proof General}.
  The Proof General distribution includes an interface wrapper script
  for the regular Isar toplevel, see @{verbatim
  "ProofGeneral/isar/interface"}.  The canonical settings for
  Isabelle/Isar are as follows:

\begin{ttbox}
ISABELLE_INTERFACE=\$ISABELLE_HOME/contrib/ProofGeneral/isar/interface
PROOFGENERAL_OPTIONS=""
\end{ttbox}

  Thus @{executable Isabelle} would automatically invoke Emacs with
  proper setup of the Proof General Lisp packages.  There are some
  options available, such as @{verbatim "-l"} for passing the logic
  image to be used by default, or @{verbatim "-m"} to tune the
  standard print mode.  The @{verbatim "-I"} option allows to switch
  between the Isar and ML view, independently of the interface script
  being used.
  
  \medskip Note that the world may be also seen the other way round:
  Emacs may be started first (with proper setup of Proof General
  mode), and @{executable isabelle} run from within.  This requires
  further Emacs Lisp configuration, see the Proof General
  documentation \cite{proofgeneral} for more information.
*}

end
