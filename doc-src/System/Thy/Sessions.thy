theory Sessions
imports Base
begin

chapter {* Isabelle sessions and build management *}

text {* FIXME *}

section {* Session ROOT specifications \label{sec:session-root} *}

text {* FIXME *}


section {* System build options \label{sec:system-options} *}

text {* FIXME *}


section {* Invoking the build process \label{sec:tool-build} *}

text {* The @{tool_def build} utility invokes the build process for
  Isabelle sessions.  It manages dependencies between sessions,
  related sources of theories and auxiliary files, and target heap
  images.  Accordingly, it runs instances of the prover process with
  optional document preparation.  Its command-line usage
  is:\footnote{Isabelle/Scala provides the same functionality via
  \texttt{isabelle.Build.build}.}
\begin{ttbox} Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -a           select all sessions
    -b           build heap images
    -d DIR       include session directory with ROOT file
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -n           no build -- test dependencies only
    -o OPTION    override session configuration OPTION
                 (via NAME=VAL or NAME)
    -s           system build mode: produce output in ISABELLE_HOME
    -v           verbose

  Build and manage Isabelle sessions, depending on implicit
  ISABELLE_BUILD_OPTIONS="..."

  ML_PLATFORM="..."
  ML_HOME="..."
  ML_SYSTEM="..."
  ML_OPTIONS="..."
\end{ttbox}

  \medskip Isabelle sessions are defined via session ROOT files as
  described in (\secref{sec:session-root}).  The totality of sessions
  is determined by collecting such specifications from all Isabelle
  component directories (\secref{sec:components}), augmented by more
  directories given via options @{verbatim "-d"}~@{text "DIR"} on the
  command line.  Each such directory may contain a session
  \texttt{ROOT} file and an additional catalog file @{verbatim
  "etc/sessions"} with further sub-directories (list of lines).  Note
  that a single \texttt{ROOT} file usually defines many sessions;
  catalogs are are only required for extra scalability and modularity
  of large libraries.

  \medskip The subset of sessions to be managed is selected via
  individual @{text "SESSIONS"} given as command-line arguments, or
  session groups that are specified via one or more options @{verbatim
  "-g"}~@{text "NAME"}.  Option @{verbatim "-a"} selects all sessions.
  The build tool takes the hierarchy of sessions into account: the
  selected set of sessions is completed by including all ancestors
  according to the dependency structure.

  \medskip The build process depends on additional options that are
  passed to the prover session eventually, see also
  (\secref{sec:system-options}).  The settings variable @{setting_ref
  ISABELLE_BUILD_OPTIONS} allows to provide additional defaults.
  Moreover, the environment of system build options may be augmented
  on the command line via @{verbatim "-o"}~@{text "NAME=VALUE"} or
  @{verbatim "-o"}~@{text "NAME"}, which abbreviates @{verbatim
  "-o"}~@{text "NAME=true"} for Boolean options.  Multiple occurrences
  of @{verbatim "-o"} on the command-line are applied in the given
  order.

  \medskip Option @{verbatim "-b"} ensures that heap images are
  produced for all selected sessions.  By default, images are only
  saved for inner nodes of the hierarchy of sessions, as required for
  other sessions to continue later on.

  \medskip Option @{verbatim "-j"} specifies the maximum number of
  parallel build jobs (prover processes).  Note that each process is
  subject to a separate limit of parallel threads, cf.\ system option
  @{system_option_ref threads}.

  \medskip Option @{verbatim "-s"} enables \emph{system mode}, which
  means that resulting heap images and log files are stored in
  @{verbatim "$ISABELLE_HOME/heaps"} instead of the default location
  @{setting ISABELLE_OUTPUT} (which is normally in @{setting
  ISABELLE_HOME_USER}, i.e.\ the user's home directory).

  \medskip Option @{verbatim "-n"} omits the actual build process
  after performing all dependency checks.  The return code indicates
  the status of the set of selected sessions.

  \medskip Option @{verbatim "-v"} enables verbose mode.
*}

subsubsection {* Examples *}

text {*
  Build a specific logic image:
\begin{ttbox}
isabelle build -b HOLCF
\end{ttbox}

  Build the main group of logic images (as determined by the session
  ROOT specifications of the Isabelle distribution):
\begin{ttbox}
isabelle build -b -g main
\end{ttbox}

  Provide a general overview of the status of all Isabelle sessions,
  without building anything:
\begin{ttbox}
isabelle build -a -n -v
\end{ttbox}

  Build all sessions with HTML browser info and PDF document
  preparation:
\begin{ttbox}
isabelle build -a -o browser_info -o document=pdf
\end{ttbox}

  Build all sessions with a maximum of 8 prover processes and 4
  threads each (on a machine with many cores):

\begin{ttbox}
isabelle build -a -j8 -o threads=4
\end{ttbox}
*}

end
