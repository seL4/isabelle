(*:maxLineLen=78:*)

theory Sessions
imports Base
begin

chapter \<open>Isabelle sessions and build management \label{ch:session}\<close>

text \<open>
  An Isabelle \<^emph>\<open>session\<close> consists of a collection of related theories that may
  be associated with formal documents (\chref{ch:present}). There is also a
  notion of \<^emph>\<open>persistent heap\<close> image to capture the state of a session,
  similar to object-code in compiled programming languages. Thus the concept
  of session resembles that of a ``project'' in common IDE environments, but
  the specific name emphasizes the connection to interactive theorem proving:
  the session wraps-up the results of user-interaction with the prover in a
  persistent form.

  Application sessions are built on a given parent session, which may be built
  recursively on other parents. Following this path in the hierarchy
  eventually leads to some major object-logic session like \<open>HOL\<close>, which itself
  is based on \<open>Pure\<close> as the common root of all sessions.

  Processing sessions may take considerable time. Isabelle build management
  helps to organize this efficiently. This includes support for parallel build
  jobs, in addition to the multithreaded theory and proof checking that is
  already provided by the prover process itself.
\<close>


section \<open>Session ROOT specifications \label{sec:session-root}\<close>

text \<open>
  Session specifications reside in files called \<^verbatim>\<open>ROOT\<close> within certain
  directories, such as the home locations of registered Isabelle components or
  additional project directories given by the user.

  The ROOT file format follows the lexical conventions of the \<^emph>\<open>outer syntax\<close>
  of Isabelle/Isar, see also \<^cite>\<open>"isabelle-isar-ref"\<close>. This defines common
  forms like identifiers, names, quoted strings, verbatim text, nested
  comments etc. The grammar for @{syntax chapter_def}, @{syntax chapter_entry}
  and @{syntax session_entry} is given as syntax diagram below. Each ROOT file
  may contain multiple specifications like this. Chapters help to organize
  browser info (\secref{sec:info}), but have no formal meaning. The default
  chapter is ``\<open>Unsorted\<close>''. Chapter definitions, which are optional, allow to
  associate additional information.

  Isabelle/jEdit \<^cite>\<open>"isabelle-jedit"\<close> includes a simple editing mode
  \<^verbatim>\<open>isabelle-root\<close> for session ROOT files, which is enabled by default for any
  file of that name.

  \<^rail>\<open>
    @{syntax_def chapter_def}: @'chapter_definition' @{syntax name} \<newline>
      groups? description?
    ;

    @{syntax_def chapter_entry}: @'chapter' @{syntax name}
    ;

    @{syntax_def session_entry}: @'session' @{syntax system_name} groups? dir? '=' \<newline>
      (@{syntax system_name} '+')? description? options? \<newline>
      sessions? directories? (theories*) \<newline>
      (document_theories?) (document_files*) \<newline>
      (export_files*) (export_classpath?)
    ;
    groups: '(' (@{syntax name} +) ')'
    ;
    dir: @'in' @{syntax embedded}
    ;
    description: @'description' @{syntax text}
    ;
    options: @'options' opts
    ;
    opts: '[' ( (@{syntax name} '=' value | @{syntax name}) + ',' ) ']'
    ;
    value: @{syntax name} | @{syntax real}
    ;
    sessions: @'sessions' (@{syntax system_name}+)
    ;
    directories: @'directories' (dir+)
    ;
    theories: @'theories' opts? (theory_entry+)
    ;
    theory_entry: @{syntax system_name} ('(' @'global' ')')?
    ;
    document_theories: @'document_theories' (@{syntax name}+)
    ;
    document_files: @'document_files' ('(' dir ')')? (@{syntax embedded}+)
    ;
    export_files: @'export_files' ('(' dir ')')? ('[' nat ']')? \<newline>
      (@{syntax embedded}+)
    ;
    export_classpath: @'export_classpath' (@{syntax embedded}*)
  \<close>

  \<^descr> \isakeyword{chapter{\isacharunderscorekeyword}definition}~\<open>A (groups)\<close>
  associates a collection of groups with chapter \<open>A\<close>. All sessions that belong
  to this chapter will automatically become members of these groups.

  \<^descr> \isakeyword{session}~\<open>A = B + body\<close> defines a new session \<open>A\<close> based on
  parent session \<open>B\<close>, with its content given in \<open>body\<close> (imported sessions and
  theories). Note that a parent (like \<open>HOL\<close>) is mandatory in practical
  applications: only Isabelle/Pure can bootstrap itself from nothing.

  All such session specifications together describe a hierarchy (graph) of
  sessions, with globally unique names. The new session name \<open>A\<close> should be
  sufficiently long and descriptive to stand on its own in a potentially large
  library.

  \<^descr> \isakeyword{session}~\<open>A (groups)\<close> indicates a collection of groups where
  the new session is a member. Group names are uninterpreted and merely follow
  certain conventions. For example, the Isabelle distribution tags some
  important sessions by the group name called ``\<open>main\<close>''. Other projects may
  invent their own conventions, but this requires some care to avoid clashes
  within this unchecked name space.

  \<^descr> \isakeyword{session}~\<open>A\<close>~\isakeyword{in}~\<open>dir\<close> specifies an explicit
  directory for this session; by default this is the current directory of the
  \<^verbatim>\<open>ROOT\<close> file.

  All theory files are located relatively to the session directory. The prover
  process is run within the same as its current working directory.

  \<^descr> \isakeyword{description}~\<open>text\<close> is a free-form description for this
  session (or chapter), e.g. for presentation purposes.

  \<^descr> \isakeyword{options}~\<open>[x = a, y = b, z]\<close> defines separate options
  (\secref{sec:system-options}) that are used when processing this session,
  but \<^emph>\<open>without\<close> propagation to child sessions. Note that \<open>z\<close> abbreviates \<open>z =
  true\<close> for Boolean options.

  \<^descr> \isakeyword{sessions}~\<open>names\<close> specifies sessions that are \<^emph>\<open>imported\<close> into
  the current name space of theories. This allows to refer to a theory \<open>A\<close>
  from session \<open>B\<close> by the qualified name \<open>B.A\<close> --- although it is loaded again
  into the current ML process, which is in contrast to a theory that is
  already present in the \<^emph>\<open>parent\<close> session.

  Theories that are imported from other sessions are excluded from the current
  session document.

  \<^descr> \isakeyword{directories}~\<open>dirs\<close> specifies additional directories for
  import of theory files via \isakeyword{theories} within \<^verbatim>\<open>ROOT\<close> or
  \<^theory_text>\<open>imports\<close> within a theory; \<open>dirs\<close> are relative to the main session
  directory (cf.\ \isakeyword{session} \dots \isakeyword{in}~\<open>dir\<close>). These
  directories need to be exclusively assigned to a unique session, without
  implicit sharing of file-system locations.

  \<^descr> \isakeyword{theories}~\<open>options names\<close> specifies a block of theories that
  are processed within an environment that is augmented by the given options,
  in addition to the global session options given before. Any number of blocks
  of \isakeyword{theories} may be given. Options are only active for each
  \isakeyword{theories} block separately.

  A theory name that is followed by \<open>(\<close>\isakeyword{global}\<open>)\<close> is treated
  literally in other session specifications or theory imports --- the normal
  situation is to qualify theory names by the session name; this ensures
  globally unique names in big session graphs. Global theories are usually the
  entry points to major logic sessions: \<open>Pure\<close>, \<open>Main\<close>, \<open>Complex_Main\<close>,
  \<open>HOLCF\<close>, \<open>IFOL\<close>, \<open>FOL\<close>, \<open>ZF\<close>, \<open>ZFC\<close> etc. Regular Isabelle applications
  should not claim any global theory names.

  \<^descr> \isakeyword{document_theories}~\<open>names\<close> specifies theories from other
  sessions that should be included in the generated document source directory.
  These theories need to be explicit imports in the current session, or
  implicit imports from the underlying hierarchy of parent sessions. The
  generated \<^verbatim>\<open>session.tex\<close> file is not affected: the session's {\LaTeX} setup
  needs to \<^verbatim>\<open>\input{\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> generated \<^verbatim>\<open>.tex\<close> files separately.

  \<^descr> \isakeyword{document_files}~\<open>(\<close>\isakeyword{in}~\<open>base_dir) files\<close> lists
  source files for document preparation, typically \<^verbatim>\<open>.tex\<close> and \<^verbatim>\<open>.sty\<close> for
  {\LaTeX}. Only these explicitly given files are copied from the base
  directory to the document output directory, before formal document
  processing is started (see also \secref{sec:tool-document}). The local path
  structure of the \<open>files\<close> is preserved, which allows to reconstruct the
  original directory hierarchy of \<open>base_dir\<close>. The default \<open>base_dir\<close> is
  \<^verbatim>\<open>document\<close> within the session root directory.

  \<^descr> \isakeyword{export_files}~\<open>(\<close>\isakeyword{in}~\<open>target_dir) [number]
  patterns\<close> specifies theory exports that may get written to the file-system,
  e.g. via @{tool_ref build} with option \<^verbatim>\<open>-e\<close> (\secref{sec:tool-build}). The
  \<open>target_dir\<close> specification is relative to the session root directory; its
  default is \<^verbatim>\<open>export\<close>. Exports are selected via \<open>patterns\<close> as in @{tool_ref
  export} (\secref{sec:tool-export}). The number given in brackets (default:
  0) specifies the prefix of elements that should be removed from each name:
  it allows to reduce the resulting directory hierarchy at the danger of
  overwriting files due to loss of uniqueness.

  \<^descr> \isakeyword{export_classpath}~\<open>patterns\<close> specifies export artifacts that
  should be included into the local Java/Scala classpath of this session
  context. This is only relevant for tools that allow dynamic loading of
  service classes (\secref{sec:scala-build}), while most other Isabelle/Scala
  tools require global configuration during system startup. An empty list of
  \<open>patterns\<close> defaults to \<^verbatim>\<open>"*:classpath/*.jar"\<close>, which fits to the naming
  convention of JAR modules produced by the Isabelle/Isar command
  \<^theory_text>\<open>scala_build_generated_files\<close> \<^cite>\<open>"isabelle-isar-ref"\<close>.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  See \<^file>\<open>~~/src/HOL/ROOT\<close> for a diversity of practically relevant situations,
  although it uses relatively complex quasi-hierarchic naming conventions like
  \<^verbatim>\<open>HOL-SPARK\<close>, \<^verbatim>\<open>HOL-SPARK-Examples\<close>. An alternative is to use unqualified
  names that are relatively long and descriptive, as in the Archive of Formal
  Proofs (AFP, \<^url>\<open>https://isa-afp.org\<close>), for example.
\<close>


section \<open>System build options \label{sec:system-options}\<close>

text \<open>
  See \<^file>\<open>~~/etc/options\<close> for the main defaults provided by the Isabelle
  distribution. Isabelle/jEdit \<^cite>\<open>"isabelle-jedit"\<close> includes a simple
  editing mode \<^verbatim>\<open>isabelle-options\<close> for this file-format.

  The following options are particularly relevant to build Isabelle sessions,
  in particular with document preparation (\chref{ch:present}).

    \<^item> @{system_option_def "browser_info"} controls output of HTML browser
    info, see also \secref{sec:info}.

    \<^item> @{system_option_def "document"} controls document output for a
    particular session or theory; \<^verbatim>\<open>document=pdf\<close> or \<^verbatim>\<open>document=true\<close> means
    enabled, \<^verbatim>\<open>document=""\<close> or \<^verbatim>\<open>document=false\<close> means disabled (especially
    for particular theories).

    \<^item> @{system_option_def "document_output"} specifies an alternative
    directory for generated output of the document preparation system; the
    default is within the @{setting "ISABELLE_BROWSER_INFO"} hierarchy as
    explained in \secref{sec:info}. See also @{tool mkroot}, which generates a
    default configuration with output readily available to the author of the
    document.

    \<^item> @{system_option_def "document_echo"} informs about document file names
    during session presentation.

    \<^item> @{system_option_def "document_variants"} specifies document variants as
    a colon-separated list of \<open>name=tags\<close> entries. The default name is
    \<^verbatim>\<open>document\<close>, without additional tags.

    Tags are specified as a comma separated list of modifier/name pairs and
    tell {\LaTeX} how to interpret certain Isabelle command regions:
    ``\<^verbatim>\<open>+\<close>\<open>foo\<close>'' (or just ``\<open>foo\<close>'') means to keep, ``\<^verbatim>\<open>-\<close>\<open>foo\<close>'' to drop,
    and ``\<^verbatim>\<open>/\<close>\<open>foo\<close>'' to fold text tagged as \<open>foo\<close>. The builtin default is
    equivalent to the tag specification
    ``\<^verbatim>\<open>+document,+theory,+proof,+ML,+visible,-invisible,+important,+unimportant\<close>'';
    see also the {\LaTeX} macros \<^verbatim>\<open>\isakeeptag\<close>, \<^verbatim>\<open>\isadroptag\<close>, and
    \<^verbatim>\<open>\isafoldtag\<close>, in \<^file>\<open>~~/lib/texinputs/isabelle.sty\<close>.

    In contrast, \<^verbatim>\<open>document_variants=document:outline=/proof,/ML\<close> indicates
    two documents: the one called \<^verbatim>\<open>document\<close> with default tags, and the other
    called \<^verbatim>\<open>outline\<close> where proofs and ML sections are folded.

    Document variant names are just a matter of conventions. It is also
    possible to use different document variant names (without tags) for
    different document root entries, see also \secref{sec:tool-document}.

    \<^item> @{system_option_def "document_tags"} specifies alternative command tags
    as a comma-separated list of items: either ``\<open>command\<close>\<^verbatim>\<open>%\<close>\<open>tag\<close>'' for a
    specific command, or ``\<^verbatim>\<open>%\<close>\<open>tag\<close>'' as default for all other commands. This
    is occasionally useful to control the global visibility of commands via
    session options (e.g.\ in \<^verbatim>\<open>ROOT\<close>).

    \<^item> @{system_option_def "document_comment_latex"} enables regular {\LaTeX}
    \<^verbatim>\<open>comment.sty\<close>, instead of the historic version for plain {\TeX}
    (default). The latter is much faster, but in conflict with {\LaTeX}
    classes like Dagstuhl
    LIPIcs\<^footnote>\<open>\<^url>\<open>https://github.com/dagstuhl-publishing/styles\<close>\<close>.

    \<^item> @{system_option_def "document_bibliography"} explicitly enables the use
    of \<^verbatim>\<open>bibtex\<close>; the default is to check the presence of \<^verbatim>\<open>root.bib\<close>, but it
    could have a different name.

    \<^item> @{system_option_def "document_heading_prefix"} specifies a prefix for
    the {\LaTeX} macro names generated from Isar commands like \<^theory_text>\<open>chapter\<close>,
    \<^theory_text>\<open>section\<close> etc. The default is \<^verbatim>\<open>isamarkup\<close>, e.g. \<^theory_text>\<open>section\<close> becomes
    \<^verbatim>\<open>\isamarkupsection\<close>.

    \<^item> @{system_option_def "threads"} determines the number of worker threads
    for parallel checking of theories and proofs. The default \<open>0\<close> means that a
    sensible value is guessed from the underlying hardware. This sometimes
    requires manual adjustment (on the command-line or within personal
    settings or preferences, not within a session \<^verbatim>\<open>ROOT\<close>).

    \<^item> @{system_option_def "condition"} specifies a comma-separated list of
    process environment variables (or Isabelle settings) that are required for
    the subsequent theories to be processed. Conditions are considered
    ``true'' if the corresponding environment value is defined and non-empty.

    \<^item> @{system_option_def "timeout"} and @{system_option_def "timeout_scale"}
    specify a real wall-clock timeout for the session as a whole: the two
    values are multiplied and taken as the number of seconds. Typically,
    @{system_option "timeout"} is given for individual sessions, and
    @{system_option "timeout_scale"} as global adjustment to overall hardware
    performance.

    The timer is controlled outside the ML process by the JVM that runs
    Isabelle/Scala. Thus it is relatively reliable in canceling processes that
    get out of control, even if there is a deadlock without CPU time usage.

    \<^item> @{system_option_def "profiling"} specifies a mode for global ML
    profiling. Possible values are the empty string (disabled), \<^verbatim>\<open>time\<close> for
    \<^ML>\<open>profile_time\<close> and \<^verbatim>\<open>allocations\<close> for \<^ML>\<open>profile_allocations\<close>.
    Results appear near the bottom of the session log file.

    \<^item> @{system_option_def system_log} specifies an optional log file for
    low-level messages produced by \<^ML>\<open>Output.system_message\<close> in
    Isabelle/ML; the standard value ``\<^verbatim>\<open>-\<close>'' refers to console progress of the
    build job.

    \<^item> @{system_option_def "system_heaps"} determines the directories for
    session heap images: \<^path>\<open>$ISABELLE_HEAPS\<close> is the user directory and
    \<^path>\<open>$ISABELLE_HEAPS_SYSTEM\<close> the system directory (usually within the
    Isabelle application). For \<^verbatim>\<open>system_heaps=false\<close>, heaps are stored in the
    user directory and may be loaded from both directories. For
    \<^verbatim>\<open>system_heaps=true\<close>, store and load happens only in the system directory.

  The @{tool_def options} tool prints Isabelle system options. Its
  command-line usage is:
  @{verbatim [display]
\<open>Usage: isabelle options [OPTIONS] [MORE_OPTIONS ...]

  Options are:
    -b           include $ISABELLE_BUILD_OPTIONS
    -g OPTION    get value of OPTION
    -l           list options
    -t TAGS      restrict list to given tags (comma-separated)
    -x FILE      export options to FILE in YXML format

  Report Isabelle system options, augmented by MORE_OPTIONS given as
  arguments NAME=VAL or NAME.\<close>}

  The command line arguments provide additional system options of the form
  \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close> or \<open>name\<close> for Boolean options.

  Option \<^verbatim>\<open>-b\<close> augments the implicit environment of system options by the ones
  of @{setting ISABELLE_BUILD_OPTIONS}, cf.\ \secref{sec:tool-build}.

  Option \<^verbatim>\<open>-g\<close> prints the value of the given option. Option \<^verbatim>\<open>-l\<close> lists all
  options with their declaration and current value. Option \<^verbatim>\<open>-t\<close> restricts the
  listing to given tags (as comma-separated list), e.g. \<^verbatim>\<open>-t build,document\<close>.

  Option \<^verbatim>\<open>-x\<close> specifies a file to export the result in YXML format, instead
  of printing it in human-readable form.
\<close>


section \<open>Invoking the build process \label{sec:tool-build}\<close>

text \<open>
  The @{tool_def build} tool invokes the build process for Isabelle sessions.
  It manages dependencies between sessions, related sources of theories and
  auxiliary files, and target heap images. Accordingly, it runs instances of
  the prover process with optional document preparation. Its command-line
  usage is:\<^footnote>\<open>Isabelle/Scala provides the same functionality via
  \<^scala_method>\<open>isabelle.Build.build\<close>.\<close>
  @{verbatim [display]
\<open>Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -A ROOT      include AFP with given root directory (":" for $AFP_BASE)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -H HOSTS     additional cluster host specifications of the form
                 NAMES:PARAMETERS (separated by commas)
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -P DIR       enable HTML/PDF presentation in directory (":" for default)
    -R           refer to requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs
                 (default: 1 for local build, 0 for build cluster)
    -l           list session source files
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions: ML heaps, session databases, documents.

  Parameters for cluster host specifications (-H), apart from system options:
     ...

  Notable system options: see "isabelle options -l -t build"

  Notable system settings:
    ISABELLE_TOOL_JAVA_OPTIONS="..."
    ISABELLE_BUILD_OPTIONS="..."

    ML_PLATFORM="..."
    ML_HOME="..."
    ML_SYSTEM="..."
    ML_OPTIONS="..."\<close>}

  \<^medskip>
  Isabelle sessions are defined via session ROOT files as described in
  (\secref{sec:session-root}). The totality of sessions is determined by
  collecting such specifications from all Isabelle component directories
  (\secref{sec:components}), augmented by more directories given via options
  \<^verbatim>\<open>-d\<close>~\<open>DIR\<close> on the command line. Each such directory may contain a session
  \<^verbatim>\<open>ROOT\<close> file with several session specifications.

  Any session root directory may refer recursively to further directories of
  the same kind, by listing them in a catalog file \<^verbatim>\<open>ROOTS\<close> line-by-line. This
  helps to organize large collections of session specifications, or to make
  \<^verbatim>\<open>-d\<close> command line options persistent (e.g.\ in
  \<^verbatim>\<open>$ISABELLE_HOME_USER/ROOTS\<close>).

  \<^medskip>
  The subset of sessions to be managed is determined via individual \<open>SESSIONS\<close>
  given as command-line arguments, or session groups that are given via one or
  more options \<^verbatim>\<open>-g\<close>~\<open>NAME\<close>. Option \<^verbatim>\<open>-a\<close> selects all sessions. The build tool
  takes session dependencies into account: the set of selected sessions is
  completed by including all ancestors.

  \<^medskip>
  One or more options \<^verbatim>\<open>-B\<close>~\<open>NAME\<close> specify base sessions to be included (all
  descendants wrt.\ the session parent or import graph).

  \<^medskip>
  One or more options \<^verbatim>\<open>-x\<close>~\<open>NAME\<close> specify sessions to be excluded (all
  descendants wrt.\ the session parent or import graph). Option \<^verbatim>\<open>-X\<close> is
  analogous to this, but excluded sessions are specified by session group
  membership.

  \<^medskip>
  Option \<^verbatim>\<open>-R\<close> reverses the selection in the sense that it refers to its
  requirements: all ancestor sessions excluding the original selection. This
  allows to prepare the stage for some build process with different options,
  before running the main build itself (without option \<^verbatim>\<open>-R\<close>).

  \<^medskip>
  Option \<^verbatim>\<open>-D\<close> is similar to \<^verbatim>\<open>-d\<close>, but selects all sessions that are defined
  in the given directories.

  \<^medskip>
  Option \<^verbatim>\<open>-S\<close> indicates a ``soft build'': the selection is restricted to
  those sessions that have changed sources (according to actually imported
  theories). The status of heap images is ignored.

  \<^medskip>
  The build process depends on additional options
  (\secref{sec:system-options}) that are passed to the prover eventually. The
  settings variable @{setting_ref ISABELLE_BUILD_OPTIONS} allows to provide
  additional defaults, e.g.\ \<^verbatim>\<open>ISABELLE_BUILD_OPTIONS="document=pdf threads=4"\<close>.
  Moreover, the environment of system build options may be augmented on the
  command line via \<^verbatim>\<open>-o\<close>~\<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close> or \<^verbatim>\<open>-o\<close>~\<open>name\<close>, which abbreviates
  \<^verbatim>\<open>-o\<close>~\<open>name\<close>\<^verbatim>\<open>=true\<close> for Boolean or string options. Multiple occurrences of
  \<^verbatim>\<open>-o\<close> on the command-line are applied in the given order.

  \<^medskip>
  Option \<^verbatim>\<open>-P\<close> enables PDF/HTML presentation in the given directory, where
  ``\<^verbatim>\<open>-P:\<close>'' refers to the default @{setting_ref ISABELLE_BROWSER_INFO} (or
  @{setting_ref ISABELLE_BROWSER_INFO_SYSTEM}). This applies only to
  explicitly selected sessions; note that option \<^verbatim>\<open>-R\<close> allows to select all
  requirements separately.

  \<^medskip>
  Option \<^verbatim>\<open>-b\<close> ensures that heap images are produced for all selected
  sessions. By default, images are only saved for inner nodes of the hierarchy
  of sessions, as required for other sessions to continue later on.

  \<^medskip>
  Option \<^verbatim>\<open>-c\<close> cleans the selected sessions (all descendants wrt.\ the session
  parent or import graph) before performing the specified build operation.

  \<^medskip>
  Option \<^verbatim>\<open>-e\<close> executes the \isakeyword{export_files} directives from the ROOT
  specification of all explicitly selected sessions: the status of the session
  build database needs to be OK, but the session could have been built
  earlier. Using \isakeyword{export_files}, a session may serve as abstract
  interface for add-on build artefacts, but these are only materialized on
  explicit request: without option \<^verbatim>\<open>-e\<close> there is no effect on the physical
  file-system yet.

  \<^medskip>
  Option \<^verbatim>\<open>-f\<close> forces a fresh build of all selected sessions and their
  requirements.

  \<^medskip> Option \<^verbatim>\<open>-n\<close> omits the actual build process after the preparatory stage
  (including optional cleanup). The overall return code always the status of
  the set of selected sessions. Add-on builds (like presentation) are run for
  successful sessions, i.e.\ already finished ones.

  \<^medskip>
  Option \<^verbatim>\<open>-j\<close> specifies the maximum number of parallel build jobs (prover
  processes). Each prover process is subject to a separate limit of parallel
  worker threads, cf.\ system option @{system_option_ref threads}. The default
  is 1 for a local build, and 0 for a cluster build (see option \<^verbatim>\<open>-H\<close> below).

  \<^medskip>
  Option \<^verbatim>\<open>-N\<close> enables cyclic shuffling of NUMA CPU nodes. This may help
  performance tuning on Linux servers with separate CPU/memory modules.

  \<^medskip>
  Option \<^verbatim>\<open>-v\<close> increases the general level of verbosity.

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> lists the source files that contribute to a session.

  \<^medskip>
  Option \<^verbatim>\<open>-H\<close> augments the cluster hosts to be used in this build process.
  Each \<^verbatim>\<open>-H\<close> option accepts multiple host or cluster names (separated by
  commas), which all share the same (optional) parameters or system options.
  Multiple \<^verbatim>\<open>-H\<close> options may be given to specify further hosts (with different
  parameters). For example: \<^verbatim>\<open>-H host1,host2:jobs=2,threads=4 -H host3:jobs=4,threads=6\<close>.

  The syntax for host parameters follows Isabelle outer syntax, notably with
  double-quoted string literals. On the command-line, this may require extra
  single quotes or escapes. For example: \<^verbatim>\<open>-H 'host4:dirs="..."'\<close>.

  The system registry (\secref{sec:system-registry}) may define host and
  cluster names in its tables \<^verbatim>\<open>host\<close> and \<^verbatim>\<open>cluster\<close>, respectively. A name in
  option \<^verbatim>\<open>-H\<close> without prefix refers to the registry table \<^verbatim>\<open>host\<close>: each entry
  consists of an optional \<^verbatim>\<open>hostname\<close> and further options. A name with the
  prefix ``\<^verbatim>\<open>cluster.\<close>'' refers to the table \<^verbatim>\<open>cluster\<close>: each entry provides
  \<^verbatim>\<open>hosts\<close>, an array of names for entries of the table \<^verbatim>\<open>host\<close> as above, and
  additional options that apply to all hosts simultaneously.

  The local host only participates in cluster build, if an explicit option
  \<^verbatim>\<open>-j\<close> > 0 is given. The default is 0, which means that \<^verbatim>\<open>isabelle build -H\<close>
  will initialize the build queue and oversee remote workers, but not run any
  Isabelle sessions on its own account.

  The presence of at least one \<^verbatim>\<open>-H\<close> option changes the mode of operation of
  \<^verbatim>\<open>isabelle build\<close> substantially. It uses a shared PostgreSQL database
  server, which needs to be accessible from each node via local system options
  such as @{system_option "build_database_server"}, @{system_option
  "build_database_host"}, or @{system_option "build_database_ssh_host"}.
  Remote host connections are managed via regular SSH configuration, see also
  \<^verbatim>\<open>$HOME/.ssh/config\<close> on each node.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Build a specific logic image:
  @{verbatim [display] \<open>  isabelle build -b HOLCF\<close>}

  \<^smallskip>
  Build the main group of logic images:
  @{verbatim [display] \<open>  isabelle build -b -g main\<close>}

  \<^smallskip>
  Build all descendants (and requirements) of \<^verbatim>\<open>FOL\<close> and \<^verbatim>\<open>ZF\<close>:
  @{verbatim [display] \<open>  isabelle build -B FOL -B ZF\<close>}

  \<^smallskip>
  Build all sessions where sources have changed (ignoring heaps):
  @{verbatim [display] \<open>  isabelle build -a -S\<close>}

  \<^smallskip>
  Provide a general overview of the status of all Isabelle sessions, without
  building anything:
  @{verbatim [display] \<open>  isabelle build -a -n -v\<close>}

  \<^smallskip>
  Build all sessions with HTML browser info and PDF document preparation:
  @{verbatim [display] \<open>  isabelle build -a -o browser_info -o document\<close>}

  \<^smallskip>
  Build all sessions with a maximum of 8 parallel prover processes and 4
  worker threads each (on a machine with many cores):
  @{verbatim [display] \<open>  isabelle build -a -j8 -o threads=4\<close>}

  \<^smallskip>
  Build some session images with cleanup of their descendants, while retaining
  their ancestry:
  @{verbatim [display] \<open>  isabelle build -b -c HOL-Library HOL-Algebra\<close>}

  \<^smallskip>
  HTML/PDF presentation for sessions that happen to be properly built already,
  without rebuilding anything except the missing browser info:
  @{verbatim [display] \<open>  isabelle build -a -n -o browser_info\<close>}

  \<^smallskip>
  Clean all sessions without building anything:
  @{verbatim [display] \<open>  isabelle build -a -n -c\<close>}

  \<^smallskip>
  Build all sessions from some other directory hierarchy, according to the
  settings variable \<^verbatim>\<open>AFP\<close> that happens to be defined inside the Isabelle
  environment:
  @{verbatim [display] \<open>  isabelle build -D '$AFP'\<close>}

  \<^smallskip>
  Inform about the status of all sessions required for AFP, without building
  anything yet:
  @{verbatim [display] \<open>  isabelle build -D '$AFP' -R -v -n\<close>}

  \<^smallskip>
  Run a distributed build on 3 cluster hosts (local, \<^verbatim>\<open>host1\<close>, \<^verbatim>\<open>host2\<close>):
  @{verbatim [display] \<open>  isabelle build -a -j2 -o threads=8 \
    -H host1:jobs=2,threads=8
    -H host2:jobs=4:threads=4,numa,shared\<close>}

  \<^smallskip>
  Use build hosts and cluster specifications:
  @{verbatim [display] \<open>  isabelle build -H a -H b -H cluster.xy\<close>}

  The above requires a \<^path>\<open>$ISABELLE_HOME_USER/etc/registry.toml\<close> file like
  this:

@{verbatim [display] \<open>    host.a = { hostname = "host-a.acme.org", jobs = 2 }
    host.b = { hostname = "host-b.acme.org", jobs = 2 }

    host.x = { hostname = "server1.example.com" }
    host.y = { hostname = "server2.example.com" }
    cluster.xy = { hosts = ["x", "y"], jobs = 4 }
\<close>}
\<close>


section \<open>Print messages from session build database \label{sec:tool-log}\<close>

text \<open>
  The @{tool_def "build_log"} tool prints prover messages from the build
  database of the given session. Its command-line usage is:

  @{verbatim [display]
\<open>Usage: isabelle build_log [OPTIONS] [SESSIONS ...]

  Options are:
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -T NAME      restrict to given theories (multiple options possible)
    -U           output Unicode symbols
    -m MARGIN    margin for pretty printing (default: 76.0)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           print all messages, including information etc.

  Print messages from the session build database of the given sessions,
  without any checks against current sources nor session structure: results
  from old sessions or failed builds can be printed as well.

  Multiple options -H and -M are conjunctive: all given patterns need to
  match. Patterns match any substring, but ^ or $ may be used to match the
  start or end explicitly.\<close>}

  The specified session databases are taken as is, with formal checking
  against current sources: There is \<^emph>\<open>no\<close> implicit build process involved, so
  it is possible to retrieve error messages from a failed session as well. The
  order of messages follows the source positions of source files; thus the
  result is mostly deterministic, independent of the somewhat erratic
  evaluation of parallel processing.

  \<^medskip> Option \<^verbatim>\<open>-o\<close> allows to change system options, as in @{tool build}
  (\secref{sec:tool-build}). This may affect the storage space for the build
  database, notably via @{system_option system_heaps}, or @{system_option
  build_database_server} and its relatives.

  \<^medskip> Option \<^verbatim>\<open>-T\<close> restricts output to given theories: multiple entries are
  possible by repeating this option on the command-line. The default is to
  refer to \<^emph>\<open>all\<close> theories used in the original session build process.

  \<^medskip> Options \<^verbatim>\<open>-m\<close> and \<^verbatim>\<open>-U\<close> modify pretty printing and output of Isabelle
  symbols. The default is for an old-fashioned ASCII terminal at 80 characters
  per line (76 + 4 characters to prefix warnings or errors).

  \<^medskip> Option \<^verbatim>\<open>-v\<close> prints all messages from the session database that are
  normally inlined into the source text, including information messages etc.

  \<^medskip> Options \<^verbatim>\<open>-H\<close> and \<^verbatim>\<open>-M\<close> filter messages according to their header or body
  content, respectively. The header follows a very basic format that makes it
  easy to match message kinds (e.g. \<^verbatim>\<open>Warning\<close> or \<^verbatim>\<open>Error\<close>) and file names
  (e.g. \<^verbatim>\<open>src/HOL/Nat.thy\<close>). The body is usually pretty-printed, but for
  matching it is treated like one long line: blocks are ignored and breaks are
  turned into plain spaces (according to their formal width).

  The syntax for patters follows regular expressions of the Java
  platform.\<^footnote>\<open>\<^url>\<open>https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/regex/Pattern.html\<close>\<close>
\<close>

subsubsection \<open>Examples\<close>

text \<open>
  Print messages from theory \<^verbatim>\<open>HOL.Nat\<close> of session \<^verbatim>\<open>HOL\<close>, using Unicode
  rendering of Isabelle symbols and a margin of 100 characters:
  @{verbatim [display] \<open>  isabelle build_log -T HOL.Nat -U -m 100 HOL\<close>}

  Print warnings about ambiguous input (inner syntax) of session
  \<^verbatim>\<open>HOL-Library\<close>, which is built beforehand:
  @{verbatim [display] \<open>  isabelle build HOL-Library
  isabelle build_log -H "Warning" -M "Ambiguous input" HOL-Library\<close>}

  Print all errors from all sessions, e.g. from a partial build of
  Isabelle/AFP:
  @{verbatim [display] \<open>  isabelle build_log -H "Error" $(isabelle sessions -a -d AFP/thys)\<close>}
\<close>


section \<open>Retrieve theory exports \label{sec:tool-export}\<close>

text \<open>
  The @{tool_def "export"} tool retrieves theory exports from the session
  database. Its command-line usage is: @{verbatim [display]
\<open>Usage: isabelle export [OPTIONS] SESSION

  Options are:
    -O DIR       output directory for exported files (default: "export")
    -d DIR       include session directory
    -l           list exports
    -n           no build of session
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p NUM       prune path of exported files by NUM elements
    -x PATTERN   extract files matching pattern (e.g. "*:**" for all)

  List or export theory exports for SESSION: named blobs produced by
  isabelle build. Option -l or -x is required; option -x may be repeated.

  The PATTERN language resembles glob patterns in the shell, with ? and *
  (both excluding ":" and "/"), ** (excluding ":"), and [abc] or [^abc],
  and variants {pattern1,pattern2,pattern3}.\<close>}

  \<^medskip>
  The specified session is updated via @{tool build}
  (\secref{sec:tool-build}), with the same options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-o\<close>. The option
  \<^verbatim>\<open>-n\<close> suppresses the implicit build process: it means that a potentially
  outdated session database is used!

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> lists all stored exports, with compound names
  \<open>theory\<close>\<^verbatim>\<open>:\<close>\<open>name\<close>.

  \<^medskip>
  Option \<^verbatim>\<open>-x\<close> extracts stored exports whose compound name matches the given
  pattern. Note that wild cards ``\<^verbatim>\<open>?\<close>'' and ``\<^verbatim>\<open>*\<close>'' do not match the
  separators ``\<^verbatim>\<open>:\<close>'' and ``\<^verbatim>\<open>/\<close>''; the wild card \<^verbatim>\<open>**\<close> matches over directory
  name hierarchies separated by ``\<^verbatim>\<open>/\<close>''. Thus the pattern ``\<^verbatim>\<open>*:**\<close>'' matches
  \<^emph>\<open>all\<close> theory exports. Multiple options \<^verbatim>\<open>-x\<close> refer to the union of all
  specified patterns.

  Option \<^verbatim>\<open>-O\<close> specifies an alternative output directory for option \<^verbatim>\<open>-x\<close>: the
  default is \<^verbatim>\<open>export\<close> within the current directory. Each theory creates its
  own sub-directory hierarchy, using the session-qualified theory name.

  Option \<^verbatim>\<open>-p\<close> specifies the number of elements that should be pruned from
  each name: it allows to reduce the resulting directory hierarchy at the
  danger of overwriting files due to loss of uniqueness.
\<close>


section \<open>Dump PIDE session database \label{sec:tool-dump}\<close>

text \<open>
  The @{tool_def "dump"} tool dumps information from the cumulative PIDE
  session database (which is processed on the spot). Its command-line usage
  is: @{verbatim [display]
\<open>Usage: isabelle dump [OPTIONS] [SESSIONS ...]

  Options are:
    -A NAMES     dump named aspects (default: ...)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -O DIR       output directory for dumped files (default: "dump")
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b NAME      base logic image (default "Pure")
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Dump cumulative PIDE session database, with the following aspects:
    ...\<close>}

  \<^medskip> Options \<^verbatim>\<open>-B\<close>, \<^verbatim>\<open>-D\<close>, \<^verbatim>\<open>-R\<close>, \<^verbatim>\<open>-X\<close>, \<^verbatim>\<open>-a\<close>, \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-g\<close>, \<^verbatim>\<open>-x\<close> and the
  remaining command-line arguments specify sessions as in @{tool build}
  (\secref{sec:tool-build}): the cumulative PIDE database of all their loaded
  theories is dumped to the output directory of option \<^verbatim>\<open>-O\<close> (default: \<^verbatim>\<open>dump\<close>
  in the current directory).

  \<^medskip> Option \<^verbatim>\<open>-b\<close> specifies an optional base logic image, for improved
  scalability of the PIDE session. Its theories are only processed if it is
  included in the overall session selection.

  \<^medskip> Option \<^verbatim>\<open>-o\<close> overrides Isabelle system options as for @{tool build}
  (\secref{sec:tool-build}).

  \<^medskip> Option \<^verbatim>\<open>-v\<close> increases the general level of verbosity.

  \<^medskip> Option \<^verbatim>\<open>-A\<close> specifies named aspects of the dump, as a comma-separated
  list. The default is to dump all known aspects, as given in the command-line
  usage of the tool. The underlying Isabelle/Scala operation
  \<^scala_method>\<open>isabelle.Dump.dump\<close> takes aspects as user-defined
  operations on the final PIDE state and document version. This allows to
  imitate Prover IDE rendering under program control.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Dump all Isabelle/ZF sessions (which are rather small):
  @{verbatim [display] \<open>  isabelle dump -v -B ZF\<close>}

  \<^smallskip>
  Dump the quite substantial \<^verbatim>\<open>HOL-Analysis\<close> session, with full bootstrap
  from Isabelle/Pure:
  @{verbatim [display] \<open>  isabelle dump -v HOL-Analysis\<close>}

  \<^smallskip>
  Dump all sessions connected to HOL-Analysis, using main Isabelle/HOL as
  basis:
  @{verbatim [display] \<open>  isabelle dump -v -b HOL -B HOL-Analysis\<close>}

  This results in uniform PIDE markup for everything, except for the
  Isabelle/Pure bootstrap process itself. Producing that on the spot requires
  several GB of heap space, both for the Isabelle/Scala and Isabelle/ML
  process (in 64bit mode). Here are some relevant settings (\secref{sec:boot})
  for such ambitious applications:
  @{verbatim [display]
\<open>  ISABELLE_TOOL_JAVA_OPTIONS="-Xms4g -Xmx32g -Xss16m"
  ML_OPTIONS="--minheap 4G --maxheap 32G"
\<close>}
\<close>


section \<open>Update theory sources based on PIDE markup \label{sec:tool-update}\<close>

text \<open>
  The @{tool_def "update"} tool updates theory sources based on markup that is
  produced by the regular @{tool build} process \secref{sec:tool-build}). Its
  command-line usage is: @{verbatim [display]
\<open>Usage: isabelle update [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -l NAME      additional base logic
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u OPT       override "update" option for selected sessions
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Update theory sources based on PIDE markup produced by "isabelle build".\<close>}

  \<^medskip> Most options are the same as for @{tool build} (\secref{sec:tool-build}).

  \<^medskip> Option \<^verbatim>\<open>-l\<close> specifies one or more base logics: these sessions and their
  ancestors are \<^emph>\<open>excluded\<close> from the update.

  \<^medskip> Option \<^verbatim>\<open>-u\<close> refers to specific \<^verbatim>\<open>update\<close> options, by relying on naming
  convention: ``\<^verbatim>\<open>-u\<close>~\<open>OPT\<close>'' is a shortcut for ``\<^verbatim>\<open>-o\<close>~\<^verbatim>\<open>update_\<close>\<open>OPT\<close>''.

  \<^medskip> The following \<^verbatim>\<open>update\<close> options are supported:

    \<^item> @{system_option_ref update_inner_syntax_cartouches} to update inner
    syntax (types, terms, etc.)~to use cartouches, instead of double-quoted
    strings or atomic identifiers. For example, ``\<^theory_text>\<open>lemma \<doublequote>x =
    x\<doublequote>\<close>'' is replaced by ``\<^theory_text>\<open>lemma \<open>x = x\<close>\<close>'', and ``\<^theory_text>\<open>assume
    A\<close>'' is replaced by ``\<^theory_text>\<open>assume \<open>A\<close>\<close>''.

    \<^item> @{system_option update_mixfix_cartouches} to update mixfix templates to
    use cartouches instead of double-quoted strings. For example, ``\<^theory_text>\<open>(infixl
    \<doublequote>+\<doublequote> 65)\<close>'' is replaced by ``\<^theory_text>\<open>(infixl \<open>+\<close>
    65)\<close>''.

    \<^item> @{system_option_ref update_control_cartouches} to update antiquotations
    to use the compact form with control symbol and cartouche argument. For
    example, ``\<open>@{term \<doublequote>x + y\<doublequote>}\<close>'' is replaced by
    ``\<open>\<^term>\<open>x + y\<close>\<close>'' (the control symbol is literally \<^verbatim>\<open>\<^term>\<close>.)

    \<^item> @{system_option_ref update_path_cartouches} to update file-system paths
    to use cartouches: this depends on language markup provided by semantic
    processing of parsed input.

    \<^item> @{system_option_ref update_cite} to update {\LaTeX} \<^verbatim>\<open>\cite\<close> commands
    and old-style \<^verbatim>\<open>@{cite "name"}\<close> document antiquotations.

  It is also possible to produce custom updates in Isabelle/ML, by reporting
  \<^ML>\<open>Markup.update\<close> with the precise source position and a replacement
  text. This operation should be made conditional on specific system options,
  similar to the ones above. Searching the above option names in ML sources of
  \<^dir>\<open>$ISABELLE_HOME/src/Pure\<close> provides some examples.

  Updates can be in conflict by producing nested or overlapping edits: this
  may require to run @{tool update} multiple times.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Update some cartouche notation in all theory sources required for session
  \<^verbatim>\<open>HOL-Analysis\<close> (and ancestors):

  @{verbatim [display] \<open>  isabelle update -u mixfix_cartouches HOL-Analysis\<close>}

  \<^smallskip> Update the same for all application sessions based on \<^verbatim>\<open>HOL-Analysis\<close>, but
  do not change the underlying \<^verbatim>\<open>HOL\<close> (and \<^verbatim>\<open>Pure\<close>) session:

  @{verbatim [display] \<open>  isabelle update -u mixfix_cartouches -l HOL -B HOL-Analysis\<close>}

  \<^smallskip> Update all sessions that happen to be properly built beforehand:

  @{verbatim [display] \<open>  isabelle update -u mixfix_cartouches -n -a\<close>}
\<close>


section \<open>Explore sessions structure\<close>

text \<open>
  The @{tool_def "sessions"} tool explores the sessions structure. Its
  command-line usage is:
  @{verbatim [display]
\<open>Usage: isabelle sessions [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           follow session build dependencies (default: source imports)
    -d DIR       include session directory
    -g NAME      select session group NAME
    -x NAME      exclude session NAME and all descendants

  Explore the structure of Isabelle sessions and print result names in
  topological order (on stdout).\<close>}

  Arguments and options for session selection resemble @{tool build}
  (\secref{sec:tool-build}).
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  All sessions of the Isabelle distribution:
  @{verbatim [display] \<open>  isabelle sessions -a\<close>}

  \<^medskip>
  Sessions that are imported by \<^verbatim>\<open>ZF\<close>:
  @{verbatim [display] \<open>  isabelle sessions ZF\<close>}

  \<^medskip>
  Sessions that are required to build \<^verbatim>\<open>ZF\<close>:
  @{verbatim [display] \<open>  isabelle sessions -b ZF\<close>}

  \<^medskip>
  Sessions that are based on \<^verbatim>\<open>ZF\<close> (and imported by it):
  @{verbatim [display] \<open>  isabelle sessions -B ZF\<close>}

  \<^medskip>
  All sessions of Isabelle/AFP (based in directory \<^path>\<open>AFP\<close>):
  @{verbatim [display] \<open>  isabelle sessions -D AFP/thys\<close>}

  \<^medskip>
  Sessions required by Isabelle/AFP (based in directory \<^path>\<open>AFP\<close>):
  @{verbatim [display] \<open>  isabelle sessions -R -D AFP/thys\<close>}
\<close>


section \<open>Synchronize source repositories and session images for Isabelle and AFP\<close>

text \<open>
  The @{tool_def sync} tool synchronizes a local Isabelle and AFP source
  repository, possibly with prebuilt \<^verbatim>\<open>.jar\<close> files and session images. Its
  command-line usage is: @{verbatim [display]
\<open>Usage: isabelle sync [OPTIONS] TARGET

  Options are:
    -A ROOT      include AFP with given root directory (":" for $AFP_BASE)
    -H           purge heaps directory on target
    -I NAME      include session heap image and build database
                 (based on accidental local state)
    -J           preserve *.jar files
    -T           thorough treatment of file content and directory times
    -a REV       explicit AFP revision (default: state of working directory)
    -s HOST      SSH host name for remote target (default: local)
    -u USER      explicit SSH user name
    -n           no changes: dry-run
    -p PORT      explicit SSH port
    -r REV       explicit revision (default: state of working directory)
    -v           verbose

  Synchronize Isabelle + AFP repositories, based on "isabelle hg_sync".\<close>}

  The approach is to apply @{tool hg_sync} (see \secref{sec:tool-hg-sync}) on
  the underlying Isabelle repository, and an optional AFP repository.
  Consequently, the Isabelle installation needs to be a Mercurial repository
  clone: a regular download of the Isabelle distribution is not sufficient!

  On the target side, AFP is placed into @{setting ISABELLE_HOME} as immediate
  sub-directory with the literal name \<^verbatim>\<open>AFP\<close>; thus it can be easily included
  elsewhere, e.g. @{tool build}~\<^verbatim>\<open>-d\<close>~\<^verbatim>\<open>'~~/AFP'\<close> on the remote side.

  \<^medskip> Options \<^verbatim>\<open>-T\<close>, \<^verbatim>\<open>-n\<close>, \<^verbatim>\<open>-p\<close>, \<^verbatim>\<open>-s\<close>, \<^verbatim>\<open>-u\<close>, \<^verbatim>\<open>-v\<close> are the same as
  the underlying @{tool hg_sync}.

  \<^medskip> Options \<^verbatim>\<open>-r\<close> and \<^verbatim>\<open>-a\<close> are the same as option \<^verbatim>\<open>-r\<close> for @{tool hg_sync},
  but for the Isabelle and AFP repositories, respectively. The AFP version is
  only used if a corresponding repository is given via option \<^verbatim>\<open>-A\<close>, either
  with explicit root directory, or as \<^verbatim>\<open>-A:\<close> to refer to \<^verbatim>\<open>$AFP_BASE\<close> (this
  assumes AFP as component of the local Isabelle installation). If no AFP
  repository is given, an existing \<^verbatim>\<open>AFP\<close> directory on the target remains
  unchanged.

  \<^medskip> Option \<^verbatim>\<open>-J\<close> uploads existing \<^verbatim>\<open>.jar\<close> files from the working directory,
  which are usually Isabelle/Scala/Java modules under control of @{tool
  scala_build} via \<^verbatim>\<open>etc/build.props\<close> (see also \secref{sec:scala-build}).
  Thus the dependency management is accurate: bad uploads will be rebuilt
  eventually (or ignored). This might fail for very old Isabelle versions,
  when going into the past via option \<^verbatim>\<open>-r\<close>: here it is better to omit option
  \<^verbatim>\<open>-J\<close> and thus purge \<^verbatim>\<open>.jar\<close> files on the target (because they do not belong
  to the repository).

  \<^medskip> Option \<^verbatim>\<open>-I\<close> uploads a collection of session images. The set of \<^verbatim>\<open>-I\<close>
  options specifies the end-points in the session build graph, including all
  required ancestors. The result collection is uploaded using the underlying
  \<^verbatim>\<open>rsync\<close> policies, so unchanged images are not sent again. Session images
  are assembled within the target \<^verbatim>\<open>heaps\<close> directory: this scheme fits
  together with @{tool build}~\<^verbatim>\<open>-o system_heaps\<close>. Images are taken as-is from
  the local Isabelle installation, regardless of option \<^verbatim>\<open>-r\<close>. Upload of bad
  images could waste time and space, but running e.g. @{tool build} on the
  target will check dependencies accurately and rebuild outdated images on
  demand.

  \<^medskip> Option \<^verbatim>\<open>-H\<close> tells the underlying \<^verbatim>\<open>rsync\<close> process to purge the \<^verbatim>\<open>heaps\<close>
  directory on the target, before uploading new images via option \<^verbatim>\<open>-I\<close>. The
  default is to work monotonically: old material that is not overwritten
  remains unchanged. Over time, this may lead to unused garbage, due to
  changes in session names or the Poly/ML version. Option \<^verbatim>\<open>-H\<close> helps to avoid
  wasting file-system space.
\<close>

subsubsection \<open>Examples\<close>

text \<open>
  For quick testing of Isabelle + AFP on a remote machine, upload changed
  sources, jars, and local sessions images for \<^verbatim>\<open>HOL\<close>:

  @{verbatim [display] \<open>  isabelle sync -A: -I HOL -J -s testmachine test/isabelle_afp\<close>}
  Assuming that the local \<^verbatim>\<open>HOL\<close> hierarchy has been up-to-date, and the local
  and remote ML platforms coincide, a remote @{tool build} will proceed
  without building \<^verbatim>\<open>HOL\<close> again.

  \<^medskip> Here is a variation for extra-clean testing of Isabelle + AFP: no option
  \<^verbatim>\<open>-J\<close>, but option \<^verbatim>\<open>-T\<close> to disable the default ``quick check'' of \<^verbatim>\<open>rsync\<close>
  (which only inspects file sizes and date stamps); existing heaps are
  deleted:
  @{verbatim [display] \<open>  isabelle sync -A: -T -H -s testmachine test/isabelle_afp\<close>}
\<close>


section \<open>Remote build management\<close>

text \<open>
  Building large collections of Isabelle session (e.g., the AFP) is an
  expensive operation that might not be feasible on a local device, so
  powerful remote hardware is necessary to be able to test changes quickly.
  In a multi-user environment, these hardware resources must be managed such
  that important tasks can be completed as soon as possible, and automated
  tasks run in the background when necessary.
\<close>

subsection \<open>Build manager server\<close>

text \<open>
  The @{tool_def build_manager} tool starts a server process that manages
  a queue of tasks, runs build jobs, and serves a web view that displays the
  results. It consists of several threads:
  
    \<^item> \<^emph>\<open>poller\<close>: listens to repository updates and queues automatic tasks.
  
    \<^item> \<^emph>\<open>timer\<close>: queues periodic tasks at specific points in time.
  
    \<^item> \<^emph>\<open>runner\<close>: starts jobs for feasible tasks with the highest priority
    whenever possible. Jobs run exclusively on their resources, either on the
    cluster specified via @{system_option build_manager_cluster} (the 
    connection to the \<^verbatim>\<open>build_master\<close> host must be specified via
    \<^verbatim>\<open>build_manager_cluster_ssh\<close> connection options), or on a single remote
    host (under the identifier given by
    @{system_option build_manager_identifier}).
  
    \<^item> \<^emph>\<open>web_server\<close>: serves the web page. If the web address is not reachable
    under the SSH hostname of the server, it must be set via 
    @{system_option build_manager_address}.

  Automated tasks must be registered in a \<^scala_type>\<open>isabelle.Isabelle_CI_Jobs\<close>
  service. The system option @{system_option build_manager_ci_jobs} controls
  which jobs are executed by the \<^verbatim>\<open>Build_Manager\<close>.

  \<^medskip>
  The command-line usage to start the server is:
  @{verbatim [display]
\<open>Usage: isabelle build_manager [OPTIONS]

  Options are:
    -A ROOT      include AFP with given root directory (":" for $AFP_BASE)
    -D DIR       include extra component in given directory
    -H HOSTS     host specifications for all available hosts of the form
                 NAMES:PARAMETERS (separated by commas)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit web server port

  Run Isabelle build manager.
\<close>}

  \<^medskip> Option \<^verbatim>\<open>-o\<close> has the same meaning as for @{tool build}.

  \<^medskip> Option \<^verbatim>\<open>-p\<close> has the same meaning as for @{tool server}.

  \<^medskip> Option \<^verbatim>\<open>-A\<close> refers to the AFP (must be a Mercurial clone).

  \<^medskip> Option \<^verbatim>\<open>-D\<close> extra Isabelle components in a Mercurial repository clone to
  be considered by the poller and CI jobs.

  \<^medskip> Option \<^verbatim>\<open>-H\<close> must list all host specifications to be used in the build
  cluster or as remote host.

  \<^medskip>
  In case a job does not complete on its own, it is terminated after a timeout
  defined by the CI job, or @{system_option build_manager_timeout} for
  user-submitted tasks.

  \<^medskip>
  To gracefully stop the build manager, it should be sent an interrupt signal
  (\<^verbatim>\<open>kill -INT\<close>). This will stop all threads gracefully: Any running build is
  allowed to complete before the Isabelle process terminates.

  \<^medskip>
  The build manager stores its persistent data (including user-submitted tasks
  and build logs) in the directory given by @{system_option build_manager_dir}.
  It must be writable by the common Unix group specified in
  @{system_option build_manager_group}. It also needs a PostgreSQL database 
  (via \<^verbatim>\<open>build_manager_database\<close> connection options) for shared state.
  A clean database state (e.g., after a schema update) can be restored from
  build logs via the @{tool_def build_manager_database} tool:
  @{verbatim [display]
\<open>Usage: isabelle build_manager_database [OPTIONS]

  Options are:
    -A ROOT      include AFP with given root directory (":" for $AFP_BASE)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u           update reports

  Restore build_manager database from log files.
\<close>}

  Options \<^verbatim>\<open>-A\<close> and \<^verbatim>\<open>-o\<close> are the same as in @{tool_ref build_manager}.

  Option \<^verbatim>\<open>-u\<close> updates Mercurial reports in the persistent storage based on
  the version history (e.g., to change the diff display in the web server).
\<close>

subsection \<open>Submitting build tasks\<close>

text \<open>
  The @{tool_def build_task} tool submits user-defined build tasks by syncing
  the local Isabelle repository to the server and queuing a task in the shared
  state. Command-line options are almost identical to the regular @{tool_ref 
  build}, with the exception of preferences in the remote build.

  For the SSH connection, the server needs to be accessible with the system
  options @{system_option build_manager_ssh_user}, @{system_option 
  build_manager_ssh_host}, etc.

  The database needs to be configured similarly (via \<^verbatim>\<open>build_manager_database\<close>
  connection options) though the PostgreSQL server can also be configured
  to trust connections of logged in users via ``peer authentication''.
\<close>

subsubsection \<open>Examples\<close>

text \<open>
Clean build of the distribution:

  @{verbatim [display] \<open>  isabelle build_task -c -a\<close>}

Build all sessions in the AFP excluding the \<^verbatim>\<open>very_slow\<close> group:

  @{verbatim [display] \<open>  isabelle build_task -A: -X slow -g AFP\<close>}
\<close>


section \<open>Process theories within a session context \label{sec:tool-process-theories}\<close>

text \<open>
  The @{tool_def process_theories} tool takes source files and theories from
  existing sessions to compose an adhoc session (in a temporary directory)
  that is then processed via regular @{tool build}. It is also possible to
  output prover messages roughly like @{tool build_log}, while the theories
  are being processed.

  @{verbatim [display]
\<open>Usage: isabelle process_theories [OPTIONS] [THEORIES...]

  Options are:
    -F FILE      include addition session files, listed in FILE
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -O           output messages
    -U           output Unicode symbols
    -d DIR       include session directory
    -f FILE      include addition session files
    -l NAME      logic session name (default ISABELLE_LOGIC="HOL")
    -m MARGIN    margin for pretty printing (default: 76.0)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose

  Process theories within an adhoc session context.
\<close>}

  Explicit \<^emph>\<open>theories\<close> given as command-line arguments, not options, refer to
  qualified theory names from existing sessions, e.g. \<^verbatim>\<open>HOL-Library.Multiset\<close>
  or \<^verbatim>\<open>HOL-Examples.Seq\<close>. The session qualifiers are used to augment the adhoc
  session specification by suitable entries for \isakeyword{sessions}
  (\secref{sec:session-root}).

  \<^medskip>
  Options \<^verbatim>\<open>-f\<close> and \<^verbatim>\<open>-F\<close> specify source files for the adhoc session directory
  (multiple occurrences are possible): \<^verbatim>\<open>-f\<close> is for literal file names, and
  \<^verbatim>\<open>-F\<close> is for files that contain a list of further files (one per line).

  All source files are copied to the private (temporary) session directory,
  without any subdirectory structure. Files with extension \<^verbatim>\<open>.thy\<close> are treated
  as theory files: their base names are appended to the overall list of
  \<^emph>\<open>theories\<close>, and thus loaded into the adhoc session, too.

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> specifies the parent logic session, which is produced on the
  spot using @{tool build}. Options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-o\<close>, \<^verbatim>\<open>-v\<close> work as in @{tool
  build}.

  Option \<^verbatim>\<open>-O\<close> enables output of prover messages. Options \<^verbatim>\<open>-H\<close>, \<^verbatim>\<open>-M\<close>, \<^verbatim>\<open>-U\<close>,
  \<^verbatim>\<open>-m\<close> work as in @{tool build_log}.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Process a theory from a different session in the context of the default
  logic (\<^verbatim>\<open>HOL\<close>):

  @{verbatim [display] \<open>  isabelle process_theories HOL-Library.Multiset\<close>}

  \<^smallskip>
  Process a theory with prover output enabled (using Unicode symbols):
  @{verbatim [display] \<open>  isabelle process_theories -U -O HOL-Library.Multiset\<close>}

  \<^smallskip>
  Process a theory with prover output enabled, including proof states:
  @{verbatim [display] \<open>  isabelle process_theories -U -O -o show_states HOL-Library.Multiset\<close>}

  \<^smallskip>
  Process a self-contained theory file from the Isabelle distribution, outside
  of its original session context:
  @{verbatim [display] \<open>  isabelle process_theories -f '~~/src/HOL/Examples/Seq.thy'\<close>}

\<close>

end
