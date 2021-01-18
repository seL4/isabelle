(*:maxLineLen=78:*)

theory Environment
imports Base
begin

chapter \<open>The Isabelle system environment\<close>

text \<open>
  This manual describes Isabelle together with related tools as seen from a
  system oriented view. See also the \<^emph>\<open>Isabelle/Isar Reference Manual\<close> @{cite
  "isabelle-isar-ref"} for the actual Isabelle input language and related
  concepts, and \<^emph>\<open>The Isabelle/Isar Implementation Manual\<close> @{cite
  "isabelle-implementation"} for the main concepts of the underlying
  implementation in Isabelle/ML.
\<close>


section \<open>Isabelle settings \label{sec:settings}\<close>

text \<open>
  Isabelle executables may depend on the \<^emph>\<open>Isabelle settings\<close> within the
  process environment. This is a statically scoped collection of environment
  variables, such as @{setting ISABELLE_HOME}, @{setting ML_SYSTEM}, @{setting
  ML_HOME}. These variables are \<^emph>\<open>not\<close> intended to be set directly from the
  shell, but are provided by Isabelle \<^emph>\<open>components\<close> their \<^emph>\<open>settings files\<close> as
  explained below.
\<close>


subsection \<open>Bootstrapping the environment \label{sec:boot}\<close>

text \<open>
  Isabelle executables need to be run within a proper settings environment.
  This is bootstrapped as described below, on the first invocation of one of
  the outer wrapper scripts (such as @{executable_ref isabelle}). This happens
  only once for each process tree, i.e.\ the environment is passed to
  subprocesses according to regular Unix conventions.

    \<^enum> The special variable @{setting_def ISABELLE_HOME} is determined
    automatically from the location of the binary that has been run.

    You should not try to set @{setting ISABELLE_HOME} manually. Also note
    that the Isabelle executables either have to be run from their original
    location in the distribution directory, or via the executable objects
    created by the @{tool install} tool. Symbolic links are admissible, but a
    plain copy of the \<^dir>\<open>$ISABELLE_HOME/bin\<close> files will not work!

    \<^enum> The file \<^file>\<open>$ISABELLE_HOME/etc/settings\<close> is run as a @{executable_ref
    bash} shell script with the auto-export option for variables enabled.

    This file holds a rather long list of shell variable assignments, thus
    providing the site-wide default settings. The Isabelle distribution
    already contains a global settings file with sensible defaults for most
    variables. When installing the system, only a few of these may have to be
    adapted (probably @{setting ML_SYSTEM} etc.).

    \<^enum> The file \<^path>\<open>$ISABELLE_HOME_USER/etc/settings\<close> (if it
    exists) is run in the same way as the site default settings. Note that the
    variable @{setting ISABELLE_HOME_USER} has already been set before ---
    usually to something like \<^verbatim>\<open>$USER_HOME/.isabelle/Isabelle2021\<close>.

    Thus individual users may override the site-wide defaults. Typically, a
    user settings file contains only a few lines, with some assignments that
    are actually changed. Never copy the central
    \<^file>\<open>$ISABELLE_HOME/etc/settings\<close> file!

  Since settings files are regular GNU @{executable_def bash} scripts, one may
  use complex shell commands, such as \<^verbatim>\<open>if\<close> or \<^verbatim>\<open>case\<close> statements to set
  variables depending on the system architecture or other environment
  variables. Such advanced features should be added only with great care,
  though. In particular, external environment references should be kept at a
  minimum.

  \<^medskip>
  A few variables are somewhat special, e.g.\ @{setting_def ISABELLE_TOOL} is
  set automatically to the absolute path name of the @{executable isabelle}
  executables.

  \<^medskip>
  Note that the settings environment may be inspected with the @{tool getenv}
  tool. This might help to figure out the effect of complex settings scripts.
\<close>


subsection \<open>Common variables\<close>

text \<open>
  This is a reference of common Isabelle settings variables. Note that the
  list is somewhat open-ended. Third-party utilities or interfaces may add
  their own selection. Variables that are special in some sense are marked
  with \<open>\<^sup>*\<close>.

  \<^descr>[@{setting_def USER_HOME}\<open>\<^sup>*\<close>] Is the cross-platform user home directory.
  On Unix systems this is usually the same as @{setting HOME}, but on Windows
  it is the regular home directory of the user, not the one of within the
  Cygwin root file-system.\<^footnote>\<open>Cygwin itself offers another choice whether its
  HOME should point to the \<^path>\<open>/home\<close> directory tree or the Windows user
  home.\<close>

  \<^descr>[@{setting_def ISABELLE_HOME}\<open>\<^sup>*\<close>] is the location of the top-level
  Isabelle distribution directory. This is automatically determined from the
  Isabelle executable that has been invoked. Do not attempt to set @{setting
  ISABELLE_HOME} yourself from the shell!

  \<^descr>[@{setting_def ISABELLE_HOME_USER}] is the user-specific counterpart of
  @{setting ISABELLE_HOME}. The default value is relative to \<^path>\<open>$USER_HOME/.isabelle\<close>, under rare circumstances this may be changed in the
  global setting file. Typically, the @{setting ISABELLE_HOME_USER} directory
  mimics @{setting ISABELLE_HOME} to some extend. In particular, site-wide
  defaults may be overridden by a private \<^verbatim>\<open>$ISABELLE_HOME_USER/etc/settings\<close>.

  \<^descr>[@{setting_def ISABELLE_PLATFORM_FAMILY}\<open>\<^sup>*\<close>] is automatically set to the
  general platform family: \<^verbatim>\<open>linux\<close>, \<^verbatim>\<open>macos\<close>, \<^verbatim>\<open>windows\<close>. Note that
  platform-dependent tools usually need to refer to the more specific
  identification according to @{setting ISABELLE_PLATFORM64}, @{setting
  ISABELLE_PLATFORM32}, @{setting ISABELLE_WINDOWS_PLATFORM64}, @{setting
  ISABELLE_WINDOWS_PLATFORM32}.

  \<^descr>[@{setting_def ISABELLE_PLATFORM64}\<open>\<^sup>*\<close>, @{setting_def
  ISABELLE_PLATFORM32}\<open>\<^sup>*\<close>] indicate the standard Posix platform: \<^verbatim>\<open>x86_64\<close>
  for 64 bit and \<^verbatim>\<open>x86\<close> for 32 bit, together with a symbolic name for the
  operating system (\<^verbatim>\<open>linux\<close>, \<^verbatim>\<open>darwin\<close>, \<^verbatim>\<open>cygwin\<close>). All platforms support 64
  bit executables, some platforms also support 32 bit executables.

  In GNU bash scripts, it is possible to use the following expressions (with
  quotes) to specify a preference of 64 bit over 32 bit:

  @{verbatim [display] \<open>"${ISABELLE_PLATFORM64:-$ISABELLE_PLATFORM32}"\<close>}

  In contrast, the subsequent expression prefers the old 32 bit variant (which
  is only relevant for unusual applications):

  @{verbatim [display] \<open>"${ISABELLE_PLATFORM32:-$ISABELLE_PLATFORM64}"\<close>}

  \<^descr>[@{setting_def ISABELLE_WINDOWS_PLATFORM64}\<open>\<^sup>*\<close>, @{setting_def
  ISABELLE_WINDOWS_PLATFORM32}\<open>\<^sup>*\<close>] indicate the native Windows platform.
  These settings are analogous (but independent) of those for the standard
  Posix subsystem: @{setting ISABELLE_PLATFORM64}, @{setting
  ISABELLE_PLATFORM32}.

  In GNU bash scripts, a preference for native Windows platform variants may
  be specified like this (first 64 bit, second 32 bit):

  @{verbatim [display] \<open>"${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_WINDOWS_PLATFORM32:-
  ${ISABELLE_PLATFORM64:-$ISABELLE_PLATFORM32}}}"\<close>}

  \<^descr>[@{setting ISABELLE_TOOL}\<open>\<^sup>*\<close>] is automatically set to the full path name
  of the @{executable isabelle} executable.

  \<^descr>[@{setting_def ISABELLE_IDENTIFIER}\<open>\<^sup>*\<close>] refers to the name of this
  Isabelle distribution, e.g.\ ``\<^verbatim>\<open>Isabelle2021\<close>''.

  \<^descr>[@{setting_def ML_SYSTEM}, @{setting_def ML_HOME}, @{setting_def
  ML_OPTIONS}, @{setting_def ML_PLATFORM}, @{setting_def ML_IDENTIFIER}\<open>\<^sup>*\<close>]
  specify the underlying ML system to be used for Isabelle. There is only a
  fixed set of admissable @{setting ML_SYSTEM} names (see the
  \<^file>\<open>$ISABELLE_HOME/etc/settings\<close> file of the distribution).

  The actual compiler binary will be run from the directory @{setting
  ML_HOME}, with @{setting ML_OPTIONS} as first arguments on the command line.
  The optional @{setting ML_PLATFORM} may specify the binary format of ML heap
  images, which is useful for cross-platform installations. The value of
  @{setting ML_IDENTIFIER} is automatically obtained by composing the values
  of @{setting ML_SYSTEM}, @{setting ML_PLATFORM} and the Isabelle version
  values.

  \<^descr>[@{setting_def ISABELLE_JDK_HOME}] points to a full JDK (Java Development
  Kit) installation with \<^verbatim>\<open>javac\<close> and \<^verbatim>\<open>jar\<close> executables. Note that
  conventional \<^verbatim>\<open>JAVA_HOME\<close> points to the JRE (Java Runtime Environment), not
  the JDK.

  \<^descr>[@{setting_def ISABELLE_JAVA_PLATFORM}] identifies the hardware and
  operating system platform for the Java installation of Isabelle. That is
  always the (native) 64 bit variant: \<^verbatim>\<open>x86_64-linux\<close>, \<^verbatim>\<open>x86_64-darwin\<close>,
  \<^verbatim>\<open>x86_64-windows\<close>.

  \<^descr>[@{setting_def ISABELLE_BROWSER_INFO}] is the directory where HTML and PDF
  browser information is stored (see also \secref{sec:info}); its default is
  \<^path>\<open>$ISABELLE_HOME_USER/browser_info\<close>. For ``system build mode'' (see
  \secref{sec:tool-build}), @{setting_def ISABELLE_BROWSER_INFO_SYSTEM} is
  used instead; its default is \<^path>\<open>$ISABELLE_HOME/browser_info\<close>.

  \<^descr>[@{setting_def ISABELLE_HEAPS}] is the directory where session heap images,
  log files, and build databases are stored; its default is
  \<^path>\<open>$ISABELLE_HOME_USER/heaps\<close>. If @{system_option system_heaps} is
  \<^verbatim>\<open>true\<close>, @{setting_def ISABELLE_HEAPS_SYSTEM} is used instead; its default
  is \<^path>\<open>$ISABELLE_HOME/heaps\<close>. See also \secref{sec:tool-build}.

  \<^descr>[@{setting_def ISABELLE_LOGIC}] specifies the default logic to load if none
  is given explicitely by the user. The default value is \<^verbatim>\<open>HOL\<close>.

  \<^descr>[@{setting_def ISABELLE_LINE_EDITOR}] specifies the line editor for the
  @{tool_ref console} interface.

  \<^descr>[@{setting_def ISABELLE_PDFLATEX}, @{setting_def ISABELLE_BIBTEX}] refer to
  {\LaTeX} related tools for Isabelle document preparation (see also
  \secref{sec:tool-latex}).

  \<^descr>[@{setting_def ISABELLE_TOOLS}] is a colon separated list of directories
  that are scanned by @{executable isabelle} for external utility programs
  (see also \secref{sec:isabelle-tool}).

  \<^descr>[@{setting_def ISABELLE_DOCS}] is a colon separated list of directories
  with documentation files.

  \<^descr>[@{setting_def PDF_VIEWER}] specifies the program to be used for displaying
  \<^verbatim>\<open>pdf\<close> files.

  \<^descr>[@{setting_def ISABELLE_TMP_PREFIX}\<open>\<^sup>*\<close>] is the prefix from which any
  running Isabelle ML process derives an individual directory for temporary
  files.

  \<^descr>[@{setting_def ISABELLE_TOOL_JAVA_OPTIONS}] is passed to the \<^verbatim>\<open>java\<close>
  executable when running Isabelle tools (e.g.\ @{tool build}). This is
  occasionally helpful to provide more heap space, via additional options like
  \<^verbatim>\<open>-Xms1g -Xmx4g\<close>.
\<close>


subsection \<open>Additional components \label{sec:components}\<close>

text \<open>
  Any directory may be registered as an explicit \<^emph>\<open>Isabelle component\<close>. The
  general layout conventions are that of the main Isabelle distribution
  itself, and the following two files (both optional) have a special meaning:

    \<^item> \<^verbatim>\<open>etc/settings\<close> holds additional settings that are initialized when
    bootstrapping the overall Isabelle environment, cf.\ \secref{sec:boot}. As
    usual, the content is interpreted as a GNU bash script. It may refer to
    the component's enclosing directory via the \<^verbatim>\<open>COMPONENT\<close> shell variable.

    For example, the following setting allows to refer to files within the
    component later on, without having to hardwire absolute paths:
    @{verbatim [display] \<open>MY_COMPONENT_HOME="$COMPONENT"\<close>}

    Components can also add to existing Isabelle settings such as
    @{setting_def ISABELLE_TOOLS}, in order to provide component-specific
    tools that can be invoked by end-users. For example:
    @{verbatim [display] \<open>ISABELLE_TOOLS="$ISABELLE_TOOLS:$COMPONENT/lib/Tools"\<close>}

    \<^item> \<^verbatim>\<open>etc/components\<close> holds a list of further sub-components of the same
    structure. The directory specifications given here can be either absolute
    (with leading \<^verbatim>\<open>/\<close>) or relative to the component's main directory.

  The root of component initialization is @{setting ISABELLE_HOME} itself.
  After initializing all of its sub-components recursively, @{setting
  ISABELLE_HOME_USER} is included in the same manner (if that directory
  exists). This allows to install private components via
  \<^path>\<open>$ISABELLE_HOME_USER/etc/components\<close>, although it is often more
  convenient to do that programmatically via the
  \<^bash_function>\<open>init_component\<close> shell function in the \<^verbatim>\<open>etc/settings\<close>
  script of \<^verbatim>\<open>$ISABELLE_HOME_USER\<close> (or any other component directory). For
  example:
  @{verbatim [display] \<open>init_component "$HOME/screwdriver-2.0"\<close>}

  This is tolerant wrt.\ missing component directories, but might produce a
  warning.

  \<^medskip>
  More complex situations may be addressed by initializing components listed
  in a given catalog file, relatively to some base directory:
  @{verbatim [display] \<open>init_components "$HOME/my_component_store" "some_catalog_file"\<close>}

  The component directories listed in the catalog file are treated as relative
  to the given base directory.

  See also \secref{sec:tool-components} for some tool-support for resolving
  components that are formally initialized but not installed yet.
\<close>


section \<open>The Isabelle tool wrapper \label{sec:isabelle-tool}\<close>

text \<open>
  The main \<^emph>\<open>Isabelle tool wrapper\<close> provides a generic startup environment for
  Isabelle-related utilities, user interfaces, add-on applications etc. Such
  tools automatically benefit from the settings mechanism
  (\secref{sec:settings}). Moreover, this is the standard way to invoke
  Isabelle/Scala functionality as a separate operating-system process.
  Isabelle command-line tools are run uniformly via a common wrapper ---
  @{executable_ref isabelle}:
  @{verbatim [display]
\<open>Usage: isabelle TOOL [ARGS ...]

  Start Isabelle TOOL with ARGS; pass "-?" for tool-specific help.

Available tools:
  ...\<close>}

  Tools may be implemented in Isabelle/Scala or as stand-alone executables
  (usually as GNU bash scripts). In the invocation of ``@{executable
  isabelle}~\<open>tool\<close>'', the named \<open>tool\<close> is resolved as follows (and in the
  given order).

    \<^enum> An external tool found on the directories listed in the @{setting
    ISABELLE_TOOLS} settings variable (colon-separated list in standard POSIX
    notation).

      \<^enum> If a file ``\<open>tool\<close>\<^verbatim>\<open>.scala\<close>'' is found, the source needs to define
      some object that extends the class \<^verbatim>\<open>Isabelle_Tool.Body\<close>. The Scala
      compiler is invoked on the spot (which may take some time), and the body
      function is run with the command-line arguments as \<^verbatim>\<open>List[String]\<close>.

      \<^enum> If an executable file ``\<open>tool\<close>'' is found, it is invoked as
      stand-alone program with the command-line arguments provided as \<^verbatim>\<open>argv\<close>
      array.

    \<^enum> An internal tool that is registered in \<^verbatim>\<open>etc/settings\<close> via the shell
    function \<^bash_function>\<open>isabelle_scala_service\<close>, referring to a
    suitable instance of class \<^scala_type>\<open>isabelle.Isabelle_Scala_Tools\<close>.
    This is the preferred approach for non-trivial systems programming in
    Isabelle/Scala: instead of adhoc interpretation of \<^verbatim>\<open>scala\<close> scripts,
    which is somewhat slow and only type-checked at runtime, there are
    properly compiled \<^verbatim>\<open>jar\<close> modules (see also the shell function
    \<^bash_function>\<open>classpath\<close> in \secref{sec:scala}).

  There are also various administrative tools that are available from a bare
  repository clone of Isabelle, but not in regular distributions.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Show the list of available documentation of the Isabelle distribution:
  @{verbatim [display] \<open>isabelle doc\<close>}

  View a certain document as follows:
  @{verbatim [display] \<open>isabelle doc system\<close>}

  Query the Isabelle settings environment:
  @{verbatim [display] \<open>isabelle getenv ISABELLE_HOME_USER\<close>}
\<close>


section \<open>The raw Isabelle ML process\<close>

subsection \<open>Batch mode \label{sec:tool-process}\<close>

text \<open>
  The @{tool_def process} tool runs the raw ML process in batch mode:
  @{verbatim [display]
\<open>Usage: isabelle process [OPTIONS]

  Options are:
    -T THEORY    load theory
    -d DIR       include session directory
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -l NAME      logic session name (default ISABELLE_LOGIC="HOL")
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the raw Isabelle ML process in batch mode.\<close>}

  \<^medskip>
  Options \<^verbatim>\<open>-e\<close> and \<^verbatim>\<open>-f\<close> allow to evaluate ML code, before the ML process is
  started. The source is either given literally or taken from a file. Multiple
  \<^verbatim>\<open>-e\<close> and \<^verbatim>\<open>-f\<close> options are evaluated in the given order. Errors lead to
  premature exit of the ML process with return code 1.

  \<^medskip>
  Option \<^verbatim>\<open>-T\<close> loads a specified theory file. This is a wrapper for \<^verbatim>\<open>-e\<close> with
  a suitable \<^ML>\<open>use_thy\<close> invocation.

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> specifies the logic session name. Option \<^verbatim>\<open>-d\<close> specifies
  additional directories for session roots, see also \secref{sec:tool-build}.

  \<^medskip>
  The \<^verbatim>\<open>-m\<close> option adds identifiers of print modes to be made active for this
  session. For example, \<^verbatim>\<open>-m ASCII\<close> prefers ASCII replacement syntax over
  mathematical Isabelle symbols.

  \<^medskip>
  Option \<^verbatim>\<open>-o\<close> allows to override Isabelle system options for this process,
  see also \secref{sec:system-options}.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  The subsequent example retrieves the \<^verbatim>\<open>Main\<close> theory value from the theory
  loader within ML:
  @{verbatim [display] \<open>isabelle process -e 'Thy_Info.get_theory "Main"'\<close>}

  Observe the delicate quoting rules for the GNU bash shell vs.\ ML. The
  Isabelle/ML and Scala libraries provide functions for that, but here we need
  to do it manually.

  \<^medskip>
  This is how to invoke a function body with proper return code and printing
  of errors, and without printing of a redundant \<^verbatim>\<open>val it = (): unit\<close> result:
  @{verbatim [display] \<open>isabelle process -e 'Command_Line.tool (fn () => writeln "OK")'\<close>}
  @{verbatim [display] \<open>isabelle process -e 'Command_Line.tool (fn () => error "Bad")'\<close>}
\<close>


subsection \<open>Interactive mode\<close>

text \<open>
  The @{tool_def console} tool runs the raw ML process with interactive
  console and line editor:
  @{verbatim [display]
\<open>Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           bootstrap from raw Poly/ML

  Build a logic session image and run the raw Isabelle ML process
  in interactive mode, with line editor ISABELLE_LINE_EDITOR.\<close>}

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> specifies the logic session name. By default, its heap image is
  checked and built on demand, but the option \<^verbatim>\<open>-n\<close> skips that.

  Option \<^verbatim>\<open>-i\<close> includes additional sessions into the name-space of theories:
  multiple occurrences are possible.

  Option \<^verbatim>\<open>-r\<close> indicates a bootstrap from the raw Poly/ML system, which is
  relevant for Isabelle/Pure development.

  \<^medskip>
  Options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-m\<close>, \<^verbatim>\<open>-o\<close> have the same meaning as for @{tool process}
  (\secref{sec:tool-process}).

  \<^medskip>
  The Isabelle/ML process is run through the line editor that is specified via
  the settings variable @{setting ISABELLE_LINE_EDITOR} (e.g.\
  @{executable_def rlwrap} for GNU readline); the fall-back is to use plain
  standard input/output.

  The user is connected to the raw ML toplevel loop: this is neither
  Isabelle/Isar nor Isabelle/ML within the usual formal context. The most
  relevant ML commands at this stage are \<^ML>\<open>use\<close> (for ML files) and
  \<^ML>\<open>use_thy\<close> (for theory files).
\<close>


section \<open>The raw Isabelle Java process \label{sec:isabelle-java}\<close>

text \<open>
  The @{executable_ref isabelle_java} executable allows to run a Java process
  within the name space of Java and Scala components that are bundled with
  Isabelle, but \<^emph>\<open>without\<close> the Isabelle settings environment
  (\secref{sec:settings}).

  After such a JVM cold-start, the Isabelle environment can be accessed via
  \<^verbatim>\<open>Isabelle_System.getenv\<close> as usual, but the underlying process environment
  remains clean. This is e.g.\ relevant when invoking other processes that
  should remain separate from the current Isabelle installation.

  \<^medskip>
  Note that under normal circumstances, Isabelle command-line tools are run
  \<^emph>\<open>within\<close> the settings environment, as provided by the @{executable
  isabelle} wrapper (\secref{sec:isabelle-tool} and \secref{sec:tool-java}).
\<close>


subsubsection \<open>Example\<close>

text \<open>
  The subsequent example creates a raw Java process on the command-line and
  invokes the main Isabelle application entry point:
  @{verbatim [display] \<open>isabelle_java isabelle.Main\<close>}
\<close>


section \<open>YXML versus XML \label{sec:yxml-vs-xml}\<close>

text \<open>
  Isabelle tools often use YXML, which is a simple and efficient syntax for
  untyped XML trees. The YXML format is defined as follows.

    \<^enum> The encoding is always UTF-8.

    \<^enum> Body text is represented verbatim (no escaping, no special treatment of
    white space, no named entities, no CDATA chunks, no comments).

    \<^enum> Markup elements are represented via ASCII control characters \<open>\<^bold>X = 5\<close>
    and \<open>\<^bold>Y = 6\<close> as follows:

    \begin{tabular}{ll}
      XML & YXML \\\hline
      \<^verbatim>\<open><\<close>\<open>name attribute\<close>\<^verbatim>\<open>=\<close>\<open>value \<dots>\<close>\<^verbatim>\<open>>\<close> &
      \<open>\<^bold>X\<^bold>Yname\<^bold>Yattribute\<close>\<^verbatim>\<open>=\<close>\<open>value\<dots>\<^bold>X\<close> \\
      \<^verbatim>\<open></\<close>\<open>name\<close>\<^verbatim>\<open>>\<close> & \<open>\<^bold>X\<^bold>Y\<^bold>X\<close> \\
    \end{tabular}

    There is no special case for empty body text, i.e.\ \<^verbatim>\<open><foo/>\<close> is treated
    like \<^verbatim>\<open><foo></foo>\<close>. Also note that \<open>\<^bold>X\<close> and \<open>\<^bold>Y\<close> may never occur in
    well-formed XML documents.

  Parsing YXML is pretty straight-forward: split the text into chunks
  separated by \<open>\<^bold>X\<close>, then split each chunk into sub-chunks separated by \<open>\<^bold>Y\<close>.
  Markup chunks start with an empty sub-chunk, and a second empty sub-chunk
  indicates close of an element. Any other non-empty chunk consists of plain
  text. For example, see \<^file>\<open>~~/src/Pure/PIDE/yxml.ML\<close> or
  \<^file>\<open>~~/src/Pure/PIDE/yxml.scala\<close>.

  YXML documents may be detected quickly by checking that the first two
  characters are \<open>\<^bold>X\<^bold>Y\<close>.
\<close>

end
