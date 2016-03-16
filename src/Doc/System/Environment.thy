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
    plain copy of the @{file "$ISABELLE_HOME/bin"} files will not work!

    \<^enum> The file @{file "$ISABELLE_HOME/etc/settings"} is run as a
    @{executable_ref bash} shell script with the auto-export option for
    variables enabled.

    This file holds a rather long list of shell variable assignments, thus
    providing the site-wide default settings. The Isabelle distribution
    already contains a global settings file with sensible defaults for most
    variables. When installing the system, only a few of these may have to be
    adapted (probably @{setting ML_SYSTEM} etc.).

    \<^enum> The file @{file_unchecked "$ISABELLE_HOME_USER/etc/settings"} (if it
    exists) is run in the same way as the site default settings. Note that the
    variable @{setting ISABELLE_HOME_USER} has already been set before ---
    usually to something like \<^verbatim>\<open>$USER_HOME/.isabelle/IsabelleXXXX\<close>.

    Thus individual users may override the site-wide defaults. Typically, a
    user settings file contains only a few lines, with some assignments that
    are actually changed. Never copy the central @{file
    "$ISABELLE_HOME/etc/settings"} file!

  Since settings files are regular GNU @{executable_def bash} scripts, one may
  use complex shell commands, such as \<^verbatim>\<open>if\<close> or \<^verbatim>\<open>case\<close> statements to set
  variables depending on the system architecture or other environment
  variables. Such advanced features should be added only with great care,
  though. In particular, external environment references should be kept at a
  minimum.

  \<^medskip>
  A few variables are somewhat special:

    \<^item> @{setting_def ISABELLE_TOOL} is set automatically to the absolute path
    name of the @{executable isabelle} executables.

    \<^item> @{setting_ref ISABELLE_OUTPUT} will have the identifiers of the Isabelle
    distribution (cf.\ @{setting ISABELLE_IDENTIFIER}) and the ML system (cf.\
    @{setting ML_IDENTIFIER}) appended automatically to its value.

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
  HOME should point to the @{file_unchecked "/home"} directory tree or the
  Windows user home.\<close>

  \<^descr>[@{setting_def ISABELLE_HOME}\<open>\<^sup>*\<close>] is the location of the top-level
  Isabelle distribution directory. This is automatically determined from the
  Isabelle executable that has been invoked. Do not attempt to set @{setting
  ISABELLE_HOME} yourself from the shell!

  \<^descr>[@{setting_def ISABELLE_HOME_USER}] is the user-specific counterpart of
  @{setting ISABELLE_HOME}. The default value is relative to @{file_unchecked
  "$USER_HOME/.isabelle"}, under rare circumstances this may be changed in the
  global setting file. Typically, the @{setting ISABELLE_HOME_USER} directory
  mimics @{setting ISABELLE_HOME} to some extend. In particular, site-wide
  defaults may be overridden by a private \<^verbatim>\<open>$ISABELLE_HOME_USER/etc/settings\<close>.

  \<^descr>[@{setting_def ISABELLE_PLATFORM_FAMILY}\<open>\<^sup>*\<close>] is automatically set to the
  general platform family: \<^verbatim>\<open>linux\<close>, \<^verbatim>\<open>macos\<close>, \<^verbatim>\<open>windows\<close>. Note that
  platform-dependent tools usually need to refer to the more specific
  identification according to @{setting ISABELLE_PLATFORM}, @{setting
  ISABELLE_PLATFORM32}, @{setting ISABELLE_PLATFORM64}.

  \<^descr>[@{setting_def ISABELLE_PLATFORM}\<open>\<^sup>*\<close>] is automatically set to a symbolic
  identifier for the underlying hardware and operating system. The Isabelle
  platform identification always refers to the 32 bit variant, even this is a
  64 bit machine. Note that the ML or Java runtime may have a different idea,
  depending on which binaries are actually run.

  \<^descr>[@{setting_def ISABELLE_PLATFORM64}\<open>\<^sup>*\<close>] is similar to @{setting
  ISABELLE_PLATFORM} but refers to the proper 64 bit variant on a platform
  that supports this; the value is empty for 32 bit. Note that the following
  bash expression (including the quotes) prefers the 64 bit platform, if that
  is available:

  @{verbatim [display] \<open>"${ISABELLE_PLATFORM64:-$ISABELLE_PLATFORM}"\<close>}

  \<^descr>[@{setting ISABELLE_TOOL}\<open>\<^sup>*\<close>] is automatically set to the full path name
  of the @{executable isabelle} executable. Thus other tools and scripts need
  not assume that the @{file "$ISABELLE_HOME/bin"} directory is on the current
  search path of the shell.

  \<^descr>[@{setting_def ISABELLE_IDENTIFIER}\<open>\<^sup>*\<close>] refers to the name of this
  Isabelle distribution, e.g.\ ``\<^verbatim>\<open>Isabelle2012\<close>''.

  \<^descr>[@{setting_def ML_SYSTEM}, @{setting_def ML_HOME}, @{setting_def
  ML_OPTIONS}, @{setting_def ML_PLATFORM}, @{setting_def ML_IDENTIFIER}\<open>\<^sup>*\<close>]
  specify the underlying ML system to be used for Isabelle. There is only a
  fixed set of admissable @{setting ML_SYSTEM} names (see the @{file
  "$ISABELLE_HOME/etc/settings"} file of the distribution).

  The actual compiler binary will be run from the directory @{setting
  ML_HOME}, with @{setting ML_OPTIONS} as first arguments on the command line.
  The optional @{setting ML_PLATFORM} may specify the binary format of ML heap
  images, which is useful for cross-platform installations. The value of
  @{setting ML_IDENTIFIER} is automatically obtained by composing the values
  of @{setting ML_SYSTEM}, @{setting ML_PLATFORM} and the Isabelle version
  values.

  \<^descr>[@{setting_def ISABELLE_JDK_HOME}] needs to point to a full JDK (Java
  Development Kit) installation with \<^verbatim>\<open>javac\<close> and \<^verbatim>\<open>jar\<close> executables. This is
  essential for Isabelle/Scala and other JVM-based tools to work properly.
  Note that conventional \<^verbatim>\<open>JAVA_HOME\<close> usually points to the JRE (Java Runtime
  Environment), not JDK.

  \<^descr>[@{setting_def ISABELLE_PATH}] is a list of directories (separated by
  colons) where Isabelle logic images may reside. When looking up heaps files,
  the value of @{setting ML_IDENTIFIER} is appended to each component
  internally.

  \<^descr>[@{setting_def ISABELLE_OUTPUT}\<open>\<^sup>*\<close>] is a directory where output heap files
  should be stored by default. The ML system and Isabelle version identifier
  is appended here, too.

  \<^descr>[@{setting_def ISABELLE_BROWSER_INFO}] is the directory where theory
  browser information is stored as HTML and PDF (see also \secref{sec:info}).
  The default value is @{file_unchecked "$ISABELLE_HOME_USER/browser_info"}.

  \<^descr>[@{setting_def ISABELLE_LOGIC}] specifies the default logic to load if none
  is given explicitely by the user. The default value is \<^verbatim>\<open>HOL\<close>.

  \<^descr>[@{setting_def ISABELLE_LINE_EDITOR}] specifies the line editor for the
  @{tool_ref console} interface.

  \<^descr>[@{setting_def ISABELLE_LATEX}, @{setting_def ISABELLE_PDFLATEX},
  @{setting_def ISABELLE_BIBTEX}] refer to {\LaTeX} related tools for Isabelle
  document preparation (see also \secref{sec:tool-latex}).

  \<^descr>[@{setting_def ISABELLE_TOOLS}] is a colon separated list of directories
  that are scanned by @{executable isabelle} for external utility programs
  (see also \secref{sec:isabelle-tool}).

  \<^descr>[@{setting_def ISABELLE_DOCS}] is a colon separated list of directories
  with documentation files.

  \<^descr>[@{setting_def PDF_VIEWER}] specifies the program to be used for displaying
  \<^verbatim>\<open>pdf\<close> files.

  \<^descr>[@{setting_def DVI_VIEWER}] specifies the program to be used for displaying
  \<^verbatim>\<open>dvi\<close> files.

  \<^descr>[@{setting_def ISABELLE_TMP_PREFIX}\<open>\<^sup>*\<close>] is the prefix from which any
  running Isabelle ML process derives an individual directory for temporary
  files.
\<close>


subsection \<open>Additional components \label{sec:components}\<close>

text \<open>
  Any directory may be registered as an explicit \<^emph>\<open>Isabelle component\<close>. The
  general layout conventions are that of the main Isabelle distribution
  itself, and the following two files (both optional) have a special meaning:

    \<^item> \<^verbatim>\<open>etc/settings\<close> holds additional settings that are initialized when
    bootstrapping the overall Isabelle environment, cf.\ \secref{sec:boot}. As
    usual, the content is interpreted as a \<^verbatim>\<open>bash\<close> script. It may refer to the
    component's enclosing directory via the \<^verbatim>\<open>COMPONENT\<close> shell variable.

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
  exists). This allows to install private components via @{file_unchecked
  "$ISABELLE_HOME_USER/etc/components"}, although it is often more convenient
  to do that programmatically via the \<^verbatim>\<open>init_component\<close> shell function in the
  \<^verbatim>\<open>etc/settings\<close> script of \<^verbatim>\<open>$ISABELLE_HOME_USER\<close> (or any other component
  directory). For example:
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
  Isabelle related utilities, user interfaces etc. Such tools automatically
  benefit from the settings mechanism. All Isabelle command-line tools are
  invoked via a common wrapper --- @{executable_ref isabelle}:
  @{verbatim [display]
\<open>Usage: isabelle TOOL [ARGS ...]

  Start Isabelle tool NAME with ARGS; pass "-?" for tool specific help.

Available tools:
  ...\<close>}

  In principle, Isabelle tools are ordinary executable scripts that are run
  within the Isabelle settings environment, see \secref{sec:settings}. The set
  of available tools is collected by @{executable isabelle} from the
  directories listed in the @{setting ISABELLE_TOOLS} setting. Do not try to
  call the scripts directly from the shell. Neither should you add the tool
  directories to your shell's search path!
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


subsubsection \<open>Example\<close>

text \<open>
  The subsequent example retrieves the \<^verbatim>\<open>Main\<close> theory value from the theory
  loader within ML:
  @{verbatim [display] \<open>isabelle process -e 'Thy_Info.get_theory "Main"'\<close>}

  Observe the delicate quoting rules for the Bash shell vs.\ ML. The
  Isabelle/ML and Scala libraries provide functions for that, but here we need
  to do it manually.
\<close>


subsection \<open>Interactive mode\<close>

text \<open>
  The @{tool_def console} tool runs the raw ML process with interactive
  console and line editor:
  @{verbatim [display]
\<open>Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           bootstrap from raw Poly/ML
    -s           system build mode for session image

  Build a logic session image and run the raw Isabelle ML process
  in interactive mode, with line editor ISABELLE_LINE_EDITOR.\<close>}

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> specifies the logic session name. By default, its heap image is
  checked and built on demand, but the option \<^verbatim>\<open>-n\<close> skips that.

  Option \<^verbatim>\<open>-r\<close> indicates a bootstrap from the raw Poly/ML system, which is
  relevant for Isabelle/Pure development.

  \<^medskip>
  Options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-m\<close>, \<^verbatim>\<open>-o\<close> have the same meaning as for @{tool process}
  (\secref{sec:tool-process}).

  Option \<^verbatim>\<open>-s\<close> has the same meaning as for @{tool build}
  (\secref{sec:tool-build}).

  \<^medskip>
  The Isabelle/ML process is run through the line editor that is specified via
  the settings variable @{setting ISABELLE_LINE_EDITOR} (e.g.\
  @{executable_def rlwrap} for GNU readline); the fall-back is to use plain
  standard input/output.

  The user is connected to the raw ML toplevel loop: this is neither
  Isabelle/Isar nor Isabelle/ML within the usual formal context. The most
  relevant ML commands at this stage are @{ML use}, @{ML use_thy}, @{ML
  use_thys}.
\<close>


section \<open>YXML versus XML\<close>

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
  text. For example, see @{file "~~/src/Pure/PIDE/yxml.ML"} or @{file
  "~~/src/Pure/PIDE/yxml.scala"}.

  YXML documents may be detected quickly by checking that the first two
  characters are \<open>\<^bold>X\<^bold>Y\<close>.
\<close>

end