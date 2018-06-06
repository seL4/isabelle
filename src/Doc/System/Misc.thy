(*:maxLineLen=78:*)

theory Misc
imports Base
begin

chapter \<open>Miscellaneous tools \label{ch:tools}\<close>

text \<open>
  Subsequently we describe various Isabelle related utilities, given in
  alphabetical order.
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

  ISABELLE_COMPONENT_REPOSITORY="https://isabelle.in.tum.de/components"\<close>}

  Components are initialized as described in \secref{sec:components} in a
  permissive manner, which can mark components as ``missing''. This state is
  amended by letting @{tool "components"} download and unpack components that
  are published on the default component repository
  \<^url>\<open>https://isabelle.in.tum.de/components\<close> in particular.

  Option \<^verbatim>\<open>-R\<close> specifies an alternative component repository. Note that
  \<^verbatim>\<open>file:///\<close> URLs can be used for local directories.

  Option \<^verbatim>\<open>-a\<close> selects all missing components to be resolved. Explicit
  components may be named as command line-arguments as well. Note that
  components are uniquely identified by their base name, while the
  installation takes place in the location that was specified in the attempt
  to initialize the component before.

  Option \<^verbatim>\<open>-l\<close> lists the current state of available and missing components
  with their location (full name) within the file-system.

  Option \<^verbatim>\<open>-I\<close> initializes the user settings file to subscribe to the standard
  components specified in the Isabelle repository clone --- this does not make
  any sense for regular Isabelle releases. If the file already exists, it
  needs to be edited manually according to the printed explanation.
\<close>


section \<open>Displaying documents \label{sec:tool-display}\<close>

text \<open>
  The @{tool_def display} tool displays documents in DVI or PDF format:
  @{verbatim [display]
\<open>Usage: isabelle display DOCUMENT

  Display DOCUMENT (in DVI or PDF format).\<close>}

  \<^medskip>
  The settings @{setting DVI_VIEWER} and @{setting PDF_VIEWER} determine the
  programs for viewing the corresponding file formats. Normally this opens the
  document via the desktop environment, potentially in an asynchronous manner
  with re-use of previews views.
\<close>


section \<open>Viewing documentation \label{sec:tool-doc}\<close>

text \<open>
  The @{tool_def doc} tool displays Isabelle documentation:
  @{verbatim [display]
\<open>Usage: isabelle doc [DOC ...]

  View Isabelle documentation.\<close>}

  If called without arguments, it lists all available documents. Each line
  starts with an identifier, followed by a short description. Any of these
  identifiers may be specified as arguments, in order to display the
  corresponding document (see also \secref{sec:tool-display}).

  \<^medskip>
  The @{setting ISABELLE_DOCS} setting specifies the list of directories
  (separated by colons) to be scanned for documentations.
\<close>


section \<open>Shell commands within the settings environment \label{sec:tool-env}\<close>

text \<open>
  The @{tool_def env} tool is a direct wrapper for the standard
  \<^verbatim>\<open>/usr/bin/env\<close> command on POSIX systems, running within the Isabelle
  settings environment (\secref{sec:settings}).

  The command-line arguments are that of the underlying version of \<^verbatim>\<open>env\<close>. For
  example, the following invokes an instance of the GNU Bash shell within the
  Isabelle environment:
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

  With the \<^verbatim>\<open>-a\<close> option, one may inspect the full process environment that
  Isabelle related programs are run in. This usually contains much more
  variables than are actually Isabelle settings. Normally, output is a list of
  lines of the form \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close>. The \<^verbatim>\<open>-b\<close> option causes only the values
  to be printed.

  Option \<^verbatim>\<open>-d\<close> produces a dump of the complete environment to the specified
  file. Entries are terminated by the ASCII null character, i.e.\ the C string
  terminator.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Get the location of @{setting ISABELLE_HOME_USER} where user-specific
  information is stored:
  @{verbatim [display] \<open>isabelle getenv ISABELLE_HOME_USER\<close>}

  \<^medskip>
  Get the value only of the same settings variable, which is particularly
  useful in shell scripts:
  @{verbatim [display] \<open>isabelle getenv -b ISABELLE_HOME_USER\<close>}
\<close>


section \<open>Installing standalone Isabelle executables \label{sec:tool-install}\<close>

text \<open>
  By default, the main Isabelle binaries (@{executable "isabelle"} etc.) are
  just run from their location within the distribution directory, probably
  indirectly by the shell through its @{setting PATH}. Other schemes of
  installation are supported by the @{tool_def install} tool:
  @{verbatim [display]
\<open>Usage: isabelle install [OPTIONS] BINDIR

  Options are:
    -d DISTDIR   refer to DISTDIR as Isabelle distribution
                 (default ISABELLE_HOME)

  Install Isabelle executables with absolute references to the
  distribution directory.\<close>}

  The \<^verbatim>\<open>-d\<close> option overrides the current Isabelle distribution directory as
  determined by @{setting ISABELLE_HOME}.

  The \<open>BINDIR\<close> argument tells where executable wrapper scripts for
  @{executable "isabelle"} and @{executable isabelle_scala_script} should be
  placed, which is typically a directory in the shell's @{setting PATH}, such
  as \<^verbatim>\<open>$HOME/bin\<close>.

  \<^medskip>
  It is also possible to make symbolic links of the main Isabelle executables
  manually, but making separate copies outside the Isabelle distribution
  directory will not work!
\<close>


section \<open>Creating instances of the Isabelle logo\<close>

text \<open>
  The @{tool_def logo} tool creates instances of the generic Isabelle logo as
  EPS and PDF, for inclusion in {\LaTeX} documents.
  @{verbatim [display]
\<open>Usage: isabelle logo [OPTIONS] XYZ

  Create instance XYZ of the Isabelle logo (as EPS and PDF).

  Options are:
    -n NAME      alternative output base name (default "isabelle_xyx")
    -q           quiet mode\<close>}

  Option \<^verbatim>\<open>-n\<close> specifies an alternative (base) name for the generated files.
  The default is \<^verbatim>\<open>isabelle_\<close>\<open>xyz\<close> in lower-case.

  Option \<^verbatim>\<open>-q\<close> omits printing of the result file name.

  \<^medskip>
  Implementors of Isabelle tools and applications are encouraged to make
  derived Isabelle logos for their own projects using this template.
\<close>


section \<open>Output the version identifier of the Isabelle distribution\<close>

text \<open>
  The @{tool_def version} tool displays Isabelle version information:
  @{verbatim [display]
\<open>Usage: isabelle version [OPTIONS]

  Options are:
    -i           short identification (derived from Mercurial id)

  Display Isabelle version information.\<close>}

  \<^medskip>
  The default is to output the full version string of the Isabelle
  distribution, e.g.\ ``\<^verbatim>\<open>Isabelle2018: August 2018\<close>.

  The \<^verbatim>\<open>-i\<close> option produces a short identification derived from the Mercurial
  id of the @{setting ISABELLE_HOME} directory.
\<close>

end
