(*:maxLineLen=78:*)

theory Scala
imports Base
begin

chapter \<open>Isabelle/Scala development tools\<close>

text \<open>
  Isabelle/ML and Isabelle/Scala are the two main language environments for
  Isabelle tool implementations. There are some basic command-line tools to
  work with the underlying Java Virtual Machine, the Scala toplevel and
  compiler. Note that Isabelle/jEdit @{cite "isabelle-jedit"} provides a Scala
  Console for interactive experimentation within the running application.
\<close>


section \<open>Java Runtime Environment within Isabelle \label{sec:tool-java}\<close>

text \<open>
  The @{tool_def java} tool is a direct wrapper for the Java Runtime
  Environment, within the regular Isabelle settings environment
  (\secref{sec:settings}). The command line arguments are that of the
  underlying Java version. It is run in \<^verbatim>\<open>-server\<close> mode if possible, to
  improve performance (at the cost of extra startup time).

  The \<^verbatim>\<open>java\<close> executable is the one within @{setting ISABELLE_JDK_HOME},
  according to the standard directory layout for official JDK distributions.
  The class loader is augmented such that the name space of
  \<^verbatim>\<open>Isabelle/Pure.jar\<close> is available, which is the main Isabelle/Scala module.
\<close>


section \<open>Scala toplevel \label{sec:tool-scala}\<close>

text \<open>
  The @{tool_def scala} tool is a direct wrapper for the Scala toplevel; see
  also @{tool java} above. The command line arguments are that of the
  underlying Scala version. This allows to interact with Isabelle/Scala in TTY
  mode. An alternative is to use the \<^verbatim>\<open>Console/Scala\<close> plugin of Isabelle/jEdit
  @{cite "isabelle-jedit"}.
\<close>

subsubsection \<open>Example\<close>

text \<open>
  Explore the Isabelle system environment in Scala:
  @{scala [display]
\<open>import isabelle._

val isabelle_home = Isabelle_System.getenv("ISABELLE_HOME")

val options = Options.init()
options.bool("browser_info")
options.string("document")\<close>}
\<close>


section \<open>Scala compiler \label{sec:tool-scalac}\<close>

text \<open>
  The @{tool_def scalac} tool is a direct wrapper for the Scala compiler; see
  also @{tool scala} above. The command line arguments are that of the
  underlying Scala version.

  This allows to compile further Scala modules, depending on existing
  Isabelle/Scala functionality. The resulting class or jar files can be added
  to the Java classpath using the \<^verbatim>\<open>classpath\<close> Bash function that is provided
  by the Isabelle process environment. Thus add-on components can register
  themselves in a modular manner, see also \secref{sec:components}.

  Note that jEdit @{cite "isabelle-jedit"} has its own mechanisms for adding
  plugin components, which needs special attention since it overrides the
  standard Java class loader.
\<close>


section \<open>Scala script wrapper\<close>

text \<open>
  The executable @{executable "$ISABELLE_HOME/bin/isabelle_scala_script"}
  allows to run Isabelle/Scala source files stand-alone programs, by using a
  suitable ``hash-bang'' line and executable file permissions. For example:
  @{verbatim [display]
\<open>#!/usr/bin/env isabelle_scala_script

val options = isabelle.Options.init()
Console.println("browser_info = " + options.bool("browser_info"))
Console.println("document = " + options.string("document"))\<close>}

  This assumes that the executable may be found via the @{setting PATH} from
  the process environment: this is the case when Isabelle settings are active,
  e.g.\ in the context of the main Isabelle tool wrapper
  \secref{sec:isabelle-tool}. Alternatively, the full
  \<^file>\<open>$ISABELLE_HOME/bin/isabelle_scala_script\<close> may be specified in expanded
  form.
\<close>


section \<open>Project setup for common Scala IDEs\<close>

text \<open>
  The @{tool_def scala_project} tool creates a project configuration for
  Isabelle/Scala/jEdit:
  @{verbatim [display]
\<open>Usage: isabelle scala_project [OPTIONS] PROJECT_DIR

  Options are:
    -L           make symlinks to original scala files

  Setup Gradle project for Isabelle/Scala/jEdit --- to support Scala IDEs
  such as IntelliJ IDEA.\<close>}

  The generated configuration is for Gradle\<^footnote>\<open>\<^url>\<open>https://gradle.org\<close>\<close>, but the
  main purpose is to import it into common Scala IDEs, such as IntelliJ
  IDEA\<^footnote>\<open>\<^url>\<open>https://www.jetbrains.com/idea\<close>\<close>. This allows to explore the
  sources with static analysis and other hints in real-time.

  The specified project directory must not exist yet. The generated files
  refer to physical file-system locations, using the path notation of the
  underlying OS platform. Thus the project needs to be recreated whenever the
  Isabelle installation is changed or moved.

  \<^medskip> By default, Scala sources are \<^emph>\<open>copied\<close> from the Isabelle distribution and
  editing them within the IDE has no permanent effect.

  Option \<^verbatim>\<open>-L\<close> produces \<^emph>\<open>symlinks\<close> to the original files: this allows to
  develop Isabelle/Scala/jEdit within an external Scala IDE. Note that
  building the result always requires \<^verbatim>\<open>isabelle jedit -b\<close> on the
  command-line.
\<close>

end
