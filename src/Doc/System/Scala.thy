theory Scala
imports Base
begin

chapter {* Isabelle/Scala development tools *}

text {* Isabelle/ML and Isabelle/Scala are the two main language
environments for Isabelle tool implementations.  There are some basic
command-line tools to work with the underlying Java Virtual Machine,
the Scala toplevel and compiler.  Note that Isabelle/jEdit
\cite{isabelle-jedit} provides a Scala Console for interactive
experimentation within the running application. *}


section {* Java Runtime Environment within Isabelle \label{sec:tool-java} *}

text {* The @{tool_def java} tool is a direct wrapper for the Java
  Runtime Environment, within the regular Isabelle settings
  environment (\secref{sec:settings}).  The command line arguments are
  that of the underlying Java version.  It is run in @{verbatim
  "-server"} mode if possible, to improve performance (at the cost of
  extra startup time).

  The @{verbatim java} executable is the one within @{setting
  ISABELLE_JDK_HOME}, according to the standard directory layout for
  official JDK distributions.  The class loader is augmented such that
  the name space of @{verbatim "Isabelle/Pure.jar"} is available,
  which is the main Isabelle/Scala module.

  For example, the following command-line invokes the main method of
  class @{verbatim isabelle.GUI_Setup}, which opens a windows with
  some diagnostic information about the Isabelle environment:
\begin{alltt}
  isabelle java isabelle.GUI_Setup
\end{alltt}
*}


section {* Scala toplevel \label{sec:tool-scala} *}

text {* The @{tool_def scala} tool is a direct wrapper for the Scala
  toplevel; see also @{tool java} above.  The command line arguments
  are that of the underlying Scala version.

  This allows to interact with Isabelle/Scala in TTY mode like this:
\begin{alltt}
  isabelle scala
  scala> isabelle.Isabelle_System.getenv("ISABELLE_HOME")
  scala> val options = isabelle.Options.init()
  scala> options.bool("browser_info")
  scala> options.string("document")
\end{alltt}
*}


section {* Scala compiler \label{sec:tool-scalac} *}

text {* The @{tool_def scalac} tool is a direct wrapper for the Scala
  compiler; see also @{tool scala} above.  The command line arguments
  are that of the underlying Scala version.

  This allows to compile further Scala modules, depending on existing
  Isabelle/Scala functionality.  The resulting class or jar files can
  be added to the Java classpath using the @{verbatim classpath} Bash
  function that is provided by the Isabelle process environment.  Thus
  add-on components can register themselves in a modular manner, see
  also \secref{sec:components}.

  Note that jEdit \cite{isabelle-jedit} has its own mechanisms for
  adding plugin components, which needs special attention since
  it overrides the standard Java class loader.  *}


section {* Scala script wrapper *}

text {* The executable @{executable
  "$ISABELLE_HOME/bin/isabelle_scala_script"} allows to run
  Isabelle/Scala source files stand-alone programs, by using a
  suitable ``hash-bang'' line and executable file permissions.

  The subsequent example assumes that the main Isabelle binaries have
  been installed in some directory that is included in @{setting PATH}
  (see also @{tool "install"}):

\begin{alltt}
#!/usr/bin/env isabelle_scala_script

val options = isabelle.Options.init()
Console.println("browser_info = " + options.bool("browser_info"))
Console.println("document = " + options.string("document"))
\end{alltt}

  Alternatively the full @{file
  "$ISABELLE_HOME/bin/isabelle_scala_script"} may be specified in
  expanded form.  *}

end
