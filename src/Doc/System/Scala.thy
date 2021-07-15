(*:maxLineLen=78:*)

theory Scala
imports Base
begin

chapter \<open>Isabelle/Scala systems programming \label{sec:scala}\<close>

text \<open>
  Isabelle/ML and Isabelle/Scala are the two main implementation languages of
  the Isabelle environment:

    \<^item> Isabelle/ML is for \<^emph>\<open>mathematics\<close>, to develop tools within the context
    of symbolic logic, e.g.\ for constructing proofs or defining
    domain-specific formal languages. See the \<^emph>\<open>Isabelle/Isar implementation
    manual\<close> @{cite "isabelle-implementation"} for more details.

    \<^item> Isabelle/Scala is for \<^emph>\<open>physics\<close>, to connect with the world of systems
    and services, including editors and IDE frameworks.

  There are various ways to access Isabelle/Scala modules and operations:

    \<^item> Isabelle command-line tools (\secref{sec:scala-tools}) run in a separate
    Java process.

    \<^item> Isabelle/ML antiquotations access Isabelle/Scala functions
    (\secref{sec:scala-functions}) via the PIDE protocol: execution happens
    within the running Java process underlying Isabelle/Scala.

    \<^item> The \<^verbatim>\<open>Console/Scala\<close> plugin of Isabelle/jEdit @{cite "isabelle-jedit"}
    operates on the running Java application, using the Scala
    read-eval-print-loop (REPL).

  The main Isabelle/Scala functionality is provided by \<^verbatim>\<open>isabelle.jar\<close>, but
  further add-ons are bundled with Isabelle, e.g.\ to access SQLite or
  PostgreSQL using JDBC (Java Database Connectivity).

  Other components may augment the system environment by providing a suitable
  \<^path>\<open>etc/settings\<close> shell script in the component directory. Some shell
  functions are available to help with that:

    \<^item> Function \<^bash_function>\<open>classpath\<close> adds \<^verbatim>\<open>jar\<close> files in Isabelle path
    notation (POSIX). On Windows, this is converted to native path names
    before invoking @{tool java} or @{tool scala} (\secref{sec:scala-tools}).

    \<^item> Function \<^bash_function>\<open>isabelle_scala_service\<close> registers global
    service providers as subclasses of
    \<^scala_type>\<open>isabelle.Isabelle_System.Service\<close>, using the raw Java name
    according to @{scala_method (in java.lang.Object) getClass} (it should be
    enclosed in single quotes to avoid special characters like \<^verbatim>\<open>$\<close> to be
    interpreted by the shell).

    Particular Isabelle/Scala services require particular subclasses:
    instances are filtered according to their dynamic type. For example, class
    \<^scala_type>\<open>isabelle.Isabelle_Scala_Tools\<close> collects Scala command-line
    tools, and class \<^scala_type>\<open>isabelle.Scala.Functions\<close>
    collects Scala functions (\secref{sec:scala-functions}).
\<close>


section \<open>Command-line tools \label{sec:scala-tools}\<close>

subsection \<open>Java Runtime Environment \label{sec:tool-java}\<close>

text \<open>
  The @{tool_def java} tool is a direct wrapper for the Java Runtime
  Environment, within the regular Isabelle settings environment
  (\secref{sec:settings}) and Isabelle classpath. The command line arguments
  are that of the bundled Java distribution: see option \<^verbatim>\<open>-help\<close> in
  particular.

  The \<^verbatim>\<open>java\<close> executable is taken from @{setting ISABELLE_JDK_HOME}, according
  to the standard directory layout for regular distributions of OpenJDK.

  The shell function \<^bash_function>\<open>isabelle_jdk\<close> allows shell scripts to
  invoke other Java tools robustly (e.g.\ \<^verbatim>\<open>isabelle_jdk jar\<close>), without
  depending on accidental operating system installations.
\<close>


subsection \<open>Scala toplevel \label{sec:tool-scala}\<close>

text \<open>
  The @{tool_def scala} tool is a direct wrapper for the Scala toplevel,
  similar to @{tool java} above. The command line arguments are that of the
  bundled Scala distribution: see option \<^verbatim>\<open>-help\<close> in particular. This allows
  to interact with Isabelle/Scala interactively.
\<close>

subsubsection \<open>Example\<close>

text \<open>
  Explore the Isabelle system environment in Scala:
  @{verbatim [display, indent = 2] \<open>$ isabelle scala\<close>}
  @{scala [display, indent = 2]
\<open>import isabelle._

val isabelle_home = Isabelle_System.getenv("ISABELLE_HOME")

val options = Options.init()
options.bool("browser_info")
options.string("document")\<close>}
\<close>


subsection \<open>Scala compiler \label{sec:tool-scalac}\<close>

text \<open>
  The @{tool_def scalac} tool is a direct wrapper for the Scala compiler; see
  also @{tool scala} above. The command line arguments are that of the
  bundled Scala distribution.

  This allows to compile further Scala modules, depending on existing
  Isabelle/Scala functionality. The resulting \<^verbatim>\<open>class\<close> or \<^verbatim>\<open>jar\<close> files can be
  added to the Java classpath using the shell function
  \<^bash_function>\<open>classpath\<close>. Thus add-on components can register themselves
  in a modular manner, see also \secref{sec:components}.

  Note that Isabelle/jEdit @{cite "isabelle-jedit"} has its own mechanisms for
  adding plugin components. This needs special attention, since it overrides
  the standard Java class loader.
\<close>


subsection \<open>Scala script wrapper\<close>

text \<open>
  The executable @{executable "$ISABELLE_HOME/bin/isabelle_scala_script"}
  allows to run Isabelle/Scala source files stand-alone programs, by using a
  suitable ``hash-bang'' line and executable file permissions. For example:
  @{verbatim [display, indent = 2] \<open>#!/usr/bin/env isabelle_scala_script\<close>}
  @{scala [display, indent = 2]
\<open>val options = isabelle.Options.init()
Console.println("browser_info = " + options.bool("browser_info"))
Console.println("document = " + options.string("document"))\<close>}

  This assumes that the executable may be found via the @{setting PATH} from
  the process environment: this is the case when Isabelle settings are active,
  e.g.\ in the context of the main Isabelle tool wrapper
  \secref{sec:isabelle-tool}. Alternatively, the full
  \<^file>\<open>$ISABELLE_HOME/bin/isabelle_scala_script\<close> may be specified in expanded
  form.
\<close>


subsection \<open>Project setup for common Scala IDEs\<close>

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

  The specified project directory needs to be fresh. The generated files refer
  to physical file-system locations, using the path notation of the underlying
  OS platform. Thus the project needs to be recreated whenever the Isabelle
  installation is changed or moved.

  \<^medskip>
  By default, Scala sources are \<^emph>\<open>copied\<close> from the Isabelle distribution and
  editing them within the IDE has no permanent effect.

  Option \<^verbatim>\<open>-L\<close> produces \<^emph>\<open>symlinks\<close> to the original files: this allows to
  develop Isabelle/Scala/jEdit within an external Scala IDE. Note that
  building the result always requires \<^verbatim>\<open>isabelle jedit -b\<close> on the
  command-line.
\<close>


section \<open>Registered Isabelle/Scala functions \label{sec:scala-functions}\<close>

subsection \<open>Defining functions in Isabelle/Scala\<close>

text \<open>
  A Scala functions of type \<^scala_type>\<open>String => String\<close> may be wrapped as
  \<^scala_type>\<open>isabelle.Scala.Fun\<close> and collected via an instance of the
  class \<^scala_type>\<open>isabelle.Scala.Functions\<close>. A system component
  can then register that class via \<^bash_function>\<open>isabelle_scala_service\<close>
  in \<^path>\<open>etc/settings\<close> (\secref{sec:components}). An example is the
  predefined collection of \<^scala_type>\<open>isabelle.Scala.Functions\<close> in
  \<^verbatim>\<open>isabelle.jar\<close> with the following line in
  \<^file>\<open>$ISABELLE_HOME/etc/settings\<close>:
  @{verbatim [display, indent = 2] \<open>isabelle_scala_service 'isabelle.Functions'\<close>}

  The overall list of registered functions is accessible in Isabelle/Scala as
  \<^scala_object>\<open>isabelle.Scala.functions\<close>.
\<close>


subsection \<open>Invoking functions in Isabelle/ML\<close>

text \<open>
  Isabelle/PIDE provides a protocol to invoke registered Scala functions in
  ML: this works both within the Prover IDE and in batch builds.

  The subsequent ML antiquotations refer to Scala functions in a
  formally-checked manner.

  \begin{matharray}{rcl}
  @{ML_antiquotation_def "scala_function"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "scala"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@{ML_antiquotation scala_function} |
     @{ML_antiquotation scala}) @{syntax embedded}
  \<close>

  \<^descr> \<open>@{scala_function name}\<close> inlines the checked function name as ML string
    literal.

  \<^descr> \<open>@{scala name}\<close> and \<open>@{scala_thread name}\<close> invoke the checked function via
  the PIDE protocol. In Isabelle/ML this appears as a function of type
  \<^ML_type>\<open>string -> string\<close>, which is subject to interrupts within the ML
  runtime environment as usual. A \<^scala>\<open>null\<close> result in Scala raises an
  exception \<^ML>\<open>Scala.Null\<close> in ML. The execution of \<open>@{scala}\<close> works via a
  Scala future on a bounded thread farm, while \<open>@{scala_thread}\<close> always forks
  a separate Java thread.

  The standard approach of representing datatypes via strings works via XML in
  YXML transfer syntax. See Isabelle/ML operations and modules @{ML
  YXML.string_of_body}, @{ML YXML.parse_body}, @{ML_structure XML.Encode},
  @{ML_structure XML.Decode}; similarly for Isabelle/Scala. Isabelle symbols
  may have to be recoded via Scala operations
  \<^scala_method>\<open>isabelle.Symbol.decode\<close> and
  \<^scala_method>\<open>isabelle.Symbol.encode\<close>.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Invoke the predefined Scala function \<^scala_function>\<open>echo\<close>:
\<close>

ML \<open>
  val s = "test";
  val s' = \<^scala>\<open>echo\<close> s;
  \<^assert> (s = s')
\<close>

text \<open>
  Let the Scala compiler process some toplevel declarations, producing a list
  of errors:
\<close>

ML \<open>
  val source = "class A(a: Int, b: Boolean)"
  val errors =
    \<^scala>\<open>scala_toplevel\<close> source
    |> YXML.parse_body
    |> let open XML.Decode in list string end;

  \<^assert> (null errors)\<close>

text \<open>
  The above is merely for demonstration. See \<^ML>\<open>Scala_Compiler.toplevel\<close>
  for a more convenient version with builtin decoding and treatment of errors.
\<close>


section \<open>Documenting Isabelle/Scala entities\<close>

text \<open>
  The subsequent document antiquotations help to document Isabelle/Scala
  entities, with formal checking of names against the Isabelle classpath.

  \begin{matharray}{rcl}
  @{antiquotation_def "scala"} & : & \<open>antiquotation\<close> \\
  @{antiquotation_def "scala_object"} & : & \<open>antiquotation\<close> \\
  @{antiquotation_def "scala_type"} & : & \<open>antiquotation\<close> \\
  @{antiquotation_def "scala_method"} & : & \<open>antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{antiquotation scala} | @@{antiquotation scala_object})
      @{syntax embedded}
    ;
    @@{antiquotation scala_type} @{syntax embedded} types
    ;
    @@{antiquotation scala_method} class @{syntax embedded} types args
    ;
    class: ('(' @'in' @{syntax name} types ')')?
    ;
    types: ('[' (@{syntax name} ',' +) ']')?
    ;
    args: ('(' (nat | (('_' | @{syntax name}) + ',')) ')')?
  \<close>

  \<^descr> \<open>@{scala s}\<close> is similar to \<open>@{verbatim s}\<close>, but the given source text is
  checked by the Scala compiler as toplevel declaration (without evaluation).
  This allows to write Isabelle/Scala examples that are statically checked.

  \<^descr> \<open>@{scala_object x}\<close> checks the given Scala object name (simple value or
  ground module) and prints the result verbatim.

  \<^descr> \<open>@{scala_type T[A]}\<close> checks the given Scala type name (with optional type
  parameters) and prints the result verbatim.

  \<^descr> \<open>@{scala_method (in c[A]) m[B](n)}\<close> checks the given Scala method \<open>m\<close> in
  the context of class \<open>c\<close>. The method argument slots are either specified by
  a number \<open>n\<close> or by a list of (optional) argument types; this may refer to
  type variables specified for the class or method: \<open>A\<close> or \<open>B\<close> above.

  Everything except for the method name \<open>m\<close> is optional. The absence of the
  class context means that this is a static method. The absence of arguments
  with types means that the method can be determined uniquely as \<^verbatim>\<open>(\<close>\<open>m\<close>\<^verbatim>\<open> _)\<close>
  in Scala (no overloading).
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Miscellaneous Isabelle/Scala entities:

    \<^item> object: \<^scala_object>\<open>isabelle.Isabelle_Process\<close>
    \<^item> type without parameter: @{scala_type isabelle.Console_Progress}
    \<^item> type with parameter: @{scala_type List[A]}
    \<^item> static method: \<^scala_method>\<open>isabelle.Isabelle_System.bash\<close>
    \<^item> class and method with type parameters:
      @{scala_method (in List[A]) map[B]("A => B")}
    \<^item> overloaded method with argument type: @{scala_method (in Int) "+" (Int)}
\<close>

end
