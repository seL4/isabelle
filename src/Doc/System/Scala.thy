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

  The main Isabelle/Scala/jEdit functionality is provided by
  \<^file>\<open>$ISABELLE_HOME/lib/classes/isabelle.jar\<close>. Further underlying Scala and
  Java libraries are bundled with Isabelle, e.g.\ to access SQLite or
  PostgreSQL via JDBC.

  Add-on Isabelle components may augment the system environment by providing
  suitable configuration in \<^path>\<open>etc/settings\<close> (GNU bash script). The
  shell function \<^bash_function>\<open>classpath\<close> helps to write
  \<^path>\<open>etc/settings\<close> in a portable manner: it refers to library \<^verbatim>\<open>jar\<close>
  files in standard POSIX path notation. On Windows, this is converted to
  native platform format, before invoking Java (\secref{sec:scala-tools}).

  \<^medskip>
  There is also an implicit build process for Isabelle/Scala/Java modules,
  based on \<^path>\<open>etc/build.props\<close> within the component directory (see also
  \secref{sec:scala-build}).
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


subsection \<open>Scala compiler \label{sec:tool-scalac}\<close>

text \<open>
  The @{tool_def scalac} tool is a direct wrapper for the Scala compiler; see
  also @{tool scala} above. The command line arguments are that of the
  bundled Scala distribution.

  This provides a low-level mechanism to compile further Scala modules,
  depending on existing Isabelle/Scala functionality; the resulting \<^verbatim>\<open>class\<close>
  or \<^verbatim>\<open>jar\<close> files can be added to the Java classpath using the shell function
  \<^bash_function>\<open>classpath\<close>.

  A more convenient high-level approach works via \<^path>\<open>etc/build.props\<close>
  (see \secref{sec:scala-build}).
\<close>


section \<open>Isabelle/Scala/Java modules \label{sec:scala-build}\<close>

subsection \<open>Component configuration via \<^path>\<open>etc/build.props\<close>\<close>

text \<open>
  Isabelle components may augment the Isabelle/Scala/Java environment
  declaratively via properties given in \<^path>\<open>etc/build.props\<close> (within the
  component directory). This specifies an output \<^verbatim>\<open>jar\<close> \<^emph>\<open>module\<close>, based on
  Scala or Java \<^emph>\<open>sources\<close>, and arbitrary \<^emph>\<open>resources\<close>. Moreover, a module can
  specify \<^emph>\<open>services\<close> that are subclasses of
  \<^scala_type>\<open>isabelle.Isabelle_System.Service\<close>; these have a particular
  meaning to Isabelle/Scala tools.

  Before running a Scala or Java process, the Isabelle system implicitly
  ensures that all provided modules are compiled and packaged (as jars). It is
  also possible to invoke @{tool scala_build} explicitly, with extra options.

  \<^medskip>
  The syntax of in \<^path>\<open>etc/build.props\<close> follows a regular Java properties
  file\<^footnote>\<open>\<^url>\<open>https://docs.oracle.com/en/java/javase/15/docs/api/java.base/java/util/Properties.html#load(java.io.Reader)\<close>\<close>,
  but the encoding is \<^verbatim>\<open>UTF-8\<close>, instead of historic \<^verbatim>\<open>ISO 8859-1\<close> from the API
  documentation.

  The subsequent properties are relevant for the Scala/Java build process.
  Most properties are optional: the default is an empty string (or list). File
  names are relative to the main component directory and may refer to Isabelle
  settings variables (e.g. \<^verbatim>\<open>$ISABELLE_HOME\<close>).

    \<^item> \<^verbatim>\<open>title\<close> (required) is a human-readable description of the module, used
    in printed messages.

    \<^item> \<^verbatim>\<open>module\<close> specifies a \<^verbatim>\<open>jar\<close> file name for the output module, as result
    of the specified sources (and resources). If this is absent (or
    \<^verbatim>\<open>no_build\<close> is set, as described below), there is no implicit build
    process. The contributing sources might be given nonetheless, notably for
    @{tool scala_project} (\secref{sec:tool-scala-project}), which includes
    Scala/Java sources of components, while suppressing \<^verbatim>\<open>jar\<close> modules (to
    avoid duplication of program content).

    \<^item> \<^verbatim>\<open>no_build\<close> is a Boolean property, with default \<^verbatim>\<open>false\<close>. If set to
    \<^verbatim>\<open>true\<close>, the implicit build process for the given \<^verbatim>\<open>module\<close> is \<^emph>\<open>omitted\<close>
    --- it is assumed to be provided by other means.

    \<^item> \<^verbatim>\<open>scalac_options\<close> and \<^verbatim>\<open>javac_options\<close> augment the default settings
    @{setting_ref ISABELLE_SCALAC_OPTIONS} and @{setting_ref
    ISABELLE_JAVAC_OPTIONS} for this component; option syntax follows the
    regular command-line tools \<^verbatim>\<open>scalac\<close> and \<^verbatim>\<open>javac\<close>, respectively.

    \<^item> \<^verbatim>\<open>main\<close> specifies the main entry point for the \<^verbatim>\<open>jar\<close> module. This is
    only relevant for direct invocation like ``\<^verbatim>\<open>java -jar test.jar\<close>''.

    \<^item> \<^verbatim>\<open>requirements\<close> is a list of \<^verbatim>\<open>jar\<close> modules that are needed in the
    compilation process, but not provided by the regular classpath (notably
    @{setting ISABELLE_CLASSPATH}).

    A \<^emph>\<open>normal entry\<close> refers to a single \<^verbatim>\<open>jar\<close> file name, possibly with
    settings variables as usual. E.g. \<^file>\<open>$ISABELLE_SCALA_JAR\<close> for the main
    \<^file>\<open>$ISABELLE_HOME/lib/classes/isabelle.jar\<close> (especially relevant for
    add-on modules).

    A \<^emph>\<open>special entry\<close> is of of the form \<^verbatim>\<open>env:\<close>\<open>variable\<close> and refers to a
    settings variable from the Isabelle environment: its value may consist of
    multiple \<^verbatim>\<open>jar\<close> entries (separated by colons). Environment variables are
    not expanded recursively.

    \<^item> \<^verbatim>\<open>resources\<close> is a list of files that should be included in the resulting
    \<^verbatim>\<open>jar\<close> file. Each item consists of a pair separated by colon:
    \<open>source\<close>\<^verbatim>\<open>:\<close>\<open>target\<close> means to copy an existing source file (relative to
    the component directory) to the given target file or directory (relative
    to the \<^verbatim>\<open>jar\<close> name space). A \<open>file\<close> specification without colon
    abbreviates \<open>file\<close>\<^verbatim>\<open>:\<close>\<open>file\<close>, i.e. the file is copied while retaining its
    relative path name.

    \<^item> \<^verbatim>\<open>sources\<close> is a list of \<^verbatim>\<open>.scala\<close> or \<^verbatim>\<open>.java\<close> files that contribute to
    the specified module. It is possible to use both languages simultaneously:
    the Scala and Java compiler will be invoked consecutively to make this
    work.

    \<^item> \<^verbatim>\<open>services\<close> is a list of class names to be registered as Isabelle
    service providers (subclasses of
    \<^scala_type>\<open>isabelle.Isabelle_System.Service\<close>). Internal class names of
    the underlying JVM need to be given: e.g. see method @{scala_method (in
    java.lang.Object) getClass}.

    Particular services require particular subclasses: instances are filtered
    according to their dynamic type. For example, class
    \<^scala_type>\<open>isabelle.Isabelle_Scala_Tools\<close> collects Scala command-line
    tools, and class \<^scala_type>\<open>isabelle.Scala.Functions\<close> collects Scala
    functions (\secref{sec:scala-functions}).
\<close>


subsection \<open>Explicit Isabelle/Scala/Java build \label{sec:tool-scala-build}\<close>

text \<open>
  The @{tool_def scala_build} tool explicitly invokes the build process for
  all registered components.
  @{verbatim [display]
\<open>Usage: isabelle scala_build [OPTIONS]

  Options are:
    -f           force fresh build
    -q           quiet mode: suppress stdout/stderr

  Build Isabelle/Scala/Java modules of all registered components
  (if required).
\<close>}

  For each registered Isabelle component that provides
  \<^path>\<open>etc/build.props\<close>, the specified output \<^verbatim>\<open>module\<close> is checked against
  the corresponding input \<^verbatim>\<open>requirements\<close>, \<^verbatim>\<open>resources\<close>, \<^verbatim>\<open>sources\<close>. If
  required, there is an automatic build using \<^verbatim>\<open>scalac\<close> or \<^verbatim>\<open>javac\<close> (or both).
  The identity of input files is recorded within the output \<^verbatim>\<open>jar\<close>, using SHA1
  digests in \<^verbatim>\<open>META-INF/isabelle/shasum\<close>.

  \<^medskip>
  Option \<^verbatim>\<open>-f\<close> forces a fresh build, regardless of the up-to-date status of
  input files vs. the output module.

  \<^medskip>
  Option \<^verbatim>\<open>-q\<close> suppresses all output on stdout/stderr produced by the Scala or
  Java compiler.

  \<^medskip> Explicit invocation of \<^verbatim>\<open>isabelle scala_build\<close> mainly serves testing or
  applications with special options: the Isabelle system normally does an
  automatic the build on demand.
\<close>


subsection \<open>Project setup for common Scala IDEs \label{sec:tool-scala-project}\<close>

text \<open>
  The @{tool_def scala_project} tool creates a project configuration for all
  Isabelle/Scala/Java modules specified in components via
  \<^path>\<open>etc/build.props\<close>, together with additional source files given on
  the command-line:

  @{verbatim [display]
\<open>Usage: isabelle scala_project [OPTIONS] [MORE_SOURCES ...]

  Options are:
    -D DIR       project directory (default: "$ISABELLE_HOME_USER/scala_project")
    -L           make symlinks to original source files
    -f           force update of existing directory

  Setup Gradle project for Isabelle/Scala/jEdit --- to support Scala IDEs
  such as IntelliJ IDEA.\<close>}

  The generated configuration is for Gradle\<^footnote>\<open>\<^url>\<open>https://gradle.org\<close>\<close>, but the
  main purpose is to import it into common Scala IDEs, such as IntelliJ
  IDEA\<^footnote>\<open>\<^url>\<open>https://www.jetbrains.com/idea\<close>\<close>. This allows to explore the
  sources with static analysis and other hints in real-time.

  The generated files refer to physical file-system locations, using the path
  notation of the underlying OS platform. Thus the project needs to be
  recreated whenever the Isabelle installation is changed or moved.

  \<^medskip>
  Option \<^verbatim>\<open>-L\<close> produces \<^emph>\<open>symlinks\<close> to the original files: this allows to
  develop Isabelle/Scala/jEdit modules within an external IDE. Note that the
  result cannot be built within the IDE: it requires implicit or explicit
  \<^verbatim>\<open>isabelle scala_build\<close> (\secref{sec:tool-scala-build}) instead.

  The default is to \<^emph>\<open>copy\<close> source files, so editing them within the IDE has
  no permanent effect on the originals.

  \<^medskip>
  Option \<^verbatim>\<open>-D\<close> specifies an explicit project directory, instead of the default
  \<^path>\<open>$ISABELLE_HOME_USER/scala_project\<close>. Option \<^verbatim>\<open>-f\<close> forces an existing
  project directory to be \<^emph>\<open>purged\<close> --- after some sanity checks that it has
  been generated by @{tool "scala_project"} before.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Create a project directory and for editing the original sources:

  @{verbatim [display] \<open>isabelle scala_project -f -L\<close>}

  On Windows, this usually requires Administrator rights, in order to create
  native symlinks.
\<close>


section \<open>Registered Isabelle/Scala functions \label{sec:scala-functions}\<close>

subsection \<open>Defining functions in Isabelle/Scala\<close>

text \<open>
  A Scala functions of type \<^scala_type>\<open>String => String\<close> may be wrapped as
  \<^scala_type>\<open>isabelle.Scala.Fun\<close> and collected via an instance of the
  class \<^scala_type>\<open>isabelle.Scala.Functions\<close>. A system component can then
  register that class via \<^verbatim>\<open>services\<close> in \<^path>\<open>etc/build.props\<close>
  (\secref{sec:scala-build}). An example is the predefined collection of
  \<^scala_type>\<open>isabelle.Scala.Functions\<close> in \<^file>\<open>$ISABELLE_HOME/etc/build.props\<close>.

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
