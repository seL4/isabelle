(*:maxLineLen=78:*)

theory JEdit
imports Base
begin

chapter \<open>Introduction\<close>

section \<open>Concepts and terminology\<close>

text \<open>
  Isabelle/jEdit is a Prover IDE that integrates \<^emph>\<open>parallel proof checking\<close>
  @{cite "Wenzel:2009" and "Wenzel:2013:ITP"} with \<^emph>\<open>asynchronous user
  interaction\<close> @{cite "Wenzel:2010" and "Wenzel:2012:UITP-EPTCS" and
  "Wenzel:2014:ITP-PIDE" and "Wenzel:2014:UITP"}, based on a document-oriented
  approach to \<^emph>\<open>continuous proof processing\<close> @{cite "Wenzel:2011:CICM" and
  "Wenzel:2012" and "Wenzel:2018:FIDE" and "Wenzel:2019:MKM"}. Many concepts
  and system components are fit together in order to make this work. The main
  building blocks are as follows.

    \<^descr>[Isabelle/ML] is the implementation and extension language of Isabelle,
    see also @{cite "isabelle-implementation"}. It is integrated into the
    logical context of Isabelle/Isar and allows to manipulate logical entities
    directly. Arbitrary add-on tools may be implemented for object-logics such
    as Isabelle/HOL.

    \<^descr>[Isabelle/Scala] is the system programming language of Isabelle. It
    extends the pure logical environment of Isabelle/ML towards the outer
    world of graphical user interfaces, text editors, IDE frameworks, web
    services, SSH servers, SQL databases etc. Special infrastructure allows to
    transfer algebraic datatypes and formatted text easily between ML and
    Scala, using asynchronous protocol commands.

    \<^descr>[PIDE] is a general framework for Prover IDEs based on Isabelle/Scala. It
    is built around a concept of parallel and asynchronous document
    processing, which is supported natively by the parallel proof engine that
    is implemented in Isabelle/ML. The traditional prover command loop is
    given up; instead there is direct support for editing of source text, with
    rich formal markup for GUI rendering.

    \<^descr>[jEdit] is a sophisticated text editor\<^footnote>\<open>\<^url>\<open>http://www.jedit.org\<close>\<close>
    implemented in Java\<^footnote>\<open>\<^url>\<open>https://adoptopenjdk.net\<close>\<close>. It is easily
    extensible by plugins written in any language that works on the JVM. In
    the context of Isabelle this is always
    Scala\<^footnote>\<open>\<^url>\<open>https://www.scala-lang.org\<close>\<close>.

    \<^descr>[Isabelle/jEdit] is the main application of the PIDE framework and the
    default user-interface for Isabelle. It targets both beginners and
    experts. Technically, Isabelle/jEdit consists of the original jEdit code
    base with minimal patches and a special plugin for Isabelle. This is
    integrated as a desktop application for the main operating system
    families: Linux, Windows, macOS.

  End-users of Isabelle download and run a standalone application that exposes
  jEdit as a text editor on the surface. Thus there is occasionally a tendency
  to apply the name ``jEdit'' to any of the Isabelle Prover IDE aspects,
  without proper differentiation. When discussing these PIDE building blocks
  in public forums, mailing lists, or even scientific publications, it is
  particularly important to distinguish Isabelle/ML versus Standard ML,
  Isabelle/Scala versus Scala, Isabelle/jEdit versus jEdit.
\<close>


section \<open>The Isabelle/jEdit Prover IDE\<close>

text \<open>
  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[width=\textwidth]{isabelle-jedit}
  \end{center}
  \caption{The Isabelle/jEdit Prover IDE}
  \label{fig:isabelle-jedit}
  \end{figure}

  Isabelle/jEdit (\figref{fig:isabelle-jedit}) consists of some plugins for
  the jEdit text editor, while preserving its general look-and-feel as far as
  possible. The main plugin is called ``Isabelle'' and has its own menu
  \<^emph>\<open>Plugins~/ Isabelle\<close> with access to several actions and add-on panels (see
  also \secref{sec:dockables}), as well as \<^emph>\<open>Plugins~/ Plugin Options~/
  Isabelle\<close> (see also \secref{sec:options}).

  The options allow to specify a logic session name, but the same selector is
  also accessible in the \<^emph>\<open>Theories\<close> panel (\secref{sec:theories}). After
  startup of the Isabelle plugin, the selected logic session image is provided
  automatically by the Isabelle build tool @{cite "isabelle-system"}: if it is
  absent or outdated wrt.\ its sources, the build process updates it within
  the running text editor. Prover IDE functionality is fully activated after
  successful termination of the build process. A failure may require changing
  some options and restart of the Isabelle plugin or application. Changing the
  logic session requires a restart of the whole application to take effect.

  \<^medskip> The main job of the Prover IDE is to manage sources and their changes,
  taking the logical structure as a formal document into account (see also
  \secref{sec:document-model}). The editor and the prover are connected
  asynchronously without locking. The prover is free to organize the checking
  of the formal text in parallel on multiple cores, and provides feedback via
  markup, which is rendered in the editor via colors, boxes, squiggly
  underlines, hyperlinks, popup windows, icons, clickable output etc.

  Using the mouse together with the modifier key \<^verbatim>\<open>CONTROL\<close> (Linux, Windows)
  or \<^verbatim>\<open>COMMAND\<close> (macOS) exposes formal content via tooltips and/or
  hyperlinks (see also \secref{sec:tooltips-hyperlinks}). Output (in popups
  etc.) may be explored recursively, using the same techniques as in the
  editor source buffer.

  Thus the Prover IDE gives an impression of direct access to formal content
  of the prover within the editor, but in reality only certain aspects are
  exposed, according to the possibilities of the prover and its add-on tools.
\<close>


subsection \<open>Documentation\<close>

text \<open>
  The \<^emph>\<open>Documentation\<close> panel of Isabelle/jEdit provides access to some example
  theory files and the standard Isabelle documentation. PDF files are opened
  by regular desktop operations of the underlying platform. The section
  ``Original jEdit Documentation'' contains the original \<^emph>\<open>User's Guide\<close> of
  this sophisticated text editor. The same is accessible via the \<^verbatim>\<open>Help\<close> menu
  or \<^verbatim>\<open>F1\<close> keyboard shortcut, using the built-in HTML viewer of Java/Swing.
  The latter also includes \<^emph>\<open>Frequently Asked Questions\<close> and documentation of
  individual plugins.

  Most of the information about jEdit is relevant for Isabelle/jEdit as well,
  but users need to keep in mind that defaults sometimes differ, and the
  official jEdit documentation does not know about the Isabelle plugin with
  its support for continuous checking of formal source text: jEdit is a plain
  text editor, but Isabelle/jEdit is a Prover IDE.
\<close>


subsection \<open>Plugins\<close>

text \<open>
  The \<^emph>\<open>Plugin Manager\<close> of jEdit allows to augment editor functionality by JVM
  modules (jars) that are provided by the central plugin repository, which is
  accessible via various mirror sites.

  Connecting to the plugin server-infrastructure of the jEdit project allows
  to update bundled plugins or to add further functionality. This needs to be
  done with the usual care for such an open bazaar of contributions. Arbitrary
  combinations of add-on features are apt to cause problems. It is advisable
  to start with the default configuration of Isabelle/jEdit and develop a
  sense how it is meant to work, before loading too many other plugins.

  \<^medskip>
  The \<^emph>\<open>Isabelle\<close> plugin is responsible for the main Prover IDE functionality
  of Isabelle/jEdit: it manages the prover session in the background. A few
  additional plugins are bundled with Isabelle/jEdit for convenience or out of
  necessity, notably \<^emph>\<open>Console\<close> with its \<^emph>\<open>Scala\<close> sub-plugin
  (\secref{sec:scala-console}) and \<^emph>\<open>SideKick\<close> with some Isabelle-specific
  parsers for document tree structure (\secref{sec:sidekick}). The
  \<^emph>\<open>Navigator\<close> plugin is particularly important for hyperlinks within the
  formal document-model (\secref{sec:tooltips-hyperlinks}). Further plugins
  (e.g.\ \<^emph>\<open>ErrorList\<close>, \<^emph>\<open>Code2HTML\<close>) are included to saturate the dependencies
  of bundled plugins, but have no particular use in Isabelle/jEdit.
\<close>


subsection \<open>Options \label{sec:options}\<close>

text \<open>
  Both jEdit and Isabelle have distinctive management of persistent options.

  Regular jEdit options are accessible via the dialogs \<^emph>\<open>Utilities~/ Global
  Options\<close> or \<^emph>\<open>Plugins~/ Plugin Options\<close>, with a second chance to flip the
  two within the central options dialog. Changes are stored in
  \<^path>\<open>$JEDIT_SETTINGS/properties\<close> and \<^path>\<open>$JEDIT_SETTINGS/keymaps\<close>.

  Isabelle system options are managed by Isabelle/Scala and changes are stored
  in \<^path>\<open>$ISABELLE_HOME_USER/etc/preferences\<close>, independently of
  other jEdit properties. See also @{cite "isabelle-system"}, especially the
  coverage of sessions and command-line tools like @{tool build} or @{tool
  options}.

  Those Isabelle options that are declared as \<^verbatim>\<open>public\<close> are configurable in
  Isabelle/jEdit via \<^emph>\<open>Plugin Options~/ Isabelle~/ General\<close>. Moreover, there
  are various options for rendering document content, which are configurable
  via \<^emph>\<open>Plugin Options~/ Isabelle~/ Rendering\<close>. Thus \<^emph>\<open>Plugin Options~/
  Isabelle\<close> in jEdit provides a view on a subset of Isabelle system options.
  Note that some of these options affect general parameters that are relevant
  outside Isabelle/jEdit as well, e.g.\ @{system_option threads} or
  @{system_option parallel_proofs} for the Isabelle build tool @{cite
  "isabelle-system"}, but it is possible to use the settings variable
  @{setting ISABELLE_BUILD_OPTIONS} to change defaults for batch builds
  without affecting the Prover IDE.

  The jEdit action @{action_def isabelle.options} opens the options dialog for
  the Isabelle plugin; it can be mapped to editor GUI elements as usual.

  \<^medskip>
  Options are usually loaded on startup and saved on shutdown of
  Isabelle/jEdit. Editing the generated \<^path>\<open>$JEDIT_SETTINGS/properties\<close>
  or \<^path>\<open>$ISABELLE_HOME_USER/etc/preferences\<close> manually while the
  application is running may cause lost updates!
\<close>


subsection \<open>Keymaps\<close>

text \<open>
  Keyboard shortcuts are managed as a separate concept of \<^emph>\<open>keymap\<close> that is
  configurable via \<^emph>\<open>Global Options~/ Shortcuts\<close>. The \<^verbatim>\<open>imported\<close> keymap is
  derived from the initial environment of properties that is available at the
  first start of the editor; afterwards the keymap file takes precedence and
  is no longer affected by change of default properties.

  Users may modify their keymap later, but this can lead to conflicts with
  \<^verbatim>\<open>shortcut\<close> properties in \<^file>\<open>$JEDIT_HOME/src/jEdit.props\<close>.

  The action @{action_def "isabelle.keymap-merge"} helps to resolve pending
  Isabelle keymap changes wrt. the current jEdit keymap; non-conflicting
  changes are applied implicitly. This action is automatically invoked on
  Isabelle/jEdit startup.
\<close>


section \<open>Command-line invocation \label{sec:command-line}\<close>

text \<open>
  Isabelle/jEdit is normally invoked as a single-instance desktop application,
  based on platform-specific executables for Linux, Windows, macOS.

  It is also possible to invoke the Prover IDE on the command-line, with some
  extra options and environment settings. The command-line usage of @{tool_def
  jedit} is as follows:
  @{verbatim [display]
\<open>Usage: isabelle jedit [OPTIONS] [FILES ...]

  Options are:
    -A NAME      ancestor session for option -R (default: parent)
    -D NAME=X    set JVM system property
    -J OPTION    add JVM runtime option
                 (default $JEDIT_JAVA_SYSTEM_OPTIONS $JEDIT_JAVA_OPTIONS)
    -R NAME      build image with requirements from other sessions
    -b           build only
    -d DIR       include session directory
    -f           fresh build
    -i NAME      include session in name-space of theories
    -j OPTION    add jEdit runtime option
                 (default $JEDIT_OPTIONS)
    -l NAME      logic image name
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -p CMD       ML process command prefix (process policy)
    -s           system build mode for session image (system_heaps=true)
    -u           user build mode for session image (system_heaps=false)

  Start jEdit with Isabelle plugin setup and open FILES
  (default "$USER_HOME/Scratch.thy" or ":" for empty buffer).\<close>}

  The \<^verbatim>\<open>-l\<close> option specifies the session name of the logic image to be used
  for proof processing. Additional session root directories may be included
  via option \<^verbatim>\<open>-d\<close> to augment the session name space (see also @{cite
  "isabelle-system"}). By default, the specified image is checked and built on
  demand, but option \<^verbatim>\<open>-n\<close> bypasses the implicit build process for the
  selected session image. Options \<^verbatim>\<open>-s\<close> and \<^verbatim>\<open>-u\<close> override the default system
  option @{system_option system_heaps}: this determines where to store the
  session image of @{tool build}.

  The \<^verbatim>\<open>-R\<close> option builds an auxiliary logic image with all theories from
  other sessions that are not already present in its parent; it also opens the
  session \<^verbatim>\<open>ROOT\<close> entry in the editor to facilitate editing of the main
  session. The \<^verbatim>\<open>-A\<close> option specifies and alternative ancestor session for
  option \<^verbatim>\<open>-R\<close>: this allows to restructure the hierarchy of session images on
  the spot.

  The \<^verbatim>\<open>-i\<close> option includes additional sessions into the name-space of
  theories: multiple occurrences are possible.

  The \<^verbatim>\<open>-m\<close> option specifies additional print modes for the prover process.
  Note that the system option @{system_option_ref jedit_print_mode} allows to
  do the same persistently (e.g.\ via the \<^emph>\<open>Plugin Options\<close> dialog of
  Isabelle/jEdit), without requiring command-line invocation.

  The \<^verbatim>\<open>-J\<close> and \<^verbatim>\<open>-j\<close> options pass additional low-level options to the JVM or
  jEdit, respectively. The defaults are provided by the Isabelle settings
  environment @{cite "isabelle-system"}, but note that these only work for the
  command-line tool described here, and not the desktop application.

  The \<^verbatim>\<open>-D\<close> option allows to define JVM system properties; this is passed
  directly to the underlying \<^verbatim>\<open>java\<close> process.

  The \<^verbatim>\<open>-b\<close> and \<^verbatim>\<open>-f\<close> options control the self-build mechanism of
  Isabelle/jEdit. This is only relevant for building from sources, which also
  requires an auxiliary \<^verbatim>\<open>jedit_build\<close> component from
  \<^url>\<open>https://isabelle.in.tum.de/components\<close>. The official Isabelle release
  already includes a pre-built version of Isabelle/jEdit.

  \<^bigskip>
  It is also possible to connect to an already running Isabelle/jEdit process
  via @{tool_def jedit_client}:
  @{verbatim [display]
\<open>Usage: isabelle jedit_client [OPTIONS] [FILES ...]

  Options are:
    -c           only check presence of server
    -n           only report server name
    -s NAME      server name (default Isabelle)

  Connect to already running Isabelle/jEdit instance and open FILES\<close>}

  The \<^verbatim>\<open>-c\<close> option merely checks the presence of the server, producing a
  process return-code.

  The \<^verbatim>\<open>-n\<close> option reports the server name, and the \<^verbatim>\<open>-s\<close> option provides a
  different server name. The default server name is the official distribution
  name (e.g.\ \<^verbatim>\<open>Isabelle2020\<close>). Thus @{tool jedit_client} can connect to the
  Isabelle desktop application without further options.

  The \<^verbatim>\<open>-p\<close> option allows to override the implicit default of the system
  option @{system_option_ref ML_process_policy} for ML processes started by
  the Prover IDE, e.g. to control CPU affinity on multiprocessor systems.

  The JVM system property \<^verbatim>\<open>isabelle.jedit_server\<close> provides a different server
  name, e.g.\ use \<^verbatim>\<open>isabelle jedit -Disabelle.jedit_server=\<close>\<open>name\<close> and
  \<^verbatim>\<open>isabelle jedit_client -s\<close>~\<open>name\<close> to connect later on.
\<close>


section \<open>GUI rendering\<close>

subsection \<open>Look-and-feel \label{sec:look-and-feel}\<close>

text \<open>
  jEdit is a Java/AWT/Swing application with the ambition to support
  ``native'' look-and-feel on all platforms, within the limits of what Java
  provider and major operating systems allow (see also \secref{sec:problems}).

  Isabelle/jEdit enables platform-specific look-and-feel by default as
  follows.

    \<^descr>[Linux:] The platform-independent \<^emph>\<open>Metal\<close> is used by default.

    The Linux-specific \<^emph>\<open>GTK+\<close> look-and-feel often works, but the overall GTK
    theme and options need to be selected to suite Java/AWT/Swing. Note that
    the Java Virtual Machine has no direct influence of GTK rendering: it
    happens within external C libraries.

    \<^descr>[Windows:] Regular \<^emph>\<open>Windows\<close> look-and-feel is used by default.

    \<^descr>[macOS:] Regular \<^emph>\<open>Mac OS X\<close> look-and-feel is used by default.

  Users may experiment with different Swing look-and-feels, but need to keep
  in mind that this extra variance of GUI functionality often causes problems.
  The platform-independent \<^emph>\<open>Metal\<close> look-and-feel should work smoothly on all
  platforms, although its is technically and stylistically outdated.

  Changing the look-and-feel in \<^emph>\<open>Global Options~/ Appearance\<close> may update the
  GUI only partially: a proper restart of Isabelle/jEdit is usually required.
\<close>


subsection \<open>Displays with high resolution \label{sec:hdpi}\<close>

text \<open>
  In 2020, we usually see displays with high resolution like ``Ultra HD'' /
  ``4K'' at $3840 \times 2160$, or more. Old ``Full HD'' displays at $1920
  \times 1080$ pixels are still being used, but Java 11 font-rendering might
  look bad on it. GUI layouts are lagging behind the high resolution trends,
  and implicitly assume very old-fashioned $1024 \times 768$ or $1280 \times
  1024$ screens and fonts with 12 or 14 pixels. Java and jEdit do provide
  reasonable support for high resolution, but this requires manual
  adjustments as described below.

  \<^medskip> The \<^bold>\<open>operating-system\<close> often provides some configuration for global
  scaling of text fonts, e.g.\ to enlarge it uniformly by $200\%$. This
  impacts regular GUI elements, when used with native look-and-feel: Linux
  \<^emph>\<open>GTK+\<close>, \<^emph>\<open>Windows\<close>, \<^emph>\<open>Mac OS X\<close>, respectively. Alternatively, it is
  possible to use the platform-independent \<^emph>\<open>Metal\<close> look-and-feel and change
  its main font sizes via jEdit options explained below. The Isabelle/jEdit
  \<^bold>\<open>application\<close> provides further options to adjust font sizes in particular
  GUI elements. Here is a summary of all relevant font properties:

    \<^item> \<^emph>\<open>Global Options / Text Area / Text font\<close>: the main text area font,
    which is also used as reference point for various derived font sizes,
    e.g.\ the \<^emph>\<open>Output\<close> (\secref{sec:output}) and \<^emph>\<open>State\<close>
    (\secref{sec:state-output}) panels.

    \<^item> \<^emph>\<open>Global Options / Gutter / Gutter font\<close>: the font for the gutter area
    left of the main text area, e.g.\ relevant for display of line numbers
    (disabled by default).

    \<^item> \<^emph>\<open>Global Options / Appearance / Button, menu and label font\<close> as well as
    \<^emph>\<open>List and text field font\<close>: this specifies the primary and secondary font
    for the \<^emph>\<open>Metal\<close> look-and-feel (\secref{sec:look-and-feel}).

    \<^item> \<^emph>\<open>Plugin Options / Isabelle / General / Reset Font Size\<close>: the main text
    area font size for action @{action_ref "isabelle.reset-font-size"}, e.g.\
    relevant for quick scaling like in common web browsers.

    \<^item> \<^emph>\<open>Plugin Options / Console / General / Font\<close>: the console window font,
    e.g.\ relevant for Isabelle/Scala command-line.

  In \figref{fig:isabelle-jedit-hdpi} the \<^emph>\<open>Metal\<close> look-and-feel is configured
  with custom fonts at 36 pixels, and the main text area and console at 40
  pixels. This leads to fairly good rendering quality, despite the
  old-fashioned appearance of \<^emph>\<open>Metal\<close>.

  \begin{sidewaysfigure}[!htb]
  \begin{center}
  \includegraphics[width=\textwidth]{isabelle-jedit-hdpi}
  \end{center}
  \caption{Metal look-and-feel with custom fonts for high resolution}
  \label{fig:isabelle-jedit-hdpi}
  \end{sidewaysfigure}
\<close>


chapter \<open>Augmented jEdit functionality\<close>

section \<open>Dockable windows \label{sec:dockables}\<close>

text \<open>
  In jEdit terminology, a \<^emph>\<open>view\<close> is an editor window with one or more \<^emph>\<open>text
  areas\<close> that show the content of one or more \<^emph>\<open>buffers\<close>. A regular view may
  be surrounded by \<^emph>\<open>dockable windows\<close> that show additional information in
  arbitrary format, not just text; a \<^emph>\<open>plain view\<close> does not allow dockables.
  The \<^emph>\<open>dockable window manager\<close> of jEdit organizes these dockable windows,
  either as \<^emph>\<open>floating\<close> windows, or \<^emph>\<open>docked\<close> panels within one of the four
  margins of the view. There may be any number of floating instances of some
  dockable window, but at most one docked instance; jEdit actions that address
  \<^emph>\<open>the\<close> dockable window of a particular kind refer to the unique docked
  instance.

  Dockables are used routinely in jEdit for important functionality like
  \<^emph>\<open>HyperSearch Results\<close> or the \<^emph>\<open>File System Browser\<close>. Plugins often provide
  a central dockable to access their main functionality, which may be opened
  by the user on demand. The Isabelle/jEdit plugin takes this approach to the
  extreme: its plugin menu provides the entry-points to many panels that are
  managed as dockable windows. Some important panels are docked by default,
  e.g.\ \<^emph>\<open>Documentation\<close>, \<^emph>\<open>State\<close>, \<^emph>\<open>Theories\<close> \<^emph>\<open>Output\<close>, \<^emph>\<open>Query\<close>. The user
  can change this arrangement easily and persistently.

  Compared to plain jEdit, dockable window management in Isabelle/jEdit is
  slightly augmented according to the the following principles:

  \<^item> Floating windows are dependent on the main window as \<^emph>\<open>dialog\<close> in
  the sense of Java/AWT/Swing. Dialog windows always stay on top of the view,
  which is particularly important in full-screen mode. The desktop environment
  of the underlying platform may impose further policies on such dependent
  dialogs, in contrast to fully independent windows, e.g.\ some window
  management functions may be missing.

  \<^item> Keyboard focus of the main view vs.\ a dockable window is carefully
  managed according to the intended semantics, as a panel mainly for output or
  input. For example, activating the \<^emph>\<open>Output\<close> (\secref{sec:output}) or State
  (\secref{sec:state-output}) panel via the dockable window manager returns
  keyboard focus to the main text area, but for \<^emph>\<open>Query\<close> (\secref{sec:query})
  or \<^emph>\<open>Sledgehammer\<close> \secref{sec:sledgehammer} the focus is given to the main
  input field of that panel.

  \<^item> Panels that provide their own text area for output have an additional
  dockable menu item \<^emph>\<open>Detach\<close>. This produces an independent copy of the
  current output as a floating \<^emph>\<open>Info\<close> window, which displays that content
  independently of ongoing changes of the PIDE document-model. Note that
  Isabelle/jEdit popup windows (\secref{sec:tooltips-hyperlinks}) provide a
  similar \<^emph>\<open>Detach\<close> operation as an icon.
\<close>


section \<open>Isabelle symbols \label{sec:symbols}\<close>

text \<open>
  Isabelle sources consist of \<^emph>\<open>symbols\<close> that extend plain ASCII to allow
  infinitely many mathematical symbols within the formal sources. This works
  without depending on particular encodings and varying Unicode
  standards.\<^footnote>\<open>Raw Unicode characters within formal sources compromise
  portability and reliability in the face of changing interpretation of
  special features of Unicode, such as Combining Characters or Bi-directional
  Text.\<close> See @{cite "Wenzel:2011:CICM"}.

  For the prover back-end, formal text consists of ASCII characters that are
  grouped according to some simple rules, e.g.\ as plain ``\<^verbatim>\<open>a\<close>'' or symbolic
  ``\<^verbatim>\<open>\<alpha>\<close>''. For the editor front-end, a certain subset of symbols is rendered
  physically via Unicode glyphs, to show ``\<^verbatim>\<open>\<alpha>\<close>'' as ``\<open>\<alpha>\<close>'', for example.
  This symbol interpretation is specified by the Isabelle system distribution
  in \<^file>\<open>$ISABELLE_HOME/etc/symbols\<close> and may be augmented by the user in
  \<^path>\<open>$ISABELLE_HOME_USER/etc/symbols\<close>.

  The appendix of @{cite "isabelle-isar-ref"} gives an overview of the
  standard interpretation of finitely many symbols from the infinite
  collection. Uninterpreted symbols are displayed literally, e.g.\
  ``\<^verbatim>\<open>\<foobar>\<close>''. Overlap of Unicode characters used in symbol
  interpretation with informal ones (which might appear e.g.\ in comments)
  needs to be avoided. Raw Unicode characters within prover source files
  should be restricted to informal parts, e.g.\ to write text in non-latin
  alphabets in comments.
\<close>

paragraph \<open>Encoding.\<close>

text \<open>Technically, the Unicode interpretation of Isabelle symbols is an
  \<^emph>\<open>encoding\<close> called \<^verbatim>\<open>UTF-8-Isabelle\<close> in jEdit (\<^emph>\<open>not\<close> in the underlying
  JVM). It is provided by the Isabelle Base plugin and enabled by default for
  all source files in Isabelle/jEdit.

  Sometimes such defaults are reset accidentally, or malformed UTF-8 sequences
  in the text force jEdit to fall back on a different encoding like
  \<^verbatim>\<open>ISO-8859-15\<close>. In that case, verbatim ``\<^verbatim>\<open>\<alpha>\<close>'' will be shown in the text
  buffer instead of its Unicode rendering ``\<open>\<alpha>\<close>''. The jEdit menu operation
  \<^emph>\<open>File~/ Reload with Encoding~/ UTF-8-Isabelle\<close> helps to resolve such
  problems (after repairing malformed parts of the text).

  If the loaded text already contains Unicode sequences that are in conflict
  with the Isabelle symbol encoding, the fallback-encoding UTF-8 is used and
  Isabelle symbols remain in literal \<^verbatim>\<open>\<symbol>\<close> form. The jEdit menu
  operation \<^emph>\<open>Utilities~/ Buffer Options~/ Character encoding\<close> allows to
  enforce \<^verbatim>\<open>UTF-8-Isabelle\<close>, but this will also change original Unicode text
  into Isabelle symbols when saving the file!
\<close>

paragraph \<open>Font.\<close>
text \<open>Correct rendering via Unicode requires a font that contains glyphs for
  the corresponding codepoints. There are also various unusual symbols with
  particular purpose in Isabelle, e.g.\ control symbols and very long arrows.
  Isabelle/jEdit prefers its own font collection \<^verbatim>\<open>Isabelle DejaVu\<close>, with
  families \<^verbatim>\<open>Serif\<close> (default for help texts), \<^verbatim>\<open>Sans\<close> (default for GUI
  elements), \<^verbatim>\<open>Mono Sans\<close> (default for text area). This ensures that all
  standard Isabelle symbols are shown on the screen (or printer) as expected.

  Note that a Java/AWT/Swing application can load additional fonts only if
  they are not installed on the operating system already! Outdated versions of
  Isabelle fonts that happen to be provided by the operating system prevent
  Isabelle/jEdit to use its bundled version. This could lead to missing glyphs
  (black rectangles), when the system version of a font is older than the
  application version. This problem can be avoided by refraining to
  ``install'' a copy of the Isabelle fonts in the first place, although it
  might be tempting to use the same font in other applications.

  HTML pages generated by Isabelle refer to the same Isabelle fonts as a
  server-side resource. Thus a web-browser can use that without requiring a
  locally installed copy.
\<close>

paragraph \<open>Input methods.\<close>
text \<open>In principle, Isabelle/jEdit could delegate the problem to produce
  Isabelle symbols in their Unicode rendering to the underlying operating
  system and its \<^emph>\<open>input methods\<close>. Regular jEdit also provides various ways to
  work with \<^emph>\<open>abbreviations\<close> to produce certain non-ASCII characters. Since
  none of these standard input methods work satisfactorily for the
  mathematical characters required for Isabelle, various specific
  Isabelle/jEdit mechanisms are provided.

  This is a summary for practically relevant input methods for Isabelle
  symbols.

  \<^enum> The \<^emph>\<open>Symbols\<close> panel: some GUI buttons allow to insert certain symbols in
  the text buffer. There are also tooltips to reveal the official Isabelle
  representation with some additional information about \<^emph>\<open>symbol
  abbreviations\<close> (see below).

  \<^enum> Copy/paste from decoded source files: text that is already rendered as
  Unicode can be re-used for other text. This also works between different
  applications, e.g.\ Isabelle/jEdit and some web browser or mail client, as
  long as the same Unicode interpretation of Isabelle symbols is used.

  \<^enum> Copy/paste from prover output within Isabelle/jEdit. The same principles
  as for text buffers apply, but note that \<^emph>\<open>copy\<close> in secondary Isabelle/jEdit
  windows works via the keyboard shortcuts \<^verbatim>\<open>C+c\<close> or \<^verbatim>\<open>C+INSERT\<close>, while jEdit
  menu actions always refer to the primary text area!

  \<^enum> Completion provided by the Isabelle plugin (see \secref{sec:completion}).
  Isabelle symbols have a canonical name and optional abbreviations. This can
  be used with the text completion mechanism of Isabelle/jEdit, to replace a
  prefix of the actual symbol like \<^verbatim>\<open>\<lambda>\<close>, or its name preceded by backslash
  \<^verbatim>\<open>\lambda\<close>, or its ASCII abbreviation \<^verbatim>\<open>%\<close> by the Unicode rendering.

  The following table is an extract of the information provided by the
  standard \<^file>\<open>$ISABELLE_HOME/etc/symbols\<close> file:

  \<^medskip>
  \begin{tabular}{lll}
    \<^bold>\<open>symbol\<close> & \<^bold>\<open>name with backslash\<close> & \<^bold>\<open>abbreviation\<close> \\\hline
    \<open>\<lambda>\<close> & \<^verbatim>\<open>\lambda\<close> & \<^verbatim>\<open>%\<close> \\
    \<open>\<Rightarrow>\<close> & \<^verbatim>\<open>\Rightarrow\<close> & \<^verbatim>\<open>=>\<close> \\
    \<open>\<Longrightarrow>\<close> & \<^verbatim>\<open>\Longrightarrow\<close> & \<^verbatim>\<open>==>\<close> \\[0.5ex]
    \<open>\<And>\<close> & \<^verbatim>\<open>\And\<close> & \<^verbatim>\<open>!!\<close> \\
    \<open>\<equiv>\<close> & \<^verbatim>\<open>\equiv\<close> & \<^verbatim>\<open>==\<close> \\[0.5ex]
    \<open>\<forall>\<close> & \<^verbatim>\<open>\forall\<close> & \<^verbatim>\<open>!\<close> \\
    \<open>\<exists>\<close> & \<^verbatim>\<open>\exists\<close> & \<^verbatim>\<open>?\<close> \\
    \<open>\<longrightarrow>\<close> & \<^verbatim>\<open>\longrightarrow\<close> & \<^verbatim>\<open>-->\<close> \\
    \<open>\<and>\<close> & \<^verbatim>\<open>\and\<close> & \<^verbatim>\<open>&\<close> \\
    \<open>\<or>\<close> & \<^verbatim>\<open>\or\<close> & \<^verbatim>\<open>|\<close> \\
    \<open>\<not>\<close> & \<^verbatim>\<open>\not\<close> & \<^verbatim>\<open>~\<close> \\
    \<open>\<noteq>\<close> & \<^verbatim>\<open>\noteq\<close> & \<^verbatim>\<open>~=\<close> \\
    \<open>\<in>\<close> & \<^verbatim>\<open>\in\<close> & \<^verbatim>\<open>:\<close> \\
    \<open>\<notin>\<close> & \<^verbatim>\<open>\notin\<close> & \<^verbatim>\<open>~:\<close> \\
  \end{tabular}
  \<^medskip>

  Note that the above abbreviations refer to the input method. The logical
  notation provides ASCII alternatives that often coincide, but sometimes
  deviate. This occasionally causes user confusion with old-fashioned Isabelle
  source that use ASCII replacement notation like \<^verbatim>\<open>!\<close> or \<^verbatim>\<open>ALL\<close> directly in
  the text.

  On the other hand, coincidence of symbol abbreviations with ASCII
  replacement syntax syntax helps to update old theory sources via explicit
  completion (see also \<^verbatim>\<open>C+b\<close> explained in \secref{sec:completion}).
\<close>

paragraph \<open>Control symbols.\<close>
text \<open>There are some special control symbols to modify the display style of a
  single symbol (without nesting). Control symbols may be applied to a region
  of selected text, either using the \<^emph>\<open>Symbols\<close> panel or keyboard shortcuts or
  jEdit actions. These editor operations produce a separate control symbol for
  each symbol in the text, in order to make the whole text appear in a certain
  style.

  \<^medskip>
  \begin{tabular}{llll}
    \<^bold>\<open>style\<close> & \<^bold>\<open>symbol\<close> & \<^bold>\<open>shortcut\<close> & \<^bold>\<open>action\<close> \\\hline
    superscript & \<^verbatim>\<open>\<^sup>\<close> & \<^verbatim>\<open>C+e UP\<close> & @{action_ref "isabelle.control-sup"} \\
    subscript & \<^verbatim>\<open>\<^sub>\<close> & \<^verbatim>\<open>C+e DOWN\<close> & @{action_ref "isabelle.control-sub"} \\
    bold face & \<^verbatim>\<open>\<^bold>\<close> & \<^verbatim>\<open>C+e RIGHT\<close> & @{action_ref "isabelle.control-bold"} \\
    emphasized & \<^verbatim>\<open>\<^emph>\<close> & \<^verbatim>\<open>C+e LEFT\<close> & @{action_ref "isabelle.control-emph"} \\
    reset & & \<^verbatim>\<open>C+e BACK_SPACE\<close> & @{action_ref "isabelle.control-reset"} \\
  \end{tabular}
  \<^medskip>

  To produce a single control symbol, it is also possible to complete on
  \<^verbatim>\<open>\sup\<close>, \<^verbatim>\<open>\sub\<close>, \<^verbatim>\<open>\bold\<close>, \<^verbatim>\<open>\emph\<close> as for regular symbols.

  The emphasized style only takes effect in document output (when used with a
  cartouche), but not in the editor.
\<close>


section \<open>Scala console \label{sec:scala-console}\<close>

text \<open>
  The \<^emph>\<open>Console\<close> plugin manages various shells (command interpreters), e.g.\
  \<^emph>\<open>BeanShell\<close>, which is the official jEdit scripting language, and the
  cross-platform \<^emph>\<open>System\<close> shell. Thus the console provides similar
  functionality than the Emacs buffers \<^verbatim>\<open>*scratch*\<close> and \<^verbatim>\<open>*shell*\<close>.

  Isabelle/jEdit extends the repertoire of the console by \<^emph>\<open>Scala\<close>, which is
  the regular Scala toplevel loop running inside the same JVM process as
  Isabelle/jEdit itself. This means the Scala command interpreter has access
  to the JVM name space and state of the running Prover IDE application. The
  default environment imports the full content of packages \<^verbatim>\<open>isabelle\<close> and
  \<^verbatim>\<open>isabelle.jedit\<close>.

  For example, \<^verbatim>\<open>PIDE\<close> refers to the Isabelle/jEdit plugin object, and \<^verbatim>\<open>view\<close>
  to the current editor view of jEdit. The Scala expression
  \<^verbatim>\<open>PIDE.snapshot(view)\<close> makes a PIDE document snapshot of the current buffer
  within the current editor view: it allows to retrieve document markup in a
  timeless~/ stateless manner, while the prover continues its processing.

  This helps to explore Isabelle/Scala functionality interactively. Some care
  is required to avoid interference with the internals of the running
  application.
\<close>


section \<open>Physical and logical files \label{sec:files}\<close>

text \<open>
  File specifications in jEdit follow various formats and conventions
  according to \<^emph>\<open>Virtual File Systems\<close>, which may be also provided by plugins.
  This allows to access remote files via the \<^verbatim>\<open>https:\<close> protocol prefix, for
  example. Isabelle/jEdit attempts to work with the file-system model of jEdit
  as far as possible. In particular, theory sources are passed from the editor
  to the prover, without indirection via the file-system. Thus files don't
  need to be saved: the editor buffer content is used directly.
\<close>


subsection \<open>Local files and environment variables \label{sec:local-files}\<close>

text \<open>
  Local files (without URL notation) are particularly important. The file path
  notation is that of the Java Virtual Machine on the underlying platform. On
  Windows the preferred form uses backslashes, but happens to accept forward
  slashes like Unix/POSIX as well. Further differences arise due to Windows
  drive letters and network shares: thus relative paths (with forward slashes)
  are portable, but absolute paths are not.

  File paths in Java are distinct from Isabelle; the latter uses POSIX
  notation with forward slashes on \<^emph>\<open>all\<close> platforms. Isabelle/ML on Windows
  uses Unix-style path notation, with drive letters according to Cygwin (e.g.\
  \<^verbatim>\<open>/cygdrive/c\<close>). Environment variables from the Isabelle process may be used
  freely, e.g.\ \<^file>\<open>$ISABELLE_HOME/etc/symbols\<close> or \<^file>\<open>$POLYML_HOME/README\<close>.
  There are special shortcuts: \<^dir>\<open>~\<close> for \<^dir>\<open>$USER_HOME\<close> and \<^dir>\<open>~~\<close> for
  \<^dir>\<open>$ISABELLE_HOME\<close>.

  \<^medskip> Since jEdit happens to support environment variables within file
  specifications as well, it is natural to use similar notation within the
  editor, e.g.\ in the file-browser. This does not work in full generality,
  though, due to the bias of jEdit towards platform-specific notation and of
  Isabelle towards POSIX. Moreover, the Isabelle settings environment is not
  accessible when starting Isabelle/jEdit via the desktop application wrapper,
  in contrast to @{tool jedit} run from the command line
  (\secref{sec:command-line}).

  Isabelle/jEdit imitates important system settings within the Java process
  environment, in order to allow easy access to these important places from
  the editor: \<^verbatim>\<open>$ISABELLE_HOME\<close>, \<^verbatim>\<open>$ISABELLE_HOME_USER\<close>, \<^verbatim>\<open>$JEDIT_HOME\<close>,
  \<^verbatim>\<open>$JEDIT_SETTINGS\<close>. The file browser of jEdit also includes \<^emph>\<open>Favorites\<close> for
  these locations.

  \<^medskip> Path specifications in prover input or output usually include formal
  markup that turns it into a hyperlink (see also
  \secref{sec:tooltips-hyperlinks}). This allows to open the corresponding
  file in the text editor, independently of the path notation. If the path
  refers to a directory, it is opened in the jEdit file browser.

  Formally checked paths in prover input are subject to completion
  (\secref{sec:completion}): partial specifications are resolved via directory
  content and possible completions are offered in a popup.
\<close>


subsection \<open>PIDE resources via virtual file-systems\<close>

text \<open>
  The jEdit file browser is docked by default, e.g. see
  \figref{fig:isabelle-jedit-hdpi} (left docking area). It provides immediate
  access to the local file-system, as well as important Isabelle resources via
  the \<^emph>\<open>Favorites\<close> menu. Environment variables like \<^verbatim>\<open>$ISABELLE_HOME\<close> are
  discussed in \secref{sec:local-files}. Virtual file-systems are more
  special: the idea is to present structured information like a directory
  tree. The following URLs are offered in the \<^emph>\<open>Favorites\<close> menu, or by
  corresponding jEdit actions.

    \<^item> URL \<^verbatim>\<open>isabelle-export:\<close> or action @{action_def
    "isabelle-export-browser"} shows a toplevel directory with theory names:
    each may provide its own tree structure of session exports. Exports are
    like a logical file-system for the current prover session, maintained as
    Isabelle/Scala data structures and written to the session database
    eventually. The \<^verbatim>\<open>isabelle-export:\<close> URL exposes the current content
    according to a snapshot of the document model. The file browser is \<^emph>\<open>not\<close>
    updated continuously when the PIDE document changes: the reload operation
    needs to be used explicitly. A notable example for exports is the command
    @{command_ref export_code} @{cite "isabelle-isar-ref"}.

    \<^item> URL \<^verbatim>\<open>isabelle-session:\<close> or action @{action_def
    "isabelle-session-browser"} show the structure of session chapters and
    sessions within them. What looks like a file-entry is actually a reference
    to the session definition in its corresponding \<^verbatim>\<open>ROOT\<close> file. The latter is
    subject to Prover IDE markup, so the session theories and other files may
    be browsed quickly by following hyperlinks in the text.
\<close>


section \<open>Indentation\<close>

text \<open>
  Isabelle/jEdit augments the existing indentation facilities of jEdit to take
  the structure of theory and proof texts into account. There is also special
  support for unstructured proof scripts (\<^theory_text>\<open>apply\<close> etc.).

    \<^descr>[Syntactic indentation] follows the outer syntax of Isabelle/Isar.

    Action @{action "indent-lines"} (shortcut \<^verbatim>\<open>C+i\<close>) indents the current line
    according to command keywords and some command substructure: this
    approximation may need further manual tuning.

    Action @{action "isabelle.newline"} (shortcut \<^verbatim>\<open>ENTER\<close>) indents the old
    and the new line according to command keywords only: leading to precise
    alignment of the main Isar language elements. This depends on option
    @{system_option_def "jedit_indent_newline"} (enabled by default).

    Regular input (via keyboard or completion) indents the current line
    whenever an new keyword is emerging at the start of the line. This depends
    on option @{system_option_def "jedit_indent_input"} (enabled by default).

    \<^descr>[Semantic indentation] adds additional white space to unstructured proof
    scripts via the number of subgoals. This requires information of ongoing
    document processing and may thus lag behind when the user is editing too
    quickly; see also option @{system_option_def "jedit_script_indent"} and
    @{system_option_def "jedit_script_indent_limit"}.

  The above options are accessible in the menu \<^emph>\<open>Plugins / Plugin Options /
  Isabelle / General\<close>. A prerequisite for advanced indentation is \<^emph>\<open>Utilities
  / Buffer Options / Automatic indentation\<close>: it needs to be set to \<^verbatim>\<open>full\<close>
  (default).
\<close>


section \<open>SideKick parsers \label{sec:sidekick}\<close>

text \<open>
  The \<^emph>\<open>SideKick\<close> plugin provides some general services to display buffer
  structure in a tree view. Isabelle/jEdit provides SideKick parsers for its
  main mode for theory files, ML files, as well as some minor modes for the
  \<^verbatim>\<open>NEWS\<close> file (see \figref{fig:sidekick}), session \<^verbatim>\<open>ROOT\<close> files, system
  \<^verbatim>\<open>options\<close>, and Bib{\TeX} files (\secref{sec:bibtex}).

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{sidekick}
  \end{center}
  \caption{The Isabelle NEWS file with SideKick tree view}
  \label{fig:sidekick}
  \end{figure}

  The default SideKick parser for theory files is \<^verbatim>\<open>isabelle\<close>: it provides a
  tree-view on the formal document structure, with section headings at the top
  and formal specification elements at the bottom. The alternative parser
  \<^verbatim>\<open>isabelle-context\<close> shows nesting of context blocks according to \<^theory_text>\<open>begin \<dots>
  end\<close> structure.

  \<^medskip>
  Isabelle/ML files are structured according to semi-formal comments that are
  explained in @{cite "isabelle-implementation"}. This outline is turned into
  a tree-view by default, by using the \<^verbatim>\<open>isabelle-ml\<close> parser. There is also a
  folding mode of the same name, for hierarchic text folds within ML files.

  \<^medskip>
  The special SideKick parser \<^verbatim>\<open>isabelle-markup\<close> exposes the uninterpreted
  markup tree of the PIDE document model of the current buffer. This is
  occasionally useful for informative purposes, but the amount of displayed
  information might cause problems for large buffers.
\<close>


chapter \<open>Prover IDE functionality \label{sec:document-model}\<close>

section \<open>Document model \label{sec:document-model}\<close>

text \<open>
  The document model is central to the PIDE architecture: the editor and the
  prover have a common notion of structured source text with markup, which is
  produced by formal processing. The editor is responsible for edits of
  document source, as produced by the user. The prover is responsible for
  reports of document markup, as produced by its processing in the background.

  Isabelle/jEdit handles classic editor events of jEdit, in order to connect
  the physical world of the GUI (with its singleton state) to the mathematical
  world of multiple document versions (with timeless and stateless updates).
\<close>


subsection \<open>Editor buffers and document nodes \label{sec:buffer-node}\<close>

text \<open>
  As a regular text editor, jEdit maintains a collection of \<^emph>\<open>buffers\<close> to
  store text files; each buffer may be associated with any number of visible
  \<^emph>\<open>text areas\<close>. Buffers are subject to an \<^emph>\<open>edit mode\<close> that is determined
  from the file name extension. The following modes are treated specifically
  in Isabelle/jEdit:

  \<^medskip>
  \begin{tabular}{lll}
  \<^bold>\<open>mode\<close> & \<^bold>\<open>file name\<close> & \<^bold>\<open>content\<close> \\\hline
  \<^verbatim>\<open>isabelle\<close> & \<^verbatim>\<open>*.thy\<close> & theory source \\
  \<^verbatim>\<open>isabelle-ml\<close> & \<^verbatim>\<open>*.ML\<close> & Isabelle/ML source \\
  \<^verbatim>\<open>sml\<close> & \<^verbatim>\<open>*.sml\<close> or \<^verbatim>\<open>*.sig\<close> & Standard ML source \\
  \<^verbatim>\<open>isabelle-root\<close> & \<^verbatim>\<open>ROOT\<close> & session root \\
  \<^verbatim>\<open>isabelle-options\<close> & & Isabelle options \\
  \<^verbatim>\<open>isabelle-news\<close> & & Isabelle NEWS \\
  \end{tabular}
  \<^medskip>

  All jEdit buffers are automatically added to the PIDE document-model as
  \<^emph>\<open>document nodes\<close>. The overall document structure is defined by the theory
  nodes in two dimensions:

    \<^enum> via \<^bold>\<open>theory imports\<close> that are specified in the \<^emph>\<open>theory header\<close> using
    concrete syntax of the @{command_ref theory} command @{cite
    "isabelle-isar-ref"};

    \<^enum> via \<^bold>\<open>auxiliary files\<close> that are included into a theory by \<^emph>\<open>load
    commands\<close>, notably @{command_ref ML_file} and @{command_ref SML_file}
    @{cite "isabelle-isar-ref"}.

  In any case, source files are managed by the PIDE infrastructure: the
  physical file-system only plays a subordinate role. The relevant version of
  source text is passed directly from the editor to the prover, using internal
  communication channels.
\<close>


subsection \<open>Theories \label{sec:theories}\<close>

text \<open>
  The \<^emph>\<open>Theories\<close> panel (see also \figref{fig:theories}) provides an overview
  of the status of continuous checking of theory nodes within the document
  model.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{theories}
  \end{center}
  \caption{Theories panel with an overview of the document-model, and jEdit
  text areas as editable views on some of the document nodes}
  \label{fig:theories}
  \end{figure}

  Theory imports are resolved automatically by the PIDE document model: all
  required files are loaded and stored internally, without the need to open
  corresponding jEdit buffers. Opening or closing editor buffers later on has
  no direct impact on the formal document content: it only affects visibility.

  In contrast, auxiliary files (e.g.\ from @{command ML_file} commands) are
  \<^emph>\<open>not\<close> resolved within the editor by default, but the prover process takes
  care of that. This may be changed by enabling the system option
  @{system_option jedit_auto_resolve}: it ensures that all files are uniformly
  provided by the editor.

  \<^medskip>
  The visible \<^emph>\<open>perspective\<close> of Isabelle/jEdit is defined by the collective
  view on theory buffers via open text areas. The perspective is taken as a
  hint for document processing: the prover ensures that those parts of a
  theory where the user is looking are checked, while other parts that are
  presently not required are ignored. The perspective is changed by opening or
  closing text area windows, or scrolling within a window.

  The \<^emph>\<open>Theories\<close> panel provides some further options to influence the process
  of continuous checking: it may be switched off globally to restrict the
  prover to superficial processing of command syntax. It is also possible to
  indicate theory nodes as \<^emph>\<open>required\<close> for continuous checking: this means
  such nodes and all their imports are always processed independently of the
  visibility status (if continuous checking is enabled). Big theory libraries
  that are marked as required can have significant impact on performance!

  The \<^emph>\<open>Purge\<close> button restricts the document model to theories that are
  required for open editor buffers: inaccessible theories are removed and will
  be rechecked when opened or imported later.

  \<^medskip>
  Formal markup of checked theory content is turned into GUI rendering, based
  on a standard repertoire known from mainstream IDEs for programming
  languages: colors, icons, highlighting, squiggly underlines, tooltips,
  hyperlinks etc. For outer syntax of Isabelle/Isar there is some traditional
  syntax-highlighting via static keywords and tokenization within the editor;
  this buffer syntax is determined from theory imports. In contrast, the
  painting of inner syntax (term language etc.)\ uses semantic information
  that is reported dynamically from the logical context. Thus the prover can
  provide additional markup to help the user to understand the meaning of
  formal text, and to produce more text with some add-on tools (e.g.\
  information messages with \<^emph>\<open>sendback\<close> markup by automated provers or
  disprovers in the background). \<close>


subsection \<open>Auxiliary files \label{sec:aux-files}\<close>

text \<open>
  Special load commands like @{command_ref ML_file} and @{command_ref
  SML_file} @{cite "isabelle-isar-ref"} refer to auxiliary files within some
  theory. Conceptually, the file argument of the command extends the theory
  source by the content of the file, but its editor buffer may be loaded~/
  changed~/ saved separately. The PIDE document model propagates changes of
  auxiliary file content to the corresponding load command in the theory, to
  update and process it accordingly: changes of auxiliary file content are
  treated as changes of the corresponding load command.

  \<^medskip>
  As a concession to the massive amount of ML files in Isabelle/HOL itself,
  the content of auxiliary files is only added to the PIDE document-model on
  demand, the first time when opened explicitly in the editor. There are
  further tricks to manage markup of ML files, such that Isabelle/HOL may be
  edited conveniently in the Prover IDE on small machines with only 8\,GB of
  main memory. Using \<^verbatim>\<open>Pure\<close> as logic session image, the exploration may start
  at the top \<^file>\<open>$ISABELLE_HOME/src/HOL/Main.thy\<close> or the bottom
  \<^file>\<open>$ISABELLE_HOME/src/HOL/HOL.thy\<close>, for example. It is also possible to
  explore the Isabelle/Pure bootstrap process (a virtual copy) by opening
  \<^file>\<open>$ISABELLE_HOME/src/Pure/ROOT.ML\<close> like a theory in the Prover IDE.

  Initially, before an auxiliary file is opened in the editor, the prover
  reads its content from the physical file-system. After the file is opened
  for the first time in the editor, e.g.\ by following the hyperlink
  (\secref{sec:tooltips-hyperlinks}) for the argument of its @{command
  ML_file} command, the content is taken from the jEdit buffer.

  The change of responsibility from prover to editor counts as an update of
  the document content, so subsequent theory sources need to be re-checked.
  When the buffer is closed, the responsibility remains to the editor: the
  file may be opened again without causing another document update.

  A file that is opened in the editor, but its theory with the load command is
  not, is presently inactive in the document model. A file that is loaded via
  multiple load commands is associated to an arbitrary one: this situation is
  morally unsupported and might lead to confusion.

  \<^medskip>
  Output that refers to an auxiliary file is combined with that of the
  corresponding load command, and shown whenever the file or the command are
  active (see also \secref{sec:output}).

  Warnings, errors, and other useful markup is attached directly to the
  positions in the auxiliary file buffer, in the manner of standard IDEs. By
  using the load command @{command SML_file} as explained in
  \<^file>\<open>$ISABELLE_HOME/src/Tools/SML/Examples.thy\<close>, Isabelle/jEdit may be used as
  fully-featured IDE for Standard ML, independently of theory or proof
  development: the required theory merely serves as some kind of project file
  for a collection of SML source modules.
\<close>


section \<open>Output \label{sec:output}\<close>

text \<open>
  Prover output consists of \<^emph>\<open>markup\<close> and \<^emph>\<open>messages\<close>. Both are directly
  attached to the corresponding positions in the original source text, and
  visualized in the text area, e.g.\ as text colours for free and bound
  variables, or as squiggly underlines for warnings, errors etc.\ (see also
  \figref{fig:output}). In the latter case, the corresponding messages are
  shown by hovering with the mouse over the highlighted text --- although in
  many situations the user should already get some clue by looking at the
  position of the text highlighting, without seeing the message body itself.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{output}
  \end{center}
  \caption{Multiple views on prover output: gutter with icon, text area with
  popup, text overview column, \<^emph>\<open>Theories\<close> panel, \<^emph>\<open>Output\<close> panel}
  \label{fig:output}
  \end{figure}

  The ``gutter'' on the left-hand-side of the text area uses icons to
  provide a summary of the messages within the adjacent text line. Message
  priorities are used to prefer errors over warnings, warnings over
  information messages; other output is ignored.

  The ``text overview column'' on the right-hand-side of the text area uses
  similar information to paint small rectangles for the overall status of the
  whole text buffer. The graphics is scaled to fit the logical buffer length
  into the given window height. Mouse clicks on the overview area move the
  cursor approximately to the corresponding text line in the buffer.

  The \<^emph>\<open>Theories\<close> panel provides another course-grained overview, but without
  direct correspondence to text positions. The coloured rectangles represent
  the amount of messages of a certain kind (warnings, errors, etc.) and the
  execution status of commands. The border of each rectangle indicates the
  overall status of processing: a thick border means it is \<^emph>\<open>finished\<close> or
  \<^emph>\<open>failed\<close> (with color for errors). A double-click on one of the theory
  entries with their status overview opens the corresponding text buffer,
  without moving the cursor to a specific point.

  \<^medskip>
  The \<^emph>\<open>Output\<close> panel displays prover messages that correspond to a given
  command, within a separate window. The cursor position in the presently
  active text area determines the prover command whose cumulative message
  output is appended and shown in that window (in canonical order according to
  the internal execution of the command). There are also control elements to
  modify the update policy of the output wrt.\ continued editor movements:
  \<^emph>\<open>Auto update\<close> and \<^emph>\<open>Update\<close>. This is particularly useful for multiple
  instances of the \<^emph>\<open>Output\<close> panel to look at different situations.
  Alternatively, the panel can be turned into a passive \<^emph>\<open>Info\<close> window via the
  \<^emph>\<open>Detach\<close> menu item.

  Proof state is handled separately (\secref{sec:state-output}), but it is
  also possible to tick the corresponding checkbox to append it to regular
  output (\figref{fig:output-including-state}). This is a globally persistent
  option: it affects all open panels and future editor sessions.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{output-including-state}
  \end{center}
  \caption{Proof state display within the regular output panel}
  \label{fig:output-including-state}
  \end{figure}

  \<^medskip>
  Following the IDE principle, regular messages are attached to the original
  source in the proper place and may be inspected on demand via popups. This
  excludes messages that are somehow internal to the machinery of proof
  checking, notably \<^emph>\<open>proof state\<close> and \<^emph>\<open>tracing\<close>.

  In any case, the same display technology is used for small popups and big
  output windows. The formal text contains markup that may be explored
  recursively via further popups and hyperlinks (see
  \secref{sec:tooltips-hyperlinks}), or clicked directly to initiate certain
  actions (see \secref{sec:auto-tools} and \secref{sec:sledgehammer}).

  \<^medskip>
  Alternatively, the subsequent actions (with keyboard shortcuts) allow to
  show tooltip messages or navigate error positions:

  \<^medskip>
  \begin{tabular}[t]{l}
  @{action_ref "isabelle.tooltip"} (\<^verbatim>\<open>CS+b\<close>) \\
  @{action_ref "isabelle.message"} (\<^verbatim>\<open>CS+m\<close>) \\
  \end{tabular}\quad
  \begin{tabular}[t]{l}
  @{action_ref "isabelle.first-error"} (\<^verbatim>\<open>CS+a\<close>) \\
  @{action_ref "isabelle.last-error"} (\<^verbatim>\<open>CS+z\<close>) \\
  @{action_ref "isabelle.next-error"} (\<^verbatim>\<open>CS+n\<close>) \\
  @{action_ref "isabelle.prev-error"} (\<^verbatim>\<open>CS+p\<close>) \\
  \end{tabular}
  \<^medskip>
\<close>


section \<open>Proof state \label{sec:state-output}\<close>

text \<open>
  The main purpose of the Prover IDE is to help the user editing proof
  documents, with ongoing formal checking by the prover in the background.
  This can be done to some extent in the main text area alone, especially for
  well-structured Isar proofs.

  Nonetheless, internal proof state needs to be inspected in many situations
  of exploration and ``debugging''. The \<^emph>\<open>State\<close> panel shows exclusively such
  proof state messages without further distraction, while all other messages
  are displayed in \<^emph>\<open>Output\<close> (\secref{sec:output}).
  \Figref{fig:output-and-state} shows a typical GUI layout where both panels
  are open.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{output-and-state}
  \end{center}
  \caption{Separate proof state display (right) and other output (bottom).}
  \label{fig:output-and-state}
  \end{figure}

  Another typical arrangement has more than one \<^emph>\<open>State\<close> panel open (as
  floating windows), with \<^emph>\<open>Auto update\<close> disabled to look at an old situation
  while the proof text in the vicinity is changed. The \<^emph>\<open>Update\<close> button
  triggers an explicit one-shot update; this operation is also available via
  the action @{action "isabelle.update-state"} (keyboard shortcut \<^verbatim>\<open>S+ENTER\<close>).

  On small screens, it is occasionally useful to have all messages
  concatenated in the regular \<^emph>\<open>Output\<close> panel, e.g.\ see
  \figref{fig:output-including-state}.

  \<^medskip>
  The mechanics of \<^emph>\<open>Output\<close> versus \<^emph>\<open>State\<close> are slightly different:

    \<^item> \<^emph>\<open>Output\<close> shows information that is continuously produced and already
    present when the GUI wants to show it. This is implicitly controlled by
    the visible perspective on the text.

    \<^item> \<^emph>\<open>State\<close> initiates a real-time query on demand, with a full round trip
    including a fresh print operation on the prover side. This is controlled
    explicitly when the cursor is moved to the next command (\<^emph>\<open>Auto update\<close>)
    or the \<^emph>\<open>Update\<close> operation is triggered.

  This can make a difference in GUI responsibility and resource usage within
  the prover process. Applications with very big proof states that are only
  inspected in isolation work better with the \<^emph>\<open>State\<close> panel.
\<close>


section \<open>Query \label{sec:query}\<close>

text \<open>
  The \<^emph>\<open>Query\<close> panel provides various GUI forms to request extra information
  from the prover, as a replacement of old-style diagnostic commands like
  @{command find_theorems}. There are input fields and buttons for a
  particular query command, with output in a dedicated text area.

  The main query modes are presented as separate tabs: \<^emph>\<open>Find Theorems\<close>,
  \<^emph>\<open>Find Constants\<close>, \<^emph>\<open>Print Context\<close>, e.g.\ see \figref{fig:query}. As usual
  in jEdit, multiple \<^emph>\<open>Query\<close> windows may be active at the same time: any
  number of floating instances, but at most one docked instance (which is used
  by default).

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{query}
  \end{center}
  \caption{An instance of the Query panel: find theorems}
  \label{fig:query}
  \end{figure}

  \<^medskip>
  The following GUI elements are common to all query modes:

    \<^item> The spinning wheel provides feedback about the status of a pending query
    wrt.\ the evaluation of its context and its own operation.

    \<^item> The \<^emph>\<open>Apply\<close> button attaches a fresh query invocation to the current
    context of the command where the cursor is pointing in the text.

    \<^item> The \<^emph>\<open>Search\<close> field allows to highlight query output according to some
    regular expression, in the notation that is commonly used on the Java
    platform.\<^footnote>\<open>\<^url>\<open>https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/util/regex/Pattern.html\<close>\<close>
    This may serve as an additional visual filter of the result.

    \<^item> The \<^emph>\<open>Zoom\<close> box controls the font size of the output area.

  All query operations are asynchronous: there is no need to wait for the
  evaluation of the document for the query context, nor for the query
  operation itself. Query output may be detached as independent \<^emph>\<open>Info\<close>
  window, using a menu operation of the dockable window manager. The printed
  result usually provides sufficient clues about the original query, with some
  hyperlink to its context (via markup of its head line).
\<close>


subsection \<open>Find theorems\<close>

text \<open>
  The \<^emph>\<open>Query\<close> panel in \<^emph>\<open>Find Theorems\<close> mode retrieves facts from the theory
  or proof context matching all of given criteria in the \<^emph>\<open>Find\<close> text field. A
  single criterion has the following syntax:

  \<^rail>\<open>
    ('-'?) ('name' ':' @{syntax name} | 'intro' | 'elim' | 'dest' |
      'solves' | 'simp' ':' @{syntax term} | @{syntax term})
  \<close>

  See also the Isar command @{command_ref find_theorems} in @{cite
  "isabelle-isar-ref"}.
\<close>


subsection \<open>Find constants\<close>

text \<open>
  The \<^emph>\<open>Query\<close> panel in \<^emph>\<open>Find Constants\<close> mode prints all constants whose type
  meets all of the given criteria in the \<^emph>\<open>Find\<close> text field. A single
  criterion has the following syntax:

  \<^rail>\<open>
    ('-'?)
      ('name' ':' @{syntax name} | 'strict' ':' @{syntax type} | @{syntax type})
  \<close>

  See also the Isar command @{command_ref find_consts} in @{cite
  "isabelle-isar-ref"}.
\<close>


subsection \<open>Print context\<close>

text \<open>
  The \<^emph>\<open>Query\<close> panel in \<^emph>\<open>Print Context\<close> mode prints information from the
  theory or proof context, or proof state. See also the Isar commands
  @{command_ref print_context}, @{command_ref print_cases}, @{command_ref
  print_term_bindings}, @{command_ref print_theorems}, described in @{cite
  "isabelle-isar-ref"}.
\<close>


section \<open>Tooltips and hyperlinks \label{sec:tooltips-hyperlinks}\<close>

text \<open>
  Formally processed text (prover input or output) contains rich markup that
  can be explored by using the \<^verbatim>\<open>CONTROL\<close> modifier key on Linux and Windows,
  or \<^verbatim>\<open>COMMAND\<close> on macOS. Hovering with the mouse while the modifier is
  pressed reveals a \<^emph>\<open>tooltip\<close> (grey box over the text with a yellow popup)
  and/or a \<^emph>\<open>hyperlink\<close> (black rectangle over the text with change of mouse
  pointer); see also \figref{fig:tooltip}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{popup1}
  \end{center}
  \caption{Tooltip and hyperlink for some formal entity}
  \label{fig:tooltip}
  \end{figure}

  Tooltip popups use the same rendering technology as the main text area, and
  further tooltips and/or hyperlinks may be exposed recursively by the same
  mechanism; see \figref{fig:nested-tooltips}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{popup2}
  \end{center}
  \caption{Nested tooltips over formal entities}
  \label{fig:nested-tooltips}
  \end{figure}

  The tooltip popup window provides some controls to \<^emph>\<open>close\<close> or \<^emph>\<open>detach\<close> the
  window, turning it into a separate \<^emph>\<open>Info\<close> window managed by jEdit. The
  \<^verbatim>\<open>ESCAPE\<close> key closes \<^emph>\<open>all\<close> popups, which is particularly relevant when
  nested tooltips are stacking up.

  \<^medskip>
  A black rectangle in the text indicates a hyperlink that may be followed by
  a mouse click (while the \<^verbatim>\<open>CONTROL\<close> or \<^verbatim>\<open>COMMAND\<close> modifier key is still
  pressed). Such jumps to other text locations are recorded by the
  \<^emph>\<open>Navigator\<close> plugin, which is bundled with Isabelle/jEdit and enabled by
  default. There are usually navigation arrows in the main jEdit toolbar.

  Note that the link target may be a file that is itself not subject to formal
  document processing of the editor session and thus prevents further
  exploration: the chain of hyperlinks may end in some source file of the
  underlying logic image, or within the ML bootstrap sources of Isabelle/Pure.
\<close>


section \<open>Formal scopes and semantic selection\<close>

text \<open>
  Formal entities are semantically annotated in the source text as explained
  in \secref{sec:tooltips-hyperlinks}. A \<^emph>\<open>formal scope\<close> consists of the
  defining position with all its referencing positions. This correspondence is
  highlighted in the text according to the cursor position, see also
  \figref{fig:scope1}. Here the referencing positions are rendered with an
  additional border, in reminiscence to a hyperlink. A mouse click with \<^verbatim>\<open>C\<close>
  modifier, or the action @{action_def "isabelle.goto-entity"} (shortcut
  \<^verbatim>\<open>CS+d\<close>) jumps to the original defining position.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{scope1}
  \end{center}
  \caption{Scope of formal entity: defining vs.\ referencing positions}
  \label{fig:scope1}
  \end{figure}

  The action @{action_def "isabelle.select-entity"} (shortcut \<^verbatim>\<open>CS+ENTER\<close>)
  supports semantic selection of all occurrences of the formal entity at the
  caret position, with a defining position in the current editor buffer. This
  facilitates systematic renaming, using regular jEdit editing of a
  multi-selection, see also \figref{fig:scope2}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{scope2}
  \end{center}
  \caption{The result of semantic selection and systematic renaming}
  \label{fig:scope2}
  \end{figure}

  By default, the visual feedback on scopes is restricted to definitions
  within the visible text area. The keyboard modifier \<^verbatim>\<open>CS\<close> overrides this:
  then all defining and referencing positions are shown. This modifier may be
  configured via option @{system_option jedit_focus_modifier}; the default
  coincides with the modifier for the above keyboard actions.
\<close>


section \<open>Completion \label{sec:completion}\<close>

text \<open>
  Smart completion of partial input is the IDE functionality \<^emph>\<open>par
  excellance\<close>. Isabelle/jEdit combines several sources of information to
  achieve that. Despite its complexity, it should be possible to get some idea
  how completion works by experimentation, based on the overview of completion
  varieties in \secref{sec:completion-varieties}. The remaining subsections
  explain concepts around completion more systematically.

  \<^medskip>
  \<^emph>\<open>Explicit completion\<close> is triggered by the action @{action_ref
  "isabelle.complete"}, which is bound to the keyboard shortcut \<^verbatim>\<open>C+b\<close>, and
  thus overrides the jEdit default for @{action_ref "complete-word"}.

  \<^emph>\<open>Implicit completion\<close> hooks into the regular keyboard input stream of the
  editor, with some event filtering and optional delays.

  \<^medskip>
  Completion options may be configured in \<^emph>\<open>Plugin Options~/ Isabelle~/
  General~/ Completion\<close>. These are explained in further detail below, whenever
  relevant. There is also a summary of options in
  \secref{sec:completion-options}.

  The asynchronous nature of PIDE interaction means that information from the
  prover is delayed --- at least by a full round-trip of the document update
  protocol. The default options already take this into account, with a
  sufficiently long completion delay to speculate on the availability of all
  relevant information from the editor and the prover, before completing text
  immediately or producing a popup. Although there is an inherent danger of
  non-deterministic behaviour due to such real-time parameters, the general
  completion policy aims at determined results as far as possible.
\<close>


subsection \<open>Varieties of completion \label{sec:completion-varieties}\<close>

subsubsection \<open>Built-in templates\<close>

text \<open>
  Isabelle is ultimately a framework of nested sub-languages of different
  kinds and purposes. The completion mechanism supports this by the following
  built-in templates:

    \<^descr> \<^verbatim>\<open>`\<close> (single ASCII back-quote) or \<^verbatim>\<open>"\<close> (double ASCII quote) support
    \<^emph>\<open>quotations\<close> via text cartouches. There are three selections, which are
    always presented in the same order and do not depend on any context
    information. The default choice produces a template ``\<open>\<open>\<box>\<close>\<close>'', where the
    box indicates the cursor position after insertion; the other choices help
    to repair the block structure of unbalanced text cartouches.

    \<^descr> \<^verbatim>\<open>@{\<close> is completed to the template ``\<open>@{\<box>}\<close>'', where the box indicates
    the cursor position after insertion. Here it is convenient to use the
    wildcard ``\<^verbatim>\<open>__\<close>'' or a more specific name prefix to let semantic
    completion of name-space entries propose antiquotation names.

  With some practice, input of quoted sub-languages and antiquotations of
  embedded languages should work smoothly. Note that national keyboard layouts
  might cause problems with back-quote as dead key, but double quote can be
  used instead.
\<close>


subsubsection \<open>Syntax keywords\<close>

text \<open>
  Syntax completion tables are determined statically from the keywords of the
  ``outer syntax'' of the underlying edit mode: for theory files this is the
  syntax of Isar commands according to the cumulative theory imports.

  Keywords are usually plain words, which means the completion mechanism only
  inserts them directly into the text for explicit completion
  (\secref{sec:completion-input}), but produces a popup
  (\secref{sec:completion-popup}) otherwise.

  At the point where outer syntax keywords are defined, it is possible to
  specify an alternative replacement string to be inserted instead of the
  keyword itself. An empty string means to suppress the keyword altogether,
  which is occasionally useful to avoid confusion, e.g.\ the rare keyword
  @{command simproc_setup} vs.\ the frequent name-space entry \<open>simp\<close>.
\<close>


subsubsection \<open>Isabelle symbols\<close>

text \<open>
  The completion tables for Isabelle symbols (\secref{sec:symbols}) are
  determined statically from \<^file>\<open>$ISABELLE_HOME/etc/symbols\<close> and
  \<^path>\<open>$ISABELLE_HOME_USER/etc/symbols\<close> for each symbol specification as
  follows:

  \<^medskip>
  \begin{tabular}{ll}
  \<^bold>\<open>completion entry\<close> & \<^bold>\<open>example\<close> \\\hline
  literal symbol & \<^verbatim>\<open>\<forall>\<close> \\
  symbol name with backslash & \<^verbatim>\<open>\\<close>\<^verbatim>\<open>forall\<close> \\
  symbol abbreviation & \<^verbatim>\<open>ALL\<close> or \<^verbatim>\<open>!\<close> \\
  \end{tabular}
  \<^medskip>

  When inserted into the text, the above examples all produce the same Unicode
  rendering \<open>\<forall>\<close> of the underlying symbol \<^verbatim>\<open>\<forall>\<close>.

  A symbol abbreviation that is a plain word, like \<^verbatim>\<open>ALL\<close>, is treated like a
  syntax keyword. Non-word abbreviations like \<^verbatim>\<open>-->\<close> are inserted more
  aggressively, except for single-character abbreviations like \<^verbatim>\<open>!\<close> above.

  Completion via abbreviations like \<^verbatim>\<open>ALL\<close> or \<^verbatim>\<open>-->\<close> depends on the semantic
  language context (\secref{sec:completion-context}). In contrast, backslash
  sequences like \<^verbatim>\<open>\forall\<close> \<^verbatim>\<open>\<forall>\<close> are always possible, but require additional
  interaction to confirm (via popup). This is important in ambiguous
  situations, e.g.\ for Isabelle document source, which may contain formal
  symbols or informal {\LaTeX} macros. Backslash sequences also help when
  input is broken, and thus escapes its normal semantic context: e.g.\
  antiquotations or string literals in ML, which do not allow arbitrary
  backslash sequences.

  Special symbols like \<^verbatim>\<open>\<comment>\<close> or control symbols like \<^verbatim>\<open>\<^cancel>\<close>,
  \<^verbatim>\<open>\<^latex>\<close>, \<^verbatim>\<open>\<^binding>\<close> can have an argument: completing on a name
  prefix offers a template with an empty cartouche. Thus completion of \<^verbatim>\<open>\co\<close>
  or \<^verbatim>\<open>\ca\<close> allows to compose formal document comments quickly.\<^footnote>\<open>It is
  customary to put a space between \<^verbatim>\<open>\<comment>\<close> and its argument, while
  control symbols do \<^emph>\<open>not\<close> allow extra space here.\<close>
\<close>


subsubsection \<open>User-defined abbreviations\<close>

text \<open>
  The theory header syntax supports abbreviations via the \<^theory_text>\<open>abbrevs\<close> keyword
  @{cite "isabelle-isar-ref"}. This is a slight generalization of built-in
  templates and abbreviations for Isabelle symbols, as explained above.
  Examples may be found in the Isabelle sources, by searching for
  ``\<^verbatim>\<open>abbrevs\<close>'' in \<^verbatim>\<open>*.thy\<close> files.

  The \<^emph>\<open>Symbols\<close> panel shows the abbreviations that are available in the
  current theory buffer (according to its \<^theory_text>\<open>imports\<close>) in the \<^verbatim>\<open>Abbrevs\<close> tab.
\<close>


subsubsection \<open>Name-space entries\<close>

text \<open>
  This is genuine semantic completion, using information from the prover, so
  it requires some delay. A \<^emph>\<open>failed name-space lookup\<close> produces an error
  message that is annotated with a list of alternative names that are legal.
  The list of results is truncated according to the system option
  @{system_option_ref completion_limit}. The completion mechanism takes this
  into account when collecting information on the prover side.

  Already recognized names are \<^emph>\<open>not\<close> completed further, but completion may be
  extended by appending a suffix of underscores. This provokes a failed
  lookup, and another completion attempt (ignoring the underscores). For
  example, in a name space where \<^verbatim>\<open>foo\<close> and \<^verbatim>\<open>foobar\<close> are known, the input
  \<^verbatim>\<open>foo\<close> remains unchanged, but \<^verbatim>\<open>foo_\<close> may be completed to \<^verbatim>\<open>foo\<close> or
  \<^verbatim>\<open>foobar\<close>.

  The special identifier ``\<^verbatim>\<open>__\<close>'' serves as a wild-card for arbitrary
  completion: it exposes the name-space content to the completion mechanism
  (truncated according to @{system_option completion_limit}). This is
  occasionally useful to explore an unknown name-space, e.g.\ in some
  template.
\<close>


subsubsection \<open>File-system paths\<close>

text \<open>
  Depending on prover markup about file-system paths in the source text, e.g.\
  for the argument of a load command (\secref{sec:aux-files}), the completion
  mechanism explores the directory content and offers the result as completion
  popup. Relative path specifications are understood wrt.\ the \<^emph>\<open>master
  directory\<close> of the document node (\secref{sec:buffer-node}) of the enclosing
  editor buffer; this requires a proper theory, not an auxiliary file.

  A suffix of slashes may be used to continue the exploration of an already
  recognized directory name.
\<close>


subsubsection \<open>Spell-checking\<close>

text \<open>
  The spell-checker combines semantic markup from the prover (regions of plain
  words) with static dictionaries (word lists) that are known to the editor.

  Unknown words are underlined in the text, using @{system_option_ref
  spell_checker_color} (blue by default). This is not an error, but a hint to
  the user that some action may be taken. The jEdit context menu provides
  various actions, as far as applicable:

  \<^medskip>
  \begin{tabular}{l}
  @{action_ref "isabelle.complete-word"} \\
  @{action_ref "isabelle.exclude-word"} \\
  @{action_ref "isabelle.exclude-word-permanently"} \\
  @{action_ref "isabelle.include-word"} \\
  @{action_ref "isabelle.include-word-permanently"} \\
  \end{tabular}
  \<^medskip>

  Instead of the specific @{action_ref "isabelle.complete-word"}, it is also
  possible to use the generic @{action_ref "isabelle.complete"} with its
  default keyboard shortcut \<^verbatim>\<open>C+b\<close>.

  \<^medskip>
  Dictionary lookup uses some educated guesses about lower-case, upper-case,
  and capitalized words. This is oriented on common use in English, where this
  aspect is not decisive for proper spelling (in contrast to German, for
  example).
\<close>


subsection \<open>Semantic completion context \label{sec:completion-context}\<close>

text \<open>
  Completion depends on a semantic context that is provided by the prover,
  although with some delay, because at least a full PIDE protocol round-trip
  is required. Until that information becomes available in the PIDE
  document-model, the default context is given by the outer syntax of the
  editor mode (see also \secref{sec:buffer-node}).

  The semantic \<^emph>\<open>language context\<close> provides information about nested
  sub-languages of Isabelle: keywords are only completed for outer syntax, and
  antiquotations for languages that support them. Symbol abbreviations only
  work for specific sub-languages: e.g.\ ``\<^verbatim>\<open>=>\<close>'' is \<^emph>\<open>not\<close> completed in
  regular ML source, but is completed within ML strings, comments,
  antiquotations. Backslash representations of symbols like ``\<^verbatim>\<open>\foobar\<close>'' or
  ``\<^verbatim>\<open>\<foobar>\<close>'' work in any context --- after additional confirmation.

  The prover may produce \<^emph>\<open>no completion\<close> markup in exceptional situations, to
  tell that some language keywords should be excluded from further completion
  attempts. For example, ``\<^verbatim>\<open>:\<close>'' within accepted Isar syntax looses its
  meaning as abbreviation for symbol ``\<open>\<in>\<close>''.
\<close>


subsection \<open>Input events \label{sec:completion-input}\<close>

text \<open>
  Completion is triggered by certain events produced by the user, with
  optional delay after keyboard input according to @{system_option
  jedit_completion_delay}.

  \<^descr>[Explicit completion] works via action @{action_ref "isabelle.complete"}
  with keyboard shortcut \<^verbatim>\<open>C+b\<close>. This overrides the shortcut for @{action_ref
  "complete-word"} in jEdit, but it is possible to restore the original jEdit
  keyboard mapping of @{action "complete-word"} via \<^emph>\<open>Global Options~/
  Shortcuts\<close> and invent a different one for @{action "isabelle.complete"}.

  \<^descr>[Explicit spell-checker completion] works via @{action_ref
  "isabelle.complete-word"}, which is exposed in the jEdit context menu, if
  the mouse points to a word that the spell-checker can complete.

  \<^descr>[Implicit completion] works via regular keyboard input of the editor. It
  depends on further side-conditions:

    \<^enum> The system option @{system_option_ref jedit_completion} needs to be
    enabled (default).

    \<^enum> Completion of syntax keywords requires at least 3 relevant characters in
    the text.

    \<^enum> The system option @{system_option_ref jedit_completion_delay} determines
    an additional delay (0.5 by default), before opening a completion popup.
    The delay gives the prover a chance to provide semantic completion
    information, notably the context (\secref{sec:completion-context}).

    \<^enum> The system option @{system_option_ref jedit_completion_immediate}
    (enabled by default) controls whether replacement text should be inserted
    immediately without popup, regardless of @{system_option
    jedit_completion_delay}. This aggressive mode of completion is restricted
    to symbol abbreviations that are not plain words (\secref{sec:symbols}).

    \<^enum> Completion of symbol abbreviations with only one relevant character in
    the text always enforces an explicit popup, regardless of
    @{system_option_ref jedit_completion_immediate}.
\<close>


subsection \<open>Completion popup \label{sec:completion-popup}\<close>

text \<open>
  A \<^emph>\<open>completion popup\<close> is a minimally invasive GUI component over the text
  area that offers a selection of completion items to be inserted into the
  text, e.g.\ by mouse clicks. Items are sorted dynamically, according to the
  frequency of selection, with persistent history. The popup may interpret
  special keys \<^verbatim>\<open>ENTER\<close>, \<^verbatim>\<open>TAB\<close>, \<^verbatim>\<open>ESCAPE\<close>, \<^verbatim>\<open>UP\<close>, \<^verbatim>\<open>DOWN\<close>, \<^verbatim>\<open>PAGE_UP\<close>,
  \<^verbatim>\<open>PAGE_DOWN\<close>, but all other key events are passed to the underlying text
  area. This allows to ignore unwanted completions most of the time and
  continue typing quickly. Thus the popup serves as a mechanism of
  confirmation of proposed items, while the default is to continue without
  completion.

  The meaning of special keys is as follows:

  \<^medskip>
  \begin{tabular}{ll}
  \<^bold>\<open>key\<close> & \<^bold>\<open>action\<close> \\\hline
  \<^verbatim>\<open>ENTER\<close> & select completion (if @{system_option jedit_completion_select_enter}) \\
  \<^verbatim>\<open>TAB\<close> & select completion (if @{system_option jedit_completion_select_tab}) \\
  \<^verbatim>\<open>ESCAPE\<close> & dismiss popup \\
  \<^verbatim>\<open>UP\<close> & move up one item \\
  \<^verbatim>\<open>DOWN\<close> & move down one item \\
  \<^verbatim>\<open>PAGE_UP\<close> & move up one page of items \\
  \<^verbatim>\<open>PAGE_DOWN\<close> & move down one page of items \\
  \end{tabular}
  \<^medskip>

  Movement within the popup is only active for multiple items. Otherwise the
  corresponding key event retains its standard meaning within the underlying
  text area.
\<close>


subsection \<open>Insertion \label{sec:completion-insert}\<close>

text \<open>
  Completion may first propose replacements to be selected (via a popup), or
  replace text immediately in certain situations and depending on certain
  options like @{system_option jedit_completion_immediate}. In any case,
  insertion works uniformly, by imitating normal jEdit text insertion,
  depending on the state of the \<^emph>\<open>text selection\<close>. Isabelle/jEdit tries to
  accommodate the most common forms of advanced selections in jEdit, but not
  all combinations make sense. At least the following important cases are
  well-defined:

    \<^descr>[No selection.] The original is removed and the replacement inserted,
    depending on the caret position.

    \<^descr>[Rectangular selection of zero width.] This special case is treated by
    jEdit as ``tall caret'' and insertion of completion imitates its normal
    behaviour: separate copies of the replacement are inserted for each line
    of the selection.

    \<^descr>[Other rectangular selection or multiple selections.] Here the original
    is removed and the replacement is inserted for each line (or segment) of
    the selection.

  Support for multiple selections is particularly useful for \<^emph>\<open>HyperSearch\<close>:
  clicking on one of the items in the \<^emph>\<open>HyperSearch Results\<close> window makes
  jEdit select all its occurrences in the corresponding line of text. Then
  explicit completion can be invoked via \<^verbatim>\<open>C+b\<close>, e.g.\ to replace occurrences
  of \<^verbatim>\<open>-->\<close> by \<open>\<longrightarrow>\<close>.

  \<^medskip>
  Insertion works by removing and inserting pieces of text from the buffer.
  This counts as one atomic operation on the jEdit history. Thus unintended
  completions may be reverted by the regular @{action undo} action of jEdit.
  According to normal jEdit policies, the recovered text after @{action undo}
  is selected: \<^verbatim>\<open>ESCAPE\<close> is required to reset the selection and to continue
  typing more text.
\<close>


subsection \<open>Options \label{sec:completion-options}\<close>

text \<open>
  This is a summary of Isabelle/Scala system options that are relevant for
  completion. They may be configured in \<^emph>\<open>Plugin Options~/ Isabelle~/ General\<close>
  as usual.

  \<^item> @{system_option_def completion_limit} specifies the maximum number of
  items for various semantic completion operations (name-space entries etc.)

  \<^item> @{system_option_def jedit_completion} guards implicit completion via
  regular jEdit key events (\secref{sec:completion-input}): it allows to
  disable implicit completion altogether.

  \<^item> @{system_option_def jedit_completion_select_enter} and @{system_option_def
  jedit_completion_select_tab} enable keys to select a completion item from
  the popup (\secref{sec:completion-popup}). Note that a regular mouse click
  on the list of items is always possible.

  \<^item> @{system_option_def jedit_completion_context} specifies whether the
  language context provided by the prover should be used at all. Disabling
  that option makes completion less ``semantic''. Note that incomplete or
  severely broken input may cause some disagreement of the prover and the user
  about the intended language context.

  \<^item> @{system_option_def jedit_completion_delay} and @{system_option_def
  jedit_completion_immediate} determine the handling of keyboard events for
  implicit completion (\secref{sec:completion-input}).

  A @{system_option jedit_completion_delay}~\<^verbatim>\<open>> 0\<close> postpones the processing of
  key events, until after the user has stopped typing for the given time span,
  but @{system_option jedit_completion_immediate}~\<^verbatim>\<open>= true\<close> means that
  abbreviations of Isabelle symbols are handled nonetheless.

  \<^item> @{system_option_def completion_path_ignore} specifies ``glob''
  patterns to ignore in file-system path completion (separated by colons),
  e.g.\ backup files ending with tilde.

  \<^item> @{system_option_def spell_checker} is a global guard for all spell-checker
  operations: it allows to disable that mechanism altogether.

  \<^item> @{system_option_def spell_checker_dictionary} determines the current
  dictionary, taken from the colon-separated list in the settings variable
  @{setting_def JORTHO_DICTIONARIES}. There are jEdit actions to specify local
  updates to a dictionary, by including or excluding words. The result of
  permanent dictionary updates is stored in the directory
  \<^path>\<open>$ISABELLE_HOME_USER/dictionaries\<close>, in a separate file for each
  dictionary.

  \<^item> @{system_option_def spell_checker_include} specifies a comma-separated
  list of markup elements that delimit words in the source that is subject to
  spell-checking, including various forms of comments.

  \<^item> @{system_option_def spell_checker_exclude} specifies a comma-separated
  list of markup elements that disable spell-checking (e.g.\ in nested
  antiquotations).
\<close>


section \<open>Automatically tried tools \label{sec:auto-tools}\<close>

text \<open>
  Continuous document processing works asynchronously in the background.
  Visible document source that has been evaluated may get augmented by
  additional results of \<^emph>\<open>asynchronous print functions\<close>. An example for that
  is proof state output, if that is enabled in the Output panel
  (\secref{sec:output}). More heavy-weight print functions may be applied as
  well, e.g.\ to prove or disprove parts of the formal text by other means.

  Isabelle/HOL provides various automatically tried tools that operate on
  outermost goal statements (e.g.\ @{command lemma}, @{command theorem}),
  independently of the state of the current proof attempt. They work
  implicitly without any arguments. Results are output as \<^emph>\<open>information
  messages\<close>, which are indicated in the text area by blue squiggles and a blue
  information sign in the gutter (see \figref{fig:auto-tools}). The message
  content may be shown as for other output (see also \secref{sec:output}).
  Some tools produce output with \<^emph>\<open>sendback\<close> markup, which means that clicking
  on certain parts of the text inserts that into the source in the proper
  place.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{auto-tools}
  \end{center}
  \caption{Result of automatically tried tools}
  \label{fig:auto-tools}
  \end{figure}

  \<^medskip>
  The following Isabelle system options control the behavior of automatically
  tried tools (see also the jEdit dialog window \<^emph>\<open>Plugin Options~/ Isabelle~/
  General~/ Automatically tried tools\<close>):

  \<^item> @{system_option_ref auto_methods} controls automatic use of a combination
  of standard proof methods (@{method auto}, @{method simp}, @{method blast},
  etc.). This corresponds to the Isar command @{command_ref "try0"} @{cite
  "isabelle-isar-ref"}.

  The tool is disabled by default, since unparameterized invocation of
  standard proof methods often consumes substantial CPU resources without
  leading to success.

  \<^item> @{system_option_ref auto_nitpick} controls a slightly reduced version of
  @{command_ref nitpick}, which tests for counterexamples using first-order
  relational logic. See also the Nitpick manual @{cite "isabelle-nitpick"}.

  This tool is disabled by default, due to the extra overhead of invoking an
  external Java process for each attempt to disprove a subgoal.

  \<^item> @{system_option_ref auto_quickcheck} controls automatic use of
  @{command_ref quickcheck}, which tests for counterexamples using a series of
  assignments for free variables of a subgoal.

  This tool is \<^emph>\<open>enabled\<close> by default. It requires little overhead, but is a
  bit weaker than @{command nitpick}.

  \<^item> @{system_option_ref auto_sledgehammer} controls a significantly reduced
  version of @{command_ref sledgehammer}, which attempts to prove a subgoal
  using external automatic provers. See also the Sledgehammer manual @{cite
  "isabelle-sledgehammer"}.

  This tool is disabled by default, due to the relatively heavy nature of
  Sledgehammer.

  \<^item> @{system_option_ref auto_solve_direct} controls automatic use of
  @{command_ref solve_direct}, which checks whether the current subgoals can
  be solved directly by an existing theorem. This also helps to detect
  duplicate lemmas.

  This tool is \<^emph>\<open>enabled\<close> by default.


  Invocation of automatically tried tools is subject to some global policies
  of parallel execution, which may be configured as follows:

  \<^item> @{system_option_ref auto_time_limit} (default 2.0) determines the timeout
  (in seconds) for each tool execution.

  \<^item> @{system_option_ref auto_time_start} (default 1.0) determines the start
  delay (in seconds) for automatically tried tools, after the main command
  evaluation is finished.


  Each tool is submitted independently to the pool of parallel execution tasks
  in Isabelle/ML, using hardwired priorities according to its relative
  ``heaviness''. The main stages of evaluation and printing of proof states
  take precedence, but an already running tool is not canceled and may thus
  reduce reactivity of proof document processing.

  Users should experiment how the available CPU resources (number of cores)
  are best invested to get additional feedback from prover in the background,
  by using a selection of weaker or stronger tools.
\<close>


section \<open>Sledgehammer \label{sec:sledgehammer}\<close>

text \<open>
  The \<^emph>\<open>Sledgehammer\<close> panel (\figref{fig:sledgehammer}) provides a view on
  some independent execution of the Isar command @{command_ref sledgehammer},
  with process indicator (spinning wheel) and GUI elements for important
  Sledgehammer arguments and options. Any number of Sledgehammer panels may be
  active, according to the standard policies of Dockable Window Management in
  jEdit. Closing such windows also cancels the corresponding prover tasks.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{sledgehammer}
  \end{center}
  \caption{An instance of the Sledgehammer panel}
  \label{fig:sledgehammer}
  \end{figure}

  The \<^emph>\<open>Apply\<close> button attaches a fresh invocation of @{command sledgehammer}
  to the command where the cursor is pointing in the text --- this should be
  some pending proof problem. Further buttons like \<^emph>\<open>Cancel\<close> and \<^emph>\<open>Locate\<close>
  help to manage the running process.

  Results appear incrementally in the output window of the panel. Proposed
  proof snippets are marked-up as \<^emph>\<open>sendback\<close>, which means a single mouse
  click inserts the text into a suitable place of the original source. Some
  manual editing may be required nonetheless, say to remove earlier proof
  attempts.
\<close>


chapter \<open>Isabelle document preparation\<close>

text \<open>
  The ultimate purpose of Isabelle is to produce nicely rendered documents
  with the Isabelle document preparation system, which is based on {\LaTeX};
  see also @{cite "isabelle-system" and "isabelle-isar-ref"}. Isabelle/jEdit
  provides some additional support for document editing.
\<close>


section \<open>Document outline\<close>

text \<open>
  Theory sources may contain document markup commands, such as @{command_ref
  chapter}, @{command_ref section}, @{command subsection}. The Isabelle
  SideKick parser (\secref{sec:sidekick}) represents this document outline as
  structured tree view, with formal statements and proofs nested inside; see
  \figref{fig:sidekick-document}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{sidekick-document}
  \end{center}
  \caption{Isabelle document outline via SideKick tree view}
  \label{fig:sidekick-document}
  \end{figure}

  It is also possible to use text folding according to this structure, by
  adjusting \<^emph>\<open>Utilities / Buffer Options / Folding mode\<close> of jEdit. The default
  mode \<^verbatim>\<open>isabelle\<close> uses the structure of formal definitions, statements, and
  proofs. The alternative mode \<^verbatim>\<open>sidekick\<close> uses the document structure of the
  SideKick parser, as explained above.
\<close>


section \<open>Markdown structure\<close>

text \<open>
  Document text is internally structured in paragraphs and nested lists, using
  notation that is similar to Markdown\<^footnote>\<open>\<^url>\<open>https://commonmark.org\<close>\<close>. There are
  special control symbols for items of different kinds of lists, corresponding
  to \<^verbatim>\<open>itemize\<close>, \<^verbatim>\<open>enumerate\<close>, \<^verbatim>\<open>description\<close> in {\LaTeX}. This is illustrated
  in for \<^verbatim>\<open>itemize\<close> in \figref{fig:markdown-document}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{markdown-document}
  \end{center}
  \caption{Markdown structure within document text}
  \label{fig:markdown-document}
  \end{figure}

  Items take colour according to the depth of nested lists. This helps to
  explore the implicit rules for list structure interactively. There is also
  markup for individual items and paragraphs in the text: it may be explored
  via mouse hovering with \<^verbatim>\<open>CONTROL\<close> / \<^verbatim>\<open>COMMAND\<close> as usual
  (\secref{sec:tooltips-hyperlinks}).
\<close>


section \<open>Citations and Bib{\TeX} entries \label{sec:bibtex}\<close>

text \<open>
  Citations are managed by {\LaTeX} and Bib{\TeX} in \<^verbatim>\<open>.bib\<close> files. The
  Isabelle session build process and the @{tool latex} tool @{cite
  "isabelle-system"} are smart enough to assemble the result, based on the
  session directory layout.

  The document antiquotation \<open>@{cite}\<close> is described in @{cite
  "isabelle-isar-ref"}. Within the Prover IDE it provides semantic markup for
  tooltips, hyperlinks, and completion for Bib{\TeX} database entries.
  Isabelle/jEdit does \<^emph>\<open>not\<close> know about the actual Bib{\TeX} environment used
  in {\LaTeX} batch-mode, but it can take citations from those \<^verbatim>\<open>.bib\<close> files
  that happen to be open in the editor; see \figref{fig:cite-completion}.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{cite-completion}
  \end{center}
  \caption{Semantic completion of citations from open Bib{\TeX} files}
  \label{fig:cite-completion}
  \end{figure}

  Isabelle/jEdit also provides IDE support for editing \<^verbatim>\<open>.bib\<close> files
  themselves. There is syntax highlighting based on entry types (according to
  standard Bib{\TeX} styles), a context-menu to compose entries
  systematically, and a SideKick tree view of the overall content; see
  \figref{fig:bibtex-mode}. Semantic checking with errors and warnings is
  performed by the original \<^verbatim>\<open>bibtex\<close> tool using style \<^verbatim>\<open>plain\<close>: different
  Bib{\TeX} styles may produce slightly different results.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{bibtex-mode}
  \end{center}
  \caption{Bib{\TeX} mode with context menu, SideKick tree view, and
    semantic output from the \<^verbatim>\<open>bibtex\<close> tool}
  \label{fig:bibtex-mode}
  \end{figure}

  Regular document preview (\secref{sec:document-preview}) of \<^verbatim>\<open>.bib\<close> files
  approximates the usual {\LaTeX} bibliography output in HTML (using style
  \<^verbatim>\<open>unsort\<close>).
\<close>


section \<open>Document preview and printing \label{sec:document-preview}\<close>

text \<open>
  The action @{action_def isabelle.preview} opens an HTML preview of the
  current document node in the default web browser. The content is derived
  from the semantic markup produced by the prover, and thus depends on the
  status of formal processing.

  Action @{action_def isabelle.draft} is similar to @{action
  isabelle.preview}, but shows a plain-text document draft.

  Both actions show document sources in a regular Web browser, which may be
  also used to print the result in a more portable manner than the Java
  printer dialog of the jEdit @{action_ref print} action.
\<close>


chapter \<open>ML debugging within the Prover IDE\<close>

text \<open>
  Isabelle/ML is based on Poly/ML\<^footnote>\<open>\<^url>\<open>https://www.polyml.org\<close>\<close> and thus
  benefits from the source-level debugger of that implementation of Standard
  ML. The Prover IDE provides the \<^emph>\<open>Debugger\<close> dockable to connect to running
  ML threads, inspect the stack frame with local ML bindings, and evaluate ML
  expressions in a particular run-time context. A typical debugger session is
  shown in \figref{fig:ml-debugger}.

  ML debugging depends on the following pre-requisites.

    \<^enum> ML source needs to be compiled with debugging enabled. This may be
    controlled for particular chunks of ML sources using any of the subsequent
    facilities.

      \<^enum> The system option @{system_option_ref ML_debugger} as implicit state
      of the Isabelle process. It may be changed in the menu \<^emph>\<open>Plugins /
      Plugin Options / Isabelle / General\<close>. ML modules need to be reloaded and
      recompiled to pick up that option as intended.

      \<^enum> The configuration option @{attribute_ref ML_debugger}, with an
      attribute of the same name, to update a global or local context (e.g.\
      with the @{command declare} command).

      \<^enum> Commands that modify @{attribute ML_debugger} state for individual
      files: @{command_ref ML_file_debug}, @{command_ref ML_file_no_debug},
      @{command_ref SML_file_debug}, @{command_ref SML_file_no_debug}.

    The instrumentation of ML code for debugging causes minor run-time
    overhead. ML modules that implement critical system infrastructure may
    lead to deadlocks or other undefined behaviour, when put under debugger
    control!

    \<^enum> The \<^emph>\<open>Debugger\<close> panel needs to be active, otherwise the program ignores
    debugger instrumentation of the compiler and runs unmanaged. It is also
    possible to start debugging with the panel open, and later undock it, to
    let the program continue unhindered.

    \<^enum> The ML program needs to be stopped at a suitable breakpoint, which may
    be activated individually or globally as follows.

    For ML sources that have been compiled with debugger support, the IDE
    visualizes possible breakpoints in the text. A breakpoint may be toggled
    by pointing accurately with the mouse, with a right-click to activate
    jEdit's context menu and its \<^emph>\<open>Toggle Breakpoint\<close> item. Alternatively, the
    \<^emph>\<open>Break\<close> checkbox in the \<^emph>\<open>Debugger\<close> panel may be enabled to stop ML
    threads always at the next possible breakpoint.

  Note that the state of individual breakpoints \<^emph>\<open>gets lost\<close> when the
  coresponding ML source is re-compiled! This may happen unintentionally,
  e.g.\ when following hyperlinks into ML modules that have not been loaded
  into the IDE before.

  \begin{figure}[!htb]
  \begin{center}
  \includegraphics[scale=0.333]{ml-debugger}
  \end{center}
  \caption{ML debugger session}
  \label{fig:ml-debugger}
  \end{figure}

  The debugger panel (\figref{fig:ml-debugger}) shows a list of all threads
  that are presently stopped. Each thread shows a stack of all function
  invocations that lead to the current breakpoint at the top.

  It is possible to jump between stack positions freely, by clicking on this
  list. The current situation is displayed in the big output window, as a
  local ML environment with names and printed values.

  ML expressions may be evaluated in the current context by entering snippets
  of source into the text fields labeled \<open>Context\<close> and \<open>ML\<close>, and pushing the
  \<open>Eval\<close> button. By default, the source is interpreted as Isabelle/ML with the
  usual support for antiquotations (like @{command ML}, @{command ML_file}).
  Alternatively, strict Standard ML may be enforced via the \<^emph>\<open>SML\<close> checkbox
  (like @{command SML_file}).

  The context for Isabelle/ML is optional, it may evaluate to a value of type
  \<^ML_type>\<open>theory\<close>, \<^ML_type>\<open>Proof.context\<close>, or \<^ML_type>\<open>Context.generic\<close>.
  Thus the given ML expression (with its antiquotations) may be subject to the
  intended dynamic run-time context, instead of the static compile-time
  context.

  \<^medskip>
  The buttons labeled \<^emph>\<open>Continue\<close>, \<^emph>\<open>Step\<close>, \<^emph>\<open>Step over\<close>, \<^emph>\<open>Step out\<close>
  recommence execution of the program, with different policies concerning
  nested function invocations. The debugger always moves the cursor within the
  ML source to the next breakpoint position, and offers new stack frames as
  before.
\<close>


chapter \<open>Miscellaneous tools\<close>

section \<open>Timing and monitoring\<close>

text \<open>
  Managed evaluation of commands within PIDE documents includes timing
  information, which consists of elapsed (wall-clock) time, CPU time, and GC
  (garbage collection) time. Note that in a multithreaded system it is
  difficult to measure execution time precisely: elapsed time is closer to the
  real requirements of runtime resources than CPU or GC time, which are both
  subject to influences from the parallel environment that are outside the
  scope of the current command transaction.

  The \<^emph>\<open>Timing\<close> panel provides an overview of cumulative command timings for
  each document node. Commands with elapsed time below the given threshold are
  ignored in the grand total. Nodes are sorted according to their overall
  timing. For the document node that corresponds to the current buffer,
  individual command timings are shown as well. A double-click on a theory
  node or command moves the editor focus to that particular source position.

  It is also possible to reveal individual timing information via some tooltip
  for the corresponding command keyword, using the technique of mouse hovering
  with \<^verbatim>\<open>CONTROL\<close>~/ \<^verbatim>\<open>COMMAND\<close> modifier (\secref{sec:tooltips-hyperlinks}).
  Actual display of timing depends on the global option @{system_option_ref
  jedit_timing_threshold}, which can be configured in \<^emph>\<open>Plugin Options~/
  Isabelle~/ General\<close>.

  \<^medskip>
  The jEdit status line includes a monitor widget for the current heap usage
  of the Isabelle/ML process; this includes information about ongoing garbage
  collection (shown as ``ML cleanup''). A double-click opens a new instance of
  the \<^emph>\<open>Monitor\<close> panel, as explained below. There is a similar widget for the
  Java VM: a double-click opens the external \<^verbatim>\<open>jconsole\<close> application, with
  detailed information and controls for the Java process underlying
  Isabelle/Scala/jEdit.

  \<^medskip>
  The \<^emph>\<open>Monitor\<close> panel visualizes various data collections about recent
  activity of the runtime system of Isabelle/ML and Java. There are buttons to
  request a full garbage collection and sharing of live data on the ML heap.
  The display is continuously updated according to @{system_option_ref
  editor_chart_delay}. Note that the painting of the chart takes considerable
  runtime itself --- on the Java Virtual Machine that runs Isabelle/Scala, not
  Isabelle/ML.
\<close>


section \<open>Low-level output\<close>

text \<open>
  Prover output is normally shown directly in the main text area or specific
  panels like \<^emph>\<open>Output\<close> (\secref{sec:output}) or \<^emph>\<open>State\<close>
  (\secref{sec:state-output}). Beyond this, it is occasionally useful to
  inspect low-level output channels via some of the following additional
  panels:

  \<^item> \<^emph>\<open>Protocol\<close> shows internal messages between the Isabelle/Scala and
  Isabelle/ML side of the PIDE document editing protocol. Recording of
  messages starts with the first activation of the corresponding dockable
  window; earlier messages are lost.

  Display of protocol messages causes considerable slowdown, so it is
  important to undock all \<^emph>\<open>Protocol\<close> panels for production work.

  \<^item> \<^emph>\<open>Raw Output\<close> shows chunks of text from the \<^verbatim>\<open>stdout\<close> and \<^verbatim>\<open>stderr\<close>
  channels of the prover process. Recording of output starts with the first
  activation of the corresponding dockable window; earlier output is lost.

  The implicit stateful nature of physical I/O channels makes it difficult to
  relate raw output to the actual command from where it was originating.
  Parallel execution may add to the confusion. Peeking at physical process I/O
  is only the last resort to diagnose problems with tools that are not PIDE
  compliant.

  Under normal circumstances, prover output always works via managed message
  channels (corresponding to \<^ML>\<open>writeln\<close>, \<^ML>\<open>warning\<close>,
  \<^ML>\<open>Output.error_message\<close> in Isabelle/ML), which are displayed by regular
  means within the document model (\secref{sec:output}). Unhandled Isabelle/ML
  exceptions are printed by the system via \<^ML>\<open>Output.error_message\<close>.

  \<^item> \<^emph>\<open>Syslog\<close> shows system messages that might be relevant to diagnose
  problems with the startup or shutdown phase of the prover process; this also
  includes raw output on \<^verbatim>\<open>stderr\<close>. Isabelle/ML also provides an explicit
  \<^ML>\<open>Output.system_message\<close> operation, which is occasionally useful for
  diagnostic purposes within the system infrastructure itself.

  A limited amount of syslog messages are buffered, independently of the
  docking state of the \<^emph>\<open>Syslog\<close> panel. This allows to diagnose serious
  problems with Isabelle/PIDE process management, outside of the actual
  protocol layer.

  Under normal situations, such low-level system output can be ignored.
\<close>


chapter \<open>Known problems and workarounds \label{sec:problems}\<close>

text \<open>
  \<^item> \<^bold>\<open>Problem:\<close> Keyboard shortcuts \<^verbatim>\<open>C+PLUS\<close> and \<^verbatim>\<open>C+MINUS\<close> for adjusting the
  editor font size depend on platform details and national keyboards.

  \<^bold>\<open>Workaround:\<close> Rebind keys via \<^emph>\<open>Global Options~/ Shortcuts\<close>.

  \<^item> \<^bold>\<open>Problem:\<close> The macOS key sequence \<^verbatim>\<open>COMMAND+COMMA\<close> for application
  \<^emph>\<open>Preferences\<close> is in conflict with the jEdit default keyboard shortcut for
  \<^emph>\<open>Incremental Search Bar\<close> (action @{action_ref "quick-search"}).

  \<^bold>\<open>Workaround:\<close> Rebind key via \<^emph>\<open>Global Options~/ Shortcuts\<close> according to the
  national keyboard layout, e.g.\ \<^verbatim>\<open>COMMAND+SLASH\<close> on English ones.

  \<^item> \<^bold>\<open>Problem:\<close> On macOS with native Apple look-and-feel, some exotic
  national keyboards may cause a conflict of menu accelerator keys with
  regular jEdit key bindings. This leads to duplicate execution of the
  corresponding jEdit action.

  \<^bold>\<open>Workaround:\<close> Disable the native Apple menu bar via Java runtime option
  \<^verbatim>\<open>-Dapple.laf.useScreenMenuBar=false\<close>.

  \<^item> \<^bold>\<open>Problem:\<close> macOS system fonts sometimes lead to character drop-outs in
  the main text area.

  \<^bold>\<open>Workaround:\<close> Use the default \<^verbatim>\<open>Isabelle DejaVu\<close> fonts.

  \<^item> \<^bold>\<open>Problem:\<close> On macOS the Java printer dialog sometimes does not work.

  \<^bold>\<open>Workaround:\<close> Use action @{action isabelle.draft} and print via the Web
  browser.

  \<^item> \<^bold>\<open>Problem:\<close> Antialiased text rendering may show bad performance or bad
  visual quality, notably on Linux/X11.

  \<^bold>\<open>Workaround:\<close> The property \<^verbatim>\<open>view.antiAlias\<close> (via menu item Utilities /
  Global Options / Text Area / Anti Aliased smooth text) has the main impact
  on text rendering, but some related properties may also change the
  behaviour. The default is \<^verbatim>\<open>view.antiAlias=subpixel HRGB\<close>: it can be much
  faster than \<^verbatim>\<open>standard\<close>, but occasionally causes problems with odd color
  shades. An alternative is to have \<^verbatim>\<open>view.antiAlias=standard\<close> and set a Java
  system property like this:\<^footnote>\<open>See also
  \<^url>\<open>https://docs.oracle.com/javase/10/troubleshoot/java-2d-pipeline-rendering-and-properties.htm\<close>.\<close>
  @{verbatim [display] \<open>isabelle jedit -Dsun.java2d.opengl=true\<close>}

  If this works reliably, it can be made persistent via @{setting
  JEDIT_JAVA_OPTIONS} within \<^path>\<open>$ISABELLE_HOME_USER/etc/settings\<close>. For
  the Isabelle desktop ``app'', there is a corresponding file with Java
  runtime options in the main directory (name depends on the OS platform).

  \<^item> \<^bold>\<open>Problem:\<close> Some Linux/X11 input methods such as IBus tend to disrupt key
  event handling of Java/AWT/Swing.

  \<^bold>\<open>Workaround:\<close> Do not use X11 input methods. Note that environment variable
  \<^verbatim>\<open>XMODIFIERS\<close> is reset by default within Isabelle settings.

  \<^item> \<^bold>\<open>Problem:\<close> Some Linux/X11 window managers that are not ``re-parenting''
  cause problems with additional windows opened by Java. This affects either
  historic or neo-minimalistic window managers like \<^verbatim>\<open>awesome\<close> or \<^verbatim>\<open>xmonad\<close>.

  \<^bold>\<open>Workaround:\<close> Use a regular re-parenting X11 window manager.

  \<^item> \<^bold>\<open>Problem:\<close> Various forks of Linux/X11 window managers and desktop
  environments (like Gnome) disrupt the handling of menu popups and mouse
  positions of Java/AWT/Swing.

  \<^bold>\<open>Workaround:\<close> Use suitable version of Linux desktops.

  \<^item> \<^bold>\<open>Problem:\<close> Full-screen mode via jEdit action @{action_ref
  "toggle-full-screen"} (default keyboard shortcut \<^verbatim>\<open>F11\<close>) works on Windows,
  but not on macOS or various Linux/X11 window managers.

  \<^bold>\<open>Workaround:\<close> Use native full-screen control of the window manager (notably
  on macOS).

  \<^item> \<^bold>\<open>Problem:\<close> Heap space of the JVM may fill up and render the Prover IDE
  unresponsive, e.g.\ when editing big Isabelle sessions with many theories.

  \<^bold>\<open>Workaround:\<close> Increase JVM heap parameters by editing platform-specific
  files (for ``properties'' or ``options'') that are associated with the main
  app bundle.
\<close>

end
