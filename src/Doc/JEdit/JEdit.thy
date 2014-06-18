(*:wrap=hard:maxLineLen=78:*)

theory JEdit
imports Base
begin

chapter {* Introduction *}

section {* Concepts and terminology *}

text {* Isabelle/jEdit is a Prover IDE that integrates \emph{parallel
  proof checking} \cite{Wenzel:2009,Wenzel:2013:ITP} with
  \emph{asynchronous user interaction}
  \cite{Wenzel:2010,Wenzel:2012:UITP-EPTCS}, based on a
  document-oriented approach to \emph{continuous proof processing}
  \cite{Wenzel:2011:CICM,Wenzel:2012}. Many concepts and system
  components are fit together in order to make this work. The main
  building blocks are as follows.

  \begin{description}

  \item [PIDE] is a general framework for Prover IDEs based on Isabelle/Scala.
  It is built around a concept of parallel and asynchronous document
  processing, which is supported natively by the parallel proof engine that is
  implemented in Isabelle/ML. The traditional prover command loop is given up;
  instead there is direct support for editing of source text, with rich formal
  markup for GUI rendering.

  \item [Isabelle/ML] is the implementation and extension language of
  Isabelle, see also \cite{isabelle-implementation}. It is integrated
  into the logical context of Isabelle/Isar and allows to manipulate
  logical entities directly. Arbitrary add-on tools may be implemented
  for object-logics such as Isabelle/HOL.

  \item [Isabelle/Scala] is the system programming language of
  Isabelle. It extends the pure logical environment of Isabelle/ML
  towards the ``real world'' of graphical user interfaces, text
  editors, IDE frameworks, web services etc.  Special infrastructure
  allows to transfer algebraic datatypes and formatted text easily
  between ML and Scala, using asynchronous protocol commands.

  \item [jEdit] is a sophisticated text editor implemented in
  Java.\footnote{@{url "http://www.jedit.org"}} It is easily extensible
  by plugins written in languages that work on the JVM, e.g.\
  Scala\footnote{@{url "http://www.scala-lang.org"}}.

  \item [Isabelle/jEdit] is the main example application of the PIDE
  framework and the default user-interface for Isabelle. It targets
  both beginners and experts. Technically, Isabelle/jEdit combines a
  slightly modified version of the jEdit code base with a special
  plugin for Isabelle, integrated as standalone application for the
  main operating system platforms: Linux, Windows, Mac OS X.

  \end{description}

  The subtle differences of Isabelle/ML versus Standard ML,
  Isabelle/Scala versus Scala, Isabelle/jEdit versus jEdit need to be
  taken into account when discussing any of these PIDE building blocks
  in public forums, mailing lists, or even scientific publications.
  *}


section {* The Isabelle/jEdit Prover IDE *}

text {*
  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{isabelle-jedit}
  \end{center}
  \caption{The Isabelle/jEdit Prover IDE}
  \label{fig:isabelle-jedit}
  \end{figure}

  Isabelle/jEdit (\figref{fig:isabelle-jedit}) consists of some plugins for
  the jEdit text editor, while preserving its general look-and-feel as far as
  possible. The main plugin is called ``Isabelle'' and has its own menu
  \emph{Plugins~/ Isabelle} with several panels (see also
  \secref{sec:dockables}), as well as \emph{Plugins~/ Plugin Options~/
  Isabelle} (see also \secref{sec:options}).

  The options allow to specify a logic session name --- the same selector is
  accessible in the \emph{Theories} panel (\secref{sec:theories}). On
  application startup, the selected logic session image is provided
  automatically by the Isabelle build tool \cite{isabelle-sys}: if it is
  absent or outdated wrt.\ its sources, the build process updates it before
  entering the Prover IDE.  Changing the logic session within Isabelle/jEdit
  requires a restart of the application.

  \medskip The main job of the Prover IDE is to manage sources and their
  changes, taking the logical structure as a formal document into account (see
  also \secref{sec:document-model}). The editor and the prover are connected
  asynchronously in a lock-free manner. The prover is free to organize the
  checking of the formal text in parallel on multiple cores, and provides
  feedback via markup, which is rendered in the editor via colors, boxes,
  squiggly underline, hyperlinks, popup windows, icons, clickable output etc.

  Using the mouse together with the modifier key @{verbatim CONTROL} (Linux,
  Windows) or @{verbatim COMMAND} (Mac OS X) exposes additional formal content
  via tooltips and/or hyperlinks (see also \secref{sec:tooltips-hyperlinks}).
  Formal output (in popups etc.) may be explored recursively, using the same
  techniques as in the editor source buffer.

  Thus the Prover IDE gives an impression of direct access to formal content
  of the prover within the editor, but in reality only certain aspects are
  exposed, according to the possibilities of the prover and its many add-on
  tools.
*}


subsection {* Documentation *}

text {*
  The \emph{Documentation} panel of Isabelle/jEdit provides access to the
  standard Isabelle documentation: PDF files are opened by regular desktop
  operations of the underlying platform. The section ``jEdit Documentation''
  contains the original \emph{User's Guide} of this sophisticated text editor.
  The same is accessible via the @{verbatim Help} menu or @{verbatim F1}
  keyboard shortcut, using the built-in HTML viewer of Java/Swing. The latter
  also includes \emph{Frequently Asked Questions} and documentation of
  individual plugins.

  Most of the information about generic jEdit is relevant for Isabelle/jEdit
  as well, but one needs to keep in mind that defaults sometimes differ, and
  the official jEdit documentation does not know about the Isabelle plugin
  with its support for continuous checking of formal source text: jEdit is a
  plain text editor, but Isabelle/jEdit is a Prover IDE.
*}


subsection {* Plugins *}

text {* The \emph{Plugin Manager} of jEdit allows to augment editor
  functionality by JVM modules (jars) that are provided by the central
  plugin repository, which is accessible via various mirror sites.

  Connecting to the plugin server infrastructure of the jEdit project
  allows to update bundled plugins or to add further functionality.
  This needs to be done with the usual care for such an open bazaar of
  contributions. Arbitrary combinations of add-on features are apt to
  cause problems.  It is advisable to start with the default
  configuration of Isabelle/jEdit and develop some understanding how
  it is supposed to work, before loading additional plugins at a grand
  scale.

  \medskip The main \emph{Isabelle} plugin is an integral part of
  Isabelle/jEdit and needs to remain active at all times! A few additional
  plugins are bundled with Isabelle/jEdit for convenience or out of necessity,
  notably \emph{Console} with its Isabelle/Scala sub-plugin
  (\secref{sec:scala-console}) and \emph{SideKick} with some Isabelle-specific
  parsers for document tree structure (\secref{sec:sidekick}). The
  \emph{Navigator} plugin is particularly important for hyperlinks within the
  formal document-model (\secref{sec:tooltips-hyperlinks}). Further plugins
  (e.g.\ \emph{ErrorList}, \emph{Code2HTML}) are included to saturate the
  dependencies of bundled plugins, but have no particular use in
  Isabelle/jEdit. *}


subsection {* Options \label{sec:options} *}

text {* Both jEdit and Isabelle have distinctive management of
  persistent options.

  Regular jEdit options are accessible via the dialogs \emph{Utilities~/
  Global Options} or \emph{Plugins~/ Plugin Options}, with a second chance to
  flip the two within the central options dialog. Changes are stored in
  @{file_unchecked "$ISABELLE_HOME_USER/jedit/properties"} and
  @{file_unchecked "$ISABELLE_HOME_USER/jedit/keymaps"}.

  Isabelle system options are managed by Isabelle/Scala and changes are stored
  in @{file_unchecked "$ISABELLE_HOME_USER/etc/preferences"}, independently of
  other jEdit properties. See also \cite{isabelle-sys}, especially the
  coverage of sessions and command-line tools like @{tool build} or @{tool
  options}.

  Those Isabelle options that are declared as \textbf{public} are configurable
  in Isabelle/jEdit via \emph{Plugin Options~/ Isabelle~/ General}. Moreover,
  there are various options for rendering of document content, which are
  configurable via \emph{Plugin Options~/ Isabelle~/ Rendering}. Thus
  \emph{Plugin Options~/ Isabelle} in jEdit provides a view on a subset of
  Isabelle system options. Note that some of these options affect general
  parameters that are relevant outside Isabelle/jEdit as well, e.g.\
  @{system_option threads} or @{system_option parallel_proofs} for the
  Isabelle build tool \cite{isabelle-sys}, but it is possible to use the
  settings variable @{setting ISABELLE_BUILD_OPTIONS} to change defaults for
  batch builds without affecting Isabelle/jEdit.

  \medskip Options are usually loaded on startup and saved on shutdown of
  Isabelle/jEdit. Editing the machine-generated @{file_unchecked
  "$ISABELLE_HOME_USER/jedit/properties"} or @{file_unchecked
  "$ISABELLE_HOME_USER/etc/preferences"} manually while the application is
  running is likely to cause surprise due to lost update! *}


subsection {* Keymaps *}

text {* Keyboard shortcuts used to be managed as jEdit properties in
  the past, but recent versions (2013) have a separate concept of
  \emph{keymap} that is configurable via \emph{Global Options~/
  Shortcuts}.  The @{verbatim imported} keymap is derived from the
  initial environment of properties that is available at the first
  start of the editor; afterwards the keymap file takes precedence.

  This is relevant for Isabelle/jEdit due to various fine-tuning of default
  properties, and additional keyboard shortcuts for Isabelle-specific
  functionality. Users may change their keymap later, but need to copy some
  keyboard shortcuts manually (see also @{file_unchecked
  "$ISABELLE_HOME_USER/jedit/keymaps"}).
*}


section {* Command-line invocation *}

text {*
  Isabelle/jEdit is normally invoked as standalone application, with
  platform-specific executable wrappers for Linux, Windows, Mac OS X.
  Nonetheless it is occasionally useful to invoke the Prover IDE on the
  command-line, with some extra options and environment settings as explained
  below. The command-line usage of @{tool_def jedit} is as follows:
\begin{ttbox}
  Usage: isabelle jedit [OPTIONS] [FILES ...]

  Options are:
    -J OPTION    add JVM runtime option (default JEDIT_JAVA_OPTIONS)
    -b           build only
    -d DIR       include session directory
    -f           fresh build
    -j OPTION    add jEdit runtime option (default JEDIT_OPTIONS)
    -l NAME      logic image name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -s           system build mode for session image

  Start jEdit with Isabelle plugin setup and open theory FILES
  (default "\$USER_HOME/Scratch.thy").
\end{ttbox}

  The @{verbatim "-l"} option specifies the session name of the logic
  image to be used for proof processing.  Additional session root
  directories may be included via option @{verbatim "-d"} to augment
  that name space of @{tool build} \cite{isabelle-sys}.

  By default, the specified image is checked and built on demand. The
  @{verbatim "-s"} option determines where to store the result session image
  of @{tool build}. The @{verbatim "-n"} option bypasses the implicit build
  process for the selected session image.

  The @{verbatim "-m"} option specifies additional print modes for the
  prover process.  Note that the system option @{system_option_ref
  jedit_print_mode} allows to do the same persistently (e.g.\ via the
  Plugin Options dialog of Isabelle/jEdit), without requiring
  command-line invocation.

  The @{verbatim "-J"} and @{verbatim "-j"} options allow to pass
  additional low-level options to the JVM or jEdit, respectively.  The
  defaults are provided by the Isabelle settings environment
  \cite{isabelle-sys}.

  The @{verbatim "-b"} and @{verbatim "-f"} options control the self-build
  mechanism of Isabelle/jEdit. This is only relevant for building from
  sources, which also requires an auxiliary @{verbatim jedit_build} component
  from @{url "http://isabelle.in.tum.de/components"}. Note that official
  Isabelle releases already include a pre-built version of Isabelle/jEdit.
*}


chapter {* Augmented jEdit functionality *}

section {* Look-and-feel *}

text {* jEdit is a Java/AWT/Swing application with some ambition to
  support ``native'' look-and-feel on all platforms, within the limits
  of what Oracle as Java provider and major operating system
  distributors allow (see also \secref{sec:problems}).

  Isabelle/jEdit enables platform-specific look-and-feel by default as
  follows:

  \begin{description}

  \item[Linux] The platform-independent \emph{Nimbus} is used by
  default.

  \emph{GTK+} works under the side-condition that the overall GTK theme is
  selected in a Swing-friendly way.\footnote{GTK support in Java/Swing was
  once marketed aggressively by Sun, but never quite finished. Today (2013) it
  is lagging behind further development of Swing and GTK. The graphics
  rendering performance can be worse than for other Swing look-and-feels.}

  \item[Windows] Regular \emph{Windows} is used by default, but
  \emph{Windows Classic} also works.

  \item[Mac OS X] Regular \emph{Mac OS X} is used by default.

  Moreover the bundled \emph{MacOSX} plugin provides various functions that
  are expected from applications on that particular platform: quit from menu
  or dock, preferences menu, drag-and-drop of text files on the application,
  full-screen mode for main editor windows. It is advisable to have the
  \emph{MacOSX} enabled all the time on that platform.

  \end{description}

  Users may experiment with different look-and-feels, but need to keep
  in mind that this extra variance of GUI functionality is unlikely to
  work in arbitrary combinations.  The platform-independent
  \emph{Nimbus} and \emph{Metal} should always work.  The historic
  \emph{CDE/Motif} is better avoided.

  After changing the look-and-feel in \emph{Global Options~/
  Appearance}, it is advisable to restart Isabelle/jEdit in order to
  take full effect.  *}


section {* Dockable windows \label{sec:dockables} *}

text {*
  In jEdit terminology, a \emph{view} is an editor window with one or more
  \emph{text areas} that show the content of one or more \emph{buffers}. A
  regular view may be surrounded by \emph{dockable windows} that show
  additional information in arbitrary format, not just text; a \emph{plain
  view} does not allow dockables. The \emph{dockable window manager} of jEdit
  organizes these dockable windows, either as \emph{floating} windows, or
  \emph{docked} panels within one of the four margins of the view. There may
  be any number of floating instances of some dockable window, but at most one
  docked instance; jEdit actions that address \emph{the} dockable window of a
  particular kind refer to the unique docked instance.

  Dockables are used routinely in jEdit for important functionality like
  \emph{HyperSearch Results} or the \emph{File System Browser}. Plugins often
  provide a central dockable to access their key functionality, which may be
  opened by the user on demand. The Isabelle/jEdit plugin takes this approach
  to the extreme: its main plugin menu merely provides entry-points to panels
  that are managed as dockable windows. Some important panels are docked by
  default, e.g.\ \emph{Documentation}, \emph{Output}, \emph{Query}, but the
  user can change this arrangement easily.

  Compared to plain jEdit, dockable window management in Isabelle/jEdit is
  slightly augmented according to the the following principles:

  \begin{itemize}

  \item Floating windows are dependent on the main window as \emph{dialog} in
  the sense of Java/AWT/Swing. Dialog windows always stay on top of the view,
  which is particularly important in full-screen mode. The desktop environment
  of the underlying platform may impose further policies on such dependent
  dialogs, in contrast to fully independent windows, e.g.\ some window
  management functions may be missing.

  \item Keyboard focus of the main view vs.\ a dockable window is carefully
  managed according to the intended semantics, as a panel mainly for output or
  input. For example, activating the \emph{Output} (\secref{sec:output}) panel
  via the dockable window manager returns keyboard focus to the main text
  area, but for \emph{Query} (\secref{sec:query}) the focus is given to the
  main input field of that panel.

  \item Panels that provide their own text area for output have an additional
  dockable menu item \emph{Detach}. This produces an independent copy of the
  current output as a floating \emph{Info} window, which displays that content
  independently of ongoing changes of the PIDE document-model. Note that
  Isabelle/jEdit popup windows (\secref{sec:tooltips-hyperlinks}) provide a
  similar \emph{Detach} operation as an icon.

  \end{itemize}
*}


section {* Isabelle symbols \label{sec:symbols} *}

text {* Isabelle sources consist of \emph{symbols} that extend plain
  ASCII to allow infinitely many mathematical symbols within the
  formal sources.  This works without depending on particular
  encodings and varying Unicode standards
  \cite{Wenzel:2011:CICM}.\footnote{Raw Unicode characters within
  formal sources would compromise portability and reliability in the
  face of changing interpretation of special features of Unicode, such
  as Combining Characters or Bi-directional Text.}

  For the prover back-end, formal text consists of ASCII characters
  that are grouped according to some simple rules, e.g.\ as plain
  ``@{verbatim a}'' or symbolic ``@{verbatim "\<alpha>"}''.

  For the editor front-end, a certain subset of symbols is rendered
  physically via Unicode glyphs, in order to show ``@{verbatim "\<alpha>"}''
  as ``@{text "\<alpha>"}'', for example.  This symbol interpretation is
  specified by the Isabelle system distribution in @{file
  "$ISABELLE_HOME/etc/symbols"} and may be augmented by the user in
  @{file_unchecked "$ISABELLE_HOME_USER/etc/symbols"}.

  The appendix of \cite{isabelle-isar-ref} gives an overview of the
  standard interpretation of finitely many symbols from the infinite
  collection.  Uninterpreted symbols are displayed literally, e.g.\
  ``@{verbatim "\<foobar>"}''.  Overlap of Unicode characters used in
  symbol interpretation with informal ones (which might appear e.g.\
  in comments) needs to be avoided!  Raw Unicode characters within
  prover source files should be restricted to informal parts, e.g.\ to
  write text in non-latin alphabets in comments.

  \medskip \paragraph{Encoding.} Technically, the Unicode view on
  Isabelle symbols is an \emph{encoding} in jEdit (not in the
  underlying JVM) that is called @{verbatim "UTF-8-Isabelle"}.  It is
  provided by the Isabelle/jEdit plugin and enabled by default for all
  source files.  Sometimes such defaults are reset accidentally, or
  malformed UTF-8 sequences in the text force jEdit to fall back on a
  different encoding like @{verbatim "ISO-8859-15"}.  In that case,
  verbatim ``@{verbatim "\<alpha>"}'' will be shown in the text buffer
  instead of its Unicode rendering ``@{text "\<alpha>"}''.  The jEdit menu
  operation \emph{File~/ Reload with Encoding~/ UTF-8-Isabelle} helps
  to resolve such problems, potentially after repairing malformed
  parts of the text.

  \medskip \paragraph{Font.} Correct rendering via Unicode requires a
  font that contains glyphs for the corresponding codepoints.  Most
  system fonts lack that, so Isabelle/jEdit prefers its own
  application font @{verbatim IsabelleText}, which ensures that
  standard collection of Isabelle symbols are actually seen on the
  screen (or printer).

  Note that a Java/AWT/Swing application can load additional fonts
  only if they are not installed on the operating system already!
  Some old version of @{verbatim IsabelleText} that happens to be
  provided by the operating system would prevent Isabelle/jEdit to use
  its bundled version.  This could lead to missing glyphs (black
  rectangles), when the system version of @{verbatim IsabelleText} is
  older than the application version.  This problem can be avoided by
  refraining to ``install'' any version of @{verbatim IsabelleText} in
  the first place (although it is occasionally tempting to use
  the same font in other applications).

  \medskip \paragraph{Input methods.} In principle, Isabelle/jEdit
  could delegate the problem to produce Isabelle symbols in their
  Unicode rendering to the underlying operating system and its
  \emph{input methods}.  Regular jEdit also provides various ways to
  work with \emph{abbreviations} to produce certain non-ASCII
  characters.  Since none of these standard input methods work
  satisfactorily for the mathematical characters required for
  Isabelle, various specific Isabelle/jEdit mechanisms are provided.

  Here is a summary for practically relevant input methods for
  Isabelle symbols:

  \begin{enumerate}

  \item The \emph{Symbols} panel: some GUI buttons allow to insert
  certain symbols in the text buffer.  There are also tooltips to
  reveal the official Isabelle representation with some additional
  information about \emph{symbol abbreviations} (see below).

  \item Copy/paste from decoded source files: text that is rendered
  as Unicode already can be re-used to produce further text.  This
  also works between different applications, e.g.\ Isabelle/jEdit and
  some web browser or mail client, as long as the same Unicode view on
  Isabelle symbols is used.

  \item Copy/paste from prover output within Isabelle/jEdit.  The
  same principles as for text buffers apply, but note that \emph{copy}
  in secondary Isabelle/jEdit windows works via the keyboard shortcut
  @{verbatim "C+c"}, while jEdit menu actions always refer to the
  primary text area!

  \item Completion provided by Isabelle plugin (see
  \secref{sec:completion}).  Isabelle symbols have a canonical name
  and optional abbreviations.  This can be used with the text
  completion mechanism of Isabelle/jEdit, to replace a prefix of the
  actual symbol like @{verbatim "\<lambda>"}, or its name preceded by backslash
  @{verbatim "\\"}@{verbatim "lambda"}, or its ASCII abbreviation
  @{verbatim "%"} by the Unicode rendering.

  The following table is an extract of the information provided by the
  standard @{file "$ISABELLE_HOME/etc/symbols"} file:

  \medskip
  \begin{tabular}{lll}
    \textbf{symbol} & \textbf{name with backslash} & \textbf{abbreviation} \\\hline
    @{text "\<lambda>"} & @{verbatim "\\lambda"} & @{verbatim "%"} \\
    @{text "\<Rightarrow>"} & @{verbatim "\\Rightarrow"} & @{verbatim "=>"} \\
    @{text "\<Longrightarrow>"} & @{verbatim "\\Longrightarrow"} & @{verbatim "==>"} \\[0.5ex]
    @{text "\<And>"} & @{verbatim "\\And"} & @{verbatim "!!"} \\
    @{text "\<equiv>"} & @{verbatim "\\equiv"} & @{verbatim "=="} \\[0.5ex]
    @{text "\<forall>"} & @{verbatim "\\forall"} & @{verbatim "!"} \\
    @{text "\<exists>"} & @{verbatim "\\exists"} & @{verbatim "?"} \\
    @{text "\<longrightarrow>"} & @{verbatim "\\longrightarrow"} & @{verbatim "-->"} \\
    @{text "\<and>"} & @{verbatim "\\and"} & @{verbatim "&"} \\
    @{text "\<or>"} & @{verbatim "\\or"} & @{verbatim "|"} \\
    @{text "\<not>"} & @{verbatim "\\not"} & @{verbatim "~"} \\
    @{text "\<noteq>"} & @{verbatim "\\noteq"} & @{verbatim "~="} \\
    @{text "\<in>"} & @{verbatim "\\in"} & @{verbatim ":"} \\
    @{text "\<notin>"} & @{verbatim "\\notin"} & @{verbatim "~:"} \\
  \end{tabular}
  \medskip

  Note that the above abbreviations refer to the input method. The
  logical notation provides ASCII alternatives that often coincide,
  but deviate occasionally.  This occasionally causes user confusion
  with very old-fashioned Isabelle source that use ASCII replacement
  notation like @{verbatim "!"} or @{verbatim "ALL"} directly in the
  text.

  On the other hand, coincidence of symbol abbreviations with ASCII
  replacement syntax syntax helps to update old theory sources via
  explicit completion (see also @{verbatim "C+b"} explained in
  \secref{sec:completion}).

  \end{enumerate}

  \paragraph{Control symbols.} There are some special control symbols
  to modify the display style of a single symbol (without
  nesting). Control symbols may be applied to a region of selected
  text, either using the \emph{Symbols} panel or keyboard shortcuts or
  jEdit actions.  These editor operations produce a separate control
  symbol for each symbol in the text, in order to make the whole text
  appear in a certain style.

  \medskip
  \begin{tabular}{llll}
    \textbf{style} & \textbf{symbol} & \textbf{shortcut} & \textbf{action} \\\hline
    superscript & @{verbatim "\<^sup>"} & @{verbatim "C+e UP"} & @{action_ref "isabelle.control-sup"} \\
    subscript & @{verbatim "\<^sub>"} & @{verbatim "C+e DOWN"} & @{action_ref "isabelle.control-sub"} \\
    bold face & @{verbatim "\<^bold>"} & @{verbatim "C+e RIGHT"} & @{action_ref "isabelle.control-bold"} \\
    reset & & @{verbatim "C+e LEFT"} & @{action_ref "isabelle.control-reset"} \\
  \end{tabular}
  \medskip

  To produce a single control symbol, it is also possible to complete
  on @{verbatim "\\"}@{verbatim sup}, @{verbatim "\\"}@{verbatim sub},
  @{verbatim "\\"}@{verbatim bold} as for regular symbols.  *}


section {* SideKick parsers \label{sec:sidekick} *}

text {*
  The \emph{SideKick} plugin provides some general services to display buffer
  structure in a tree view.

  Isabelle/jEdit provides SideKick parsers for its main mode for theory files,
  as well as some minor modes for the @{verbatim NEWS} file (see
  \figref{fig:sidekick}), session @{verbatim ROOT} files, and system
  @{verbatim options}.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{sidekick}
  \end{center}
  \caption{The Isabelle NEWS file with SideKick tree view}
  \label{fig:sidekick}
  \end{figure}

  Moreover, the special SideKick parser @{verbatim "isabelle-markup"}
  provides access to the full (uninterpreted) markup tree of the PIDE
  document model of the current buffer.  This is occasionally useful
  for informative purposes, but the amount of displayed information
  might cause problems for large buffers, both for the human and the
  machine.
*}


section {* Scala console \label{sec:scala-console} *}

text {*
  The \emph{Console} plugin manages various shells (command interpreters),
  e.g.\ \emph{BeanShell}, which is the official jEdit scripting language, and
  the cross-platform \emph{System} shell. Thus the console provides similar
  functionality than the special Emacs buffers @{verbatim "*scratch*"} and
  @{verbatim "*shell*"}.

  Isabelle/jEdit extends the repertoire of the console by \emph{Scala}, which
  is the regular Scala toplevel loop running inside the \emph{same} JVM
  process as Isabelle/jEdit itself. This means the Scala command interpreter
  has access to the JVM name space and state of the running Prover IDE
  application: the main entry points are @{verbatim view} (the current editor
  view of jEdit) and @{verbatim PIDE} (the Isabelle/jEdit plugin object). For
  example, the Scala expression @{verbatim "PIDE.snapshot(view)"} makes a PIDE
  document snapshot of the current buffer within the current editor view.

  This helps to explore Isabelle/Scala functionality interactively. Some care
  is required to avoid interference with the internals of the running
  application, especially in production use.
*}


section {* File-system access *}

text {* File specifications in jEdit follow various formats and
  conventions according to \emph{Virtual File Systems}, which may be
  also provided by additional plugins.  This allows to access remote
  files via the @{verbatim "http:"} protocol prefix, for example.
  Isabelle/jEdit attempts to work with the file-system access model of
  jEdit as far as possible.  In particular, theory sources are passed
  directly from the editor to the prover, without indirection via
  physical files.

  Despite the flexibility of URLs in jEdit, local files are
  particularly important and are accessible without protocol prefix.
  Here the path notation is that of the Java Virtual Machine on the
  underlying platform.  On Windows the preferred form uses
  backslashes, but happens to accept forward slashes of Unix/POSIX, too.
  Further differences arise due to drive letters and network shares.

  The Java notation for files needs to be distinguished from the one of
  Isabelle, which uses POSIX notation with forward slashes on \emph{all}
  platforms.\footnote{Isabelle/ML on Windows uses Cygwin file-system access
  and Unix-style path notation.} Moreover, environment variables from the
  Isabelle process may be used freely, e.g.\ @{file
  "$ISABELLE_HOME/etc/symbols"} or @{file_unchecked "$POLYML_HOME/README"}.
  There are special shortcuts: @{file "~"} for @{file "$USER_HOME"} and @{file
  "~~"} for @{file "$ISABELLE_HOME"}.

  \medskip Since jEdit happens to support environment variables within
  file specifications as well, it is natural to use similar notation
  within the editor, e.g.\ in the file-browser.  This does not work in
  full generality, though, due to the bias of jEdit towards
  platform-specific notation and of Isabelle towards POSIX.  Moreover,
  the Isabelle settings environment is not yet active when starting
  Isabelle/jEdit via its standard application wrapper (in contrast to
  @{verbatim "isabelle jedit"} run from the command line).

  Isabelle/jEdit imitates @{verbatim "$ISABELLE_HOME"} and @{verbatim
  "$ISABELLE_HOME_USER"} within the Java process environment, in order to
  allow easy access to these important places from the editor. The file
  browser of jEdit also includes \emph{Favorites} for these two important
  locations.

  \medskip Path specifications in prover input or output usually include
  formal markup that turns it into a hyperlink (see also
  \secref{sec:tooltips-hyperlinks}). This allows to open the corresponding
  file in the text editor, independently of the path notation.

  Formally checked paths in prover input are subject to completion
  (\secref{sec:completion}): partial specifications are resolved via actual
  directory content and possible completions are offered in a popup.
*}


chapter {* Prover IDE functionality \label{sec:document-model} *}

section {* Document model \label{sec:document-model} *}

text {*
  The document model is central to the PIDE architecture: the editor and the
  prover have a common notion of structured source text with markup, which is
  produced by formal processing. The editor is responsible for edits of
  document source, as produced by the user. The prover is responsible for
  reports of document markup, as produced by its processing in the background.

  Isabelle/jEdit handles classic editor events of jEdit, in order to connect
  the physical world of the GUI (with its singleton state) to the mathematical
  world of multiple document versions (with timeless and stateless updates).
*}


subsection {* Editor buffers and document nodes \label{sec:buffer-node} *}

text {*
  As a regular text editor, jEdit maintains a collection of \emph{buffers} to
  store text files; each buffer may be associated with any number of visible
  \emph{text areas}. Buffers are subject to an \emph{edit mode} that is
  determined from the file name extension. The following modes are treated
  specifically in Isabelle/jEdit:

  \medskip
  \begin{tabular}{lll}
  \textbf{mode} & \textbf{file extension} & \textbf{content} \\\hline
  @{verbatim "isabelle"} & @{verbatim ".thy"} & theory source \\
  @{verbatim "isabelle-ml"} & @{verbatim ".ML"} & Isabelle/ML source \\
  @{verbatim "sml"} & @{verbatim ".sml"} or @{verbatim ".sig"} & Standard ML source \\
  \end{tabular}
  \medskip

  All jEdit buffers are automatically added to the PIDE document-model as
  \emph{document nodes}. The overall document structure is defined by the
  theory nodes in two dimensions:

  \begin{enumerate}

  \item via \textbf{theory imports} that are specified in the \emph{theory
  header} using concrete syntax of the @{command_ref theory} command
  \cite{isabelle-isar-ref};

  \item via \textbf{auxiliary files} that are loaded into a theory by special
  \emph{load commands}, notably @{command_ref ML_file} and @{command_ref
  SML_file} \cite{isabelle-isar-ref}.

  \end{enumerate}

  In any case, source files are managed by the PIDE infrastructure: the
  physical file-system only plays a subordinate role. The relevant version of
  source text is passed directly from the editor to the prover, via internal
  communication channels.
*}


subsection {* Theories \label{sec:theories} *}

text {*
  The \emph{Theories} panel (see also \figref{fig:output}) provides an
  overview of the status of continuous checking of theory nodes within the
  document model. Unlike batch sessions of @{tool build} \cite{isabelle-sys},
  theory nodes are identified by full path names; this allows to work with
  multiple (disjoint) Isabelle sessions simultaneously within the same editor
  session.

  Certain events to open or update editor buffers cause Isabelle/jEdit to
  resolve dependencies of theory imports. The system requests to load
  additional files into editor buffers, in order to be included in the
  document model for further checking. It is also possible to let the system
  resolve dependencies automatically, according to \emph{Plugin Options~/
  Isabelle~/ General~/ Auto Load}.

  \medskip The visible \emph{perspective} of Isabelle/jEdit is defined by the
  collective view on theory buffers via open text areas. The perspective is
  taken as a hint for document processing: the prover ensures that those parts
  of a theory where the user is looking are checked, while other parts that
  are presently not required are ignored. The perspective is changed by
  opening or closing text area windows, or scrolling within a window.

  The \emph{Theories} panel provides some further options to influence
  the process of continuous checking: it may be switched off globally
  to restrict the prover to superficial processing of command syntax.
  It is also possible to indicate theory nodes as \emph{required} for
  continuous checking: this means such nodes and all their imports are
  always processed independently of the visibility status (if
  continuous checking is enabled).  Big theory libraries that are
  marked as required can have significant impact on performance,
  though.

  \medskip Formal markup of checked theory content is turned into GUI
  rendering, based on a standard repertoire known from IDEs for programming
  languages: colors, icons, highlighting, squiggly underline, tooltips,
  hyperlinks etc. For outer syntax of Isabelle/Isar there is some traditional
  syntax-highlighting via static keyword tables and tokenization within the
  editor. In contrast, the painting of inner syntax (term language etc.)\ uses
  semantic information that is reported dynamically from the logical context.
  Thus the prover can provide additional markup to help the user to understand
  the meaning of formal text, and to produce more text with some add-on tools
  (e.g.\ information messages with \emph{sendback} markup by automated provers
  or disprovers in the background).

*}

subsection {* Auxiliary files \label{sec:aux-files} *}

text {*
  Special load commands like @{command_ref ML_file} and @{command_ref
  SML_file} \cite{isabelle-isar-ref} refer to auxiliary files within some
  theory. Conceptually, the file argument of the command extends the theory
  source by the content of the file, but its editor buffer may be loaded~/
  changed~/ saved separately. The PIDE document model propagates changes of
  auxiliary file content to the corresponding load command in the theory, to
  update and process it accordingly: changes of auxiliary file content are
  treated as changes of the corresponding load command.

  \medskip As a concession to the massive amount of ML files in Isabelle/HOL
  itself, the content of auxiliary files is only added to the PIDE
  document-model on demand, the first time when opened explicitly in the
  editor. There are further special tricks to manage markup of ML files, such
  that Isabelle/HOL may be edited conveniently in the Prover IDE on small
  machines with only 4--8\,GB of main memory. Using @{verbatim Pure} as logic
  session image, the exploration may start at the top @{file
  "$ISABELLE_HOME/src/HOL/Main.thy"} or the bottom @{file
  "$ISABELLE_HOME/src/HOL/HOL.thy"}, for example.

  Initially, before an auxiliary file is opened in the editor, the prover
  reads its content from the physical file-system. After the file is opened
  for the first time in the editor, e.g.\ by following the hyperlink
  (\secref{sec:tooltips-hyperlinks}) for the argument of its @{command
  ML_file} command, the content is taken from the jEdit buffer.

  The change of responsibility from prover to editor counts as an update of
  the document content, so subsequent theory sources need to be re-checked.
  When the buffer is closed, the responsibility remains to the editor, though:
  the file may be opened again without causing another document update.

  A file that is opened in the editor, but its theory with the load command is
  not, is presently inactive in the document model. A file that is loaded via
  multiple load commands is associated to an arbitrary one: this situation is
  morally unsupported and might lead to confusion.

  \medskip Output that refers to an auxiliary file is combined with that of
  the corresponding load command, and shown whenever the file or the command
  are active (see also \secref{sec:output}).

  Warnings, errors, and other useful markup is attached directly to the
  positions in the auxiliary file buffer, in the manner of other well-known
  IDEs. By using the load command @{command SML_file} as explained in @{file
  "$ISABELLE_HOME/src/Tools/SML/Examples.thy"}, Isabelle/jEdit may be used as
  fully-featured IDE for Standard ML, independently of theory or proof
  development: the required theory merely serves as some kind of project
  file for a collection of SML source modules.
*}


section {* Output \label{sec:output} *}

text {* Prover output consists of \emph{markup} and \emph{messages}.
  Both are directly attached to the corresponding positions in the
  original source text, and visualized in the text area, e.g.\ as text
  colours for free and bound variables, or as squiggly underline for
  warnings, errors etc.\ (see also \figref{fig:output}).  In the
  latter case, the corresponding messages are shown by hovering with
  the mouse over the highlighted text --- although in many situations
  the user should already get some clue by looking at the position of
  the text highlighting.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{output}
  \end{center}
  \caption{Multiple views on prover output: gutter area with icon,
    text area with popup, overview area, Theories panel, Output panel}
  \label{fig:output}
  \end{figure}

  The ``gutter area'' on the left-hand-side of the text area uses
  icons to provide a summary of the messages within the adjacent
  line of text.  Message priorities are used to prefer errors over
  warnings, warnings over information messages, but plain output is
  ignored.

  The ``overview area'' on the right-hand-side of the text area uses similar
  information to paint small rectangles for the overall status of the whole
  text buffer. The graphics is scaled to fit the logical buffer length into
  the given window height. Mouse clicks on the overview area position the
  cursor approximately to the corresponding line of text in the buffer.
  Repainting the overview in real-time causes problems with big theories, so
  it is restricted according to \emph{Plugin Options~/ Isabelle~/ General~/
  Text Overview Limit} (in characters).

  Another course-grained overview is provided by the \emph{Theories}
  panel, but without direct correspondence to text positions.  A
  double-click on one of the theory entries with their status overview
  opens the corresponding text buffer, without changing the cursor
  position.

  \medskip In addition, the \emph{Output} panel displays prover
  messages that correspond to a given command, within a separate
  window.

  The cursor position in the presently active text area determines the prover
  command whose cumulative message output is appended and shown in that window
  (in canonical order according to the internal execution of the command).
  There are also control elements to modify the update policy of the output
  wrt.\ continued editor movements. This is particularly useful with several
  independent instances of the \emph{Output} panel, which the Dockable Window
  Manager of jEdit can handle conveniently.

  Former users of the old TTY interaction model (e.g.\ Proof~General) might
  find a separate window for prover messages familiar, but it is important to
  understand that the main Prover IDE feedback happens elsewhere. It is
  possible to do meaningful proof editing, while using secondary output
  windows only rarely.

  The main purpose of the output window is to ``debug'' unclear
  situations by inspecting internal state of the prover.\footnote{In
  that sense, unstructured tactic scripts depend on continuous
  debugging with internal state inspection.} Consequently, some
  special messages for \emph{tracing} or \emph{proof state} only
  appear here, and are not attached to the original source.

  \medskip In any case, prover messages also contain markup that may
  be explored recursively via tooltips or hyperlinks (see
  \secref{sec:tooltips-hyperlinks}), or clicked directly to initiate
  certain actions (see \secref{sec:auto-tools} and
  \secref{sec:sledgehammer}).  *}


section {* Query \label{sec:query} *}

text {*
  The \emph{Query} panel provides various GUI forms to request extra
  information from the prover In old times the user would have issued some
  diagnostic command like @{command find_theorems} and inspected its output,
  but this is now integrated into the Prover IDE.

  A \emph{Query} window provides some input fields and buttons for a
  particular query command, with output in a dedicated text area. There are
  various query modes: \emph{Find Theorems}, \emph{Find Constants},
  \emph{Print Context}, e.g.\ see \figref{fig:query}. As usual in jEdit,
  multiple \emph{Query} windows may be active at the same time: any number of
  floating instances, but at most one docked instance (which is used by
  default).

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{query}
  \end{center}
  \caption{An instance of the Query panel}
  \label{fig:query}
  \end{figure}

  \medskip The following GUI elements are common to all query modes:
  \begin{itemize}

  \item The spinning wheel provides feedback about the status of a pending
  query wrt.\ the evaluation of its context and its own operation.

  \item The \emph{Apply} button attaches a fresh query invocation to the
  current context of the command where the cursor is pointing in the text.

  \item The \emph{Search} field allows to highlight query output according to
  some regular expression, in the notation that is commonly used on the Java
  platform. This may serve as an additional visual filter of the result.

  \item The \emph{Zoom} box controls the font size of the output area.

  \end{itemize}

  All query operations are asynchronous: there is no need to wait for the
  evaluation of the document for the query context, nor for the query
  operation itself. Query output may be detached as independent \emph{Info}
  window, using a menu operation of the dockable window manager. The printed
  result usually provides sufficient clues about the original query, with some
  hyperlink to its context (via markup of its head line).
*}


subsection {* Find theorems *}

text {*
  The \emph{Query} panel in \emph{Find Theorems} mode retrieves facts from the
  theory or proof context matching all of given criteria in the \emph{Find}
  text field. A single criterium has the following syntax:

  @{rail \<open>
    ('-'?) ('name' ':' @{syntax nameref} | 'intro' | 'elim' | 'dest' |
      'solves' | 'simp' ':' @{syntax term} | @{syntax term})
  \<close>}

  See also the Isar command @{command_ref find_theorems} in
  \cite{isabelle-isar-ref}.
*}


subsection {* Find constants *}

text {*
  The \emph{Query} panel in \emph{Find Constants} mode prints all constants
  whose type meets all of the given criteria in the \emph{Find} text field.
  A single criterium has the following syntax:

  @{rail \<open>
    ('-'?)
      ('name' ':' @{syntax nameref} | 'strict' ':' @{syntax type} | @{syntax type})
  \<close>}

  See also the Isar command @{command_ref find_consts} in
  \cite{isabelle-isar-ref}.
*}


subsection {* Print context *}

text {*
  The \emph{Query} panel in \emph{Print Context} mode prints information from
  the theory or proof context, or proof state. See also the Isar commands
  @{command_ref print_context}, @{command_ref print_cases}, @{command_ref
  print_binds}, @{command_ref print_theorems}, @{command_ref print_state} in
  \cite{isabelle-isar-ref}.
*}


section {* Tooltips and hyperlinks \label{sec:tooltips-hyperlinks} *}

text {*
  Formally processed text (prover input or output) contains rich markup
  information that can be explored further by using the @{verbatim CONTROL}
  modifier key on Linux and Windows, or @{verbatim COMMAND} on Mac OS X.
  Hovering with the mouse while the modifier is pressed reveals a
  \emph{tooltip} (grey box over the text with a yellow popup) and/or a
  \emph{hyperlink} (black rectangle over the text with change of mouse
  pointer); see also \figref{fig:tooltip}.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.5]{popup1}
  \end{center}
  \caption{Tooltip and hyperlink for some formal entity}
  \label{fig:tooltip}
  \end{figure}

  Tooltip popups use the same rendering mechanisms as the main text
  area, and further tooltips and/or hyperlinks may be exposed
  recursively by the same mechanism; see \figref{fig:nested-tooltips}.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.5]{popup2}
  \end{center}
  \caption{Nested tooltips over formal entities}
  \label{fig:nested-tooltips}
  \end{figure}

  The tooltip popup window provides some controls to \emph{close} or
  \emph{detach} the window, turning it into a separate \emph{Info}
  window managed by jEdit.  The @{verbatim ESCAPE} key closes
  \emph{all} popups, which is particularly relevant when nested
  tooltips are stacking up.

  \medskip A black rectangle in the text indicates a hyperlink that may be
  followed by a mouse click (while the @{verbatim CONTROL} or @{verbatim
  COMMAND} modifier key is still pressed). Such jumps to other text locations
  are recorded by the \emph{Navigator} plugin, which is bundled with
  Isabelle/jEdit and enabled by default, including navigation arrows in the
  main jEdit toolbar.

  Also note that the link target may be a file that is itself not
  subject to formal document processing of the editor session and thus
  prevents further exploration: the chain of hyperlinks may end in
  some source file of the underlying logic image, or within the
  Isabelle/ML bootstrap sources of Isabelle/Pure. *}


section {* Completion \label{sec:completion} *}

text {*
  Smart completion of partial input is the IDE functionality \emph{par
  excellance}. Isabelle/jEdit combines several sources of information to
  achieve that. Despite its complexity, it should be possible to get some idea
  how completion works by experimentation, based on the overview of completion
  varieties in \secref{sec:completion-varieties}. The remaining subsections
  explain concepts around completion more systematically.

  \medskip \emph{Explicit completion} is triggered by the action @{action_ref
  "isabelle.complete"}, which is bound to the keyboard shortcut @{verbatim
  "C+b"}, and thus overrides the jEdit default for @{action_ref
  "complete-word"}.

  \emph{Implicit completion} hooks into the regular keyboard input stream of
  the editor, with some event filtering and optional delays.

  \medskip Completion options may be configured in \emph{Plugin Options~/
  Isabelle~/ General~/ Completion}. These are explained in further detail
  below, whenever relevant. There is also a summary of options in
  \secref{sec:completion-options}.

  The asynchronous nature of PIDE interaction means that information from the
  prover is delayed --- at least by a full round-trip of the document update
  protocol. The default options already take this into account, with a
  sufficiently long completion delay to speculate on the availability of all
  relevant information from the editor and the prover, before completing text
  immediately or producing a popup. Although there is an inherent danger of
  non-deterministic behaviour due to such real-time parameters, the general
  completion policy aims at determined results as far as possible.
*}


subsection {* Varieties of completion \label{sec:completion-varieties} *}

subsubsection {* Built-in templates *}

text {*
  Isabelle is ultimately a framework of nested sub-languages of different
  kinds and purposes. The completion mechanism supports this by the following
  built-in templates:

  \begin{description}

  \item[] @{verbatim "`"} (single ASCII back-quote) supports \emph{quotations}
  via text cartouches. There are three selections, which are always presented
  in the same order and do not depend on any context information. The default
  choice produces a template ``@{text "\<open>\<box>\<close>"}'', where the box indicates the
  cursor position after insertion; the other choices help to repair the block
  structure of unbalanced text cartouches.

  \item[] @{verbatim "@{"} is completed to the template ``@{text "@{\<box>}"}'',
  where the box indicates the cursor position after insertion. Here it is
  convenient to use the wildcard ``@{verbatim __}'' or a more specific name
  prefix to let semantic completion of name-space entries propose
  antiquotation names.

  \end{description}

  With some practice, input of quoted sub-languages and antiquotations of
  embedded languages should work fluently. Note that national keyboard layouts
  might cause problems with back-quote as dead key: if possible, dead keys
  should be disabled.
*}


subsubsection {* Syntax keywords *}

text {*
  Syntax completion tables are determined statically from the keywords of the
  ``outer syntax'' of the underlying edit mode: for theory files this is the
  syntax of Isar commands.

  Keywords are usually plain words, which means the completion mechanism only
  inserts them directly into the text for explicit completion
  (\secref{sec:completion-input}), but produces a popup
  (\secref{sec:completion-popup}) otherwise.

  At the point where outer syntax keywords are defined, it is possible to
  specify an alternative replacement string to be inserted instead of the
  keyword itself. An empty string means to suppress the keyword altogether,
  which is occasionally useful to avoid confusion, e.g.\ the rare keyword
  @{command simproc_setup} vs.\ the frequent name-space entry @{text simp}.
*}


subsubsection {* Symbols *}

text {*
  The completion tables for Isabelle symbols (\secref{sec:symbols}) are
  determined statically from @{file "$ISABELLE_HOME/etc/symbols"} and
  @{file_unchecked "$ISABELLE_HOME_USER/etc/symbols"} for each symbol
  specification as follows:

  \medskip
  \begin{tabular}{ll}
  \textbf{completion entry} & \textbf{example} \\\hline
  literal symbol & @{verbatim "\<forall>"} \\
  symbol name with backslash & @{verbatim "\\"}@{verbatim forall} \\
  symbol abbreviation & @{verbatim "ALL"} or @{verbatim "!"} \\
  \end{tabular}
  \medskip

  When inserted into the text, the above examples all produce the same Unicode
  rendering @{text "\<forall>"} of the underlying symbol @{verbatim "\<forall>"}.

  A symbol abbreviation that is a plain word, like @{verbatim "ALL"}, is
  treated like a syntax keyword. Non-word abbreviations like @{verbatim "-->"}
  are inserted more aggressively, except for single-character abbreviations
  like @{verbatim "!"} above.

  \medskip Symbol completion depends on the semantic language context
  (\secref{sec:completion-context}), to enable or disable that aspect for a
  particular sub-language of Isabelle. For example, symbol completion is
  suppressed within document source to avoid confusion with {\LaTeX} macros
  that use similar notation.
*}


subsubsection {* Name-space entries *}

text {*
  This is genuine semantic completion, using information from the prover, so
  it requires some delay. A \emph{failed name-space lookup} produces an error
  message that is annotated with a list of alternative names that are legal.
  The list of results is truncated according to the system option
  @{system_option_ref completion_limit}. The completion mechanism takes this
  into account when collecting information on the prover side.

  Already recognized names are \emph{not} completed further, but completion
  may be extended by appending a suffix of underscores. This provokes a failed
  lookup, and another completion attempt while ignoring the underscores. For
  example, in a name space where @{verbatim "foo"} and @{verbatim "foobar"}
  are known, the input @{verbatim "foo"} remains unchanged, but @{verbatim
  "foo_"} may be completed to @{verbatim "foo"} or @{verbatim "foobar"}.

  The special identifier ``@{verbatim "__"}'' serves as a wild-card for
  arbitrary completion: it exposes the name-space content to the completion
  mechanism (truncated according to @{system_option completion_limit}). This
  is occasionally useful to explore an unknown name-space, e.g.\ in some
  template.
*}


subsubsection {* File-system paths *}

text {*
  Depending on prover markup about file-system path specifications in the
  source text, e.g.\ for the argument of a load command
  (\secref{sec:aux-files}), the completion mechanism explores the directory
  content and offers the result as completion popup. Relative path
  specifications are understood wrt.\ the \emph{master directory} of the
  document node (\secref{sec:buffer-node}) of the enclosing editor buffer;
  this requires a proper theory, not an auxiliary file.

  A suffix of slashes may be used to continue the exploration of an already
  recognized directory name.
*}


subsubsection {* Spell-checking *}

text {*
  The spell-checker combines semantic markup from the prover (regions of plain
  words) with static dictionaries (word lists) that are known to the editor.

  Unknown words are underlined in the text, using @{system_option_ref
  spell_checker_color} (blue by default). This is not an error, but a hint to
  the user that some action may be taken. The jEdit context menu provides
  various actions, as far as applicable:

  \medskip
  \begin{tabular}{l}
  @{action_ref "isabelle.complete-word"} \\
  @{action_ref "isabelle.exclude-word"} \\
  @{action_ref "isabelle.exclude-word-permanently"} \\
  @{action_ref "isabelle.include-word"} \\
  @{action_ref "isabelle.include-word-permanently"} \\
  \end{tabular}
  \medskip

  Instead of the specific @{action_ref "isabelle.complete-word"}, it is also
  possible to use the generic @{action_ref "isabelle.complete"} with its
  default keyboard shortcut @{verbatim "C+b"}.

  \medskip Dictionary lookup uses some educated guesses about lower-case,
  upper-case, and capitalized words. This is oriented on common use in
  English, where this aspect is not decisive for proper spelling, in contrast
  to German, for example.
*}


subsection {* Semantic completion context \label{sec:completion-context} *}

text {*
  Completion depends on a semantic context that is provided by the prover,
  although with some delay, because at least a full PIDE protocol round-trip
  is required. Until that information becomes available in the PIDE
  document-model, the default context is given by the outer syntax of the
  editor mode (see also \secref{sec:buffer-node}).

  The semantic \emph{language context} provides information about nested
  sub-languages of Isabelle: keywords are only completed for outer syntax,
  symbols or antiquotations for languages that support them. E.g.\ there is no
  symbol completion for ML source, but within ML strings, comments,
  antiquotations.

  The prover may produce \emph{no completion} markup in exceptional
  situations, to tell that some language keywords should be excluded from
  further completion attempts. For example, @{verbatim ":"} within accepted
  Isar syntax looses its meaning as abbreviation for symbol @{text "\<in>"}.
*}


subsection {* Input events \label{sec:completion-input} *}

text {*
  Completion is triggered by certain events produced by the user, with
  optional delay after keyboard input according to @{system_option
  jedit_completion_delay}.

  \begin{description}

  \item[Explicit completion] works via action @{action_ref
  "isabelle.complete"} with keyboard shortcut @{verbatim "C+b"}. This
  overrides the shortcut for @{action_ref "complete-word"} in jEdit, but it is
  possible to restore the original jEdit keyboard mapping of @{action
  "complete-word"} via \emph{Global Options~/ Shortcuts} and invent a
  different one for @{action "isabelle.complete"}.

  \item[Explicit spell-checker completion] works via @{action_ref
  "isabelle.complete-word"}, which is exposed in the jEdit context menu, if
  the mouse points to a word that the spell-checker can complete.

  \item[Implicit completion] works via regular keyboard input of the editor.
  It depends on further side-conditions:

  \begin{enumerate}

  \item The system option @{system_option_ref jedit_completion} needs to
  be enabled (default).

  \item Completion of syntax keywords requires at least 3 relevant
  characters in the text.

  \item The system option @{system_option_ref jedit_completion_delay}
  determines an additional delay (0.5 by default), before opening a completion
  popup.  The delay gives the prover a chance to provide semantic completion
  information, notably the context (\secref{sec:completion-context}).

  \item The system option @{system_option_ref jedit_completion_immediate}
  (disabled by default) controls whether replacement text should be inserted
  immediately without popup, regardless of @{system_option
  jedit_completion_delay}. This aggressive mode of completion is restricted to
  Isabelle symbols and their abbreviations (\secref{sec:symbols}).

  \item Completion of symbol abbreviations with only one relevant
  character in the text always enforces an explicit popup,
  regardless of @{system_option_ref jedit_completion_immediate}.

  \end{enumerate}

  \end{description}
*}


subsection {* Completion popup \label{sec:completion-popup} *}

text {*
  A \emph{completion popup} is a minimally invasive GUI component over the
  text area that offers a selection of completion items to be inserted into
  the text, e.g.\ by mouse clicks. The popup interprets special keys
  @{verbatim TAB}, @{verbatim ESCAPE}, @{verbatim UP}, @{verbatim DOWN},
  @{verbatim PAGE_UP}, @{verbatim PAGE_DOWN}, but all other key events are
  passed to the underlying text area. This allows to ignore unwanted
  completions most of the time and continue typing quickly. Thus the popup
  serves as a mechanism of confirmation of proposed items, but the default is
  to continue without completion.

  The meaning of special keys is as follows:

  \medskip
  \begin{tabular}{ll}
  \textbf{key} & \textbf{action} \\\hline
  @{verbatim "TAB"} & select completion \\
  @{verbatim "ESCAPE"} & dismiss popup \\
  @{verbatim "UP"} & move up one item \\
  @{verbatim "DOWN"} & move down one item \\
  @{verbatim "PAGE_UP"} & move up one page of items \\
  @{verbatim "PAGE_DOWN"} & move down one page of items \\
  \end{tabular}
  \medskip

  Movement within the popup is only active for multiple items.
  Otherwise the corresponding key event retains its standard meaning
  within the underlying text area.
*}


subsection {* Insertion \label{sec:completion-insert} *}

text {*
  Completion may first propose replacements to be selected (via a popup), or
  replace text immediately in certain situations and depending on certain
  options like @{system_option jedit_completion_immediate}. In any case,
  insertion works uniformly, by imitating normal text insertion to some
  extent. The precise behaviour depends on the state of the \emph{text
  selection} of jEdit. Isabelle/jEdit tries to accommodate the most common
  forms of advanced selections in jEdit, but not all combinations make sense.
  At least the following important cases are well-defined.

  \begin{description}

  \item[No selection.] The original is removed and the replacement inserted,
  depending on the caret position.

  \item[Rectangular selection zero width.] This special case is treated by
  jEdit as ``tall caret'' and insertion of completion imitates its normal
  behaviour: separate copies of the replacement are inserted for each line of
  the selection.

  \item[Other rectangular selection or multiple selections.] Here the original
  is removed and the replacement is inserted for each line (or segment) of the
  selection.

  \end{description}

  Support for multiple selections is particularly useful for
  \emph{HyperSearch}: clicking on one of the items in the \emph{HyperSearch
  Results} window makes jEdit select all its occurrences in the corresponding
  line of text. Then explicit completion can be invoked via @{verbatim "C+b"},
  for example to replace occurrences of @{verbatim "-->"} by @{text "\<longrightarrow>"}.

  \medskip Insertion works by removing and inserting pieces of text from the
  buffer. This counts as one atomic operation on the jEdit history. Thus
  unintended completions may be reverted by the regular @{action undo} action
  of jEdit. According to normal jEdit policies, the recovered text after
  @{action undo} is selected: @{verbatim ESCAPE} is required to reset the
  selection and to continue typing more text.
*}


subsection {* Options \label{sec:completion-options} *}

text {*
  This is a summary of Isabelle/Scala system options that are relevant for
  completion. They may be configured in \emph{Plugin Options~/ Isabelle~/
  General} as usual.

  \begin{itemize}

  \item @{system_option_def completion_limit} specifies the maximum number of
  name-space entries exposed in semantic completion by the prover.

  \item @{system_option_def jedit_completion} guards implicit completion via
  regular jEdit key events (\secref{sec:completion-input}): it allows to
  disable implicit completion altogether.

  \item @{system_option_def jedit_completion_context} specifies whether the
  language context provided by the prover should be used at all. Disabling
  that option makes completion less ``semantic''. Note that incomplete or
  severely broken input may cause some disagreement of the prover and the user
  about the intended language context.

  \item @{system_option_def jedit_completion_delay} and @{system_option_def
  jedit_completion_immediate} determine the handling of keyboard events for
  implicit completion (\secref{sec:completion-input}).

  A @{system_option jedit_completion_delay}~@{verbatim "> 0"} postpones the
  processing of key events, until after the user has stopped typing for the
  given time span, but @{system_option jedit_completion_immediate}~@{verbatim
  "= true"} means that abbreviations of Isabelle symbols are handled
  nonetheless.

  \item @{system_option_def jedit_completion_path_ignore} specifies ``glob''
  patterns to ignore in file-system path completion (separated by colons),
  e.g.\ backup files ending with tilde.

  \item @{system_option_def spell_checker} is a global guard for all
  spell-checker operations: it allows to disable that mechanism altogether.

  \item @{system_option_def spell_checker_dictionary} determines the current
  dictionary, taken from the colon-separated list in the settings variable
  @{setting_def JORTHO_DICTIONARIES}. There are jEdit actions to specify local
  updates to a dictionary, by including or excluding words. The result of
  permanent dictionary updates is stored in the directory @{file_unchecked
  "$ISABELLE_HOME_USER/dictionaries"}, in a separate file for each dictionary.

  \item @{system_option_def spell_checker_elements} specifies a
  comma-separated list of markup elements that delimit words in the source
  that is subject to spell-checking, including various forms of comments.

  \end{itemize}
*}


section {* Automatically tried tools \label{sec:auto-tools} *}

text {*
  Continuous document processing works asynchronously in the background.
  Visible document source that has been evaluated may get augmented by
  additional results of \emph{asynchronous print functions}. The canonical
  example is proof state output, which is always enabled. More heavy-weight
  print functions may be applied, in order to prove or disprove parts of the
  formal text by other means.

  Isabelle/HOL provides various automatically tried tools that operate
  on outermost goal statements (e.g.\ @{command lemma}, @{command
  theorem}), independently of the state of the current proof attempt.
  They work implicitly without any arguments.  Results are output as
  \emph{information messages}, which are indicated in the text area by
  blue squiggles and a blue information sign in the gutter (see
  \figref{fig:auto-tools}).  The message content may be shown as for
  other output (see also \secref{sec:output}).  Some tools
  produce output with \emph{sendback} markup, which means that
  clicking on certain parts of the output inserts that text into the
  source in the proper place.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{auto-tools}
  \end{center}
  \caption{Result of automatically tried tools}
  \label{fig:auto-tools}
  \end{figure}

  \medskip The following Isabelle system options control the behavior
  of automatically tried tools (see also the jEdit dialog window
  \emph{Plugin Options~/ Isabelle~/ General~/ Automatically tried
  tools}):

  \begin{itemize}

  \item @{system_option_ref auto_methods} controls automatic use of a
  combination of standard proof methods (@{method auto}, @{method
  simp}, @{method blast}, etc.).  This corresponds to the Isar command
  @{command_ref "try0"}.

  The tool is disabled by default, since unparameterized invocation of
  standard proof methods often consumes substantial CPU resources
  without leading to success.

  \item @{system_option_ref auto_nitpick} controls a slightly reduced
  version of @{command_ref nitpick}, which tests for counterexamples using
  first-order relational logic. See also the Nitpick manual
  \cite{isabelle-nitpick}.

  This tool is disabled by default, due to the extra overhead of
  invoking an external Java process for each attempt to disprove a
  subgoal.

  \item @{system_option_ref auto_quickcheck} controls automatic use of
  @{command_ref quickcheck}, which tests for counterexamples using a
  series of assignments for free variables of a subgoal.

  This tool is \emph{enabled} by default.  It requires little
  overhead, but is a bit weaker than @{command nitpick}.

  \item @{system_option_ref auto_sledgehammer} controls a significantly
  reduced version of @{command_ref sledgehammer}, which attempts to prove
  a subgoal using external automatic provers. See also the
  Sledgehammer manual \cite{isabelle-sledgehammer}.

  This tool is disabled by default, due to the relatively heavy nature
  of Sledgehammer.

  \item @{system_option_ref auto_solve_direct} controls automatic use of
  @{command_ref solve_direct}, which checks whether the current subgoals
  can be solved directly by an existing theorem.  This also helps to
  detect duplicate lemmas.

  This tool is \emph{enabled} by default.

  \end{itemize}

  Invocation of automatically tried tools is subject to some global
  policies of parallel execution, which may be configured as follows:

  \begin{itemize}

  \item @{system_option_ref auto_time_limit} (default 2.0) determines the
  timeout (in seconds) for each tool execution.

  \item @{system_option_ref auto_time_start} (default 1.0) determines the
  start delay (in seconds) for automatically tried tools, after the
  main command evaluation is finished.

  \end{itemize}

  Each tool is submitted independently to the pool of parallel
  execution tasks in Isabelle/ML, using hardwired priorities according
  to its relative ``heaviness''.  The main stages of evaluation and
  printing of proof states take precedence, but an already running
  tool is not canceled and may thus reduce reactivity of proof
  document processing.

  Users should experiment how the available CPU resources (number of
  cores) are best invested to get additional feedback from prover in
  the background, by using a selection of weaker or stronger tools.
*}


section {* Sledgehammer \label{sec:sledgehammer} *}

text {* The \emph{Sledgehammer} panel (\figref{fig:sledgehammer})
  provides a view on some independent execution of the Isar command
  @{command_ref sledgehammer}, with process indicator (spinning wheel) and
  GUI elements for important Sledgehammer arguments and options.  Any
  number of Sledgehammer panels may be active, according to the
  standard policies of Dockable Window Management in jEdit.  Closing
  such windows also cancels the corresponding prover tasks.

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[scale=0.333]{sledgehammer}
  \end{center}
  \caption{An instance of the Sledgehammer panel}
  \label{fig:sledgehammer}
  \end{figure}

  The \emph{Apply} button attaches a fresh invocation of @{command
  sledgehammer} to the command where the cursor is pointing in the
  text --- this should be some pending proof problem.  Further buttons
  like \emph{Cancel} and \emph{Locate} help to manage the running
  process.

  Results appear incrementally in the output window of the panel.
  Proposed proof snippets are marked-up as \emph{sendback}, which
  means a single mouse click inserts the text into a suitable place of
  the original source.  Some manual editing may be required
  nonetheless, say to remove earlier proof attempts. *}


chapter {* Miscellaneous tools *}

section {* Timing *}

text {* Managed evaluation of commands within PIDE documents includes
  timing information, which consists of elapsed (wall-clock) time, CPU
  time, and GC (garbage collection) time.  Note that in a
  multithreaded system it is difficult to measure execution time
  precisely: elapsed time is closer to the real requirements of
  runtime resources than CPU or GC time, which are both subject to
  influences from the parallel environment that are outside the scope
  of the current command transaction.

  The \emph{Timing} panel provides an overview of cumulative command
  timings for each document node.  Commands with elapsed time below
  the given threshold are ignored in the grand total.  Nodes are
  sorted according to their overall timing.  For the document node
  that corresponds to the current buffer, individual command timings
  are shown as well.  A double-click on a theory node or command moves
  the editor focus to that particular source position.

  It is also possible to reveal individual timing information via some
  tooltip for the corresponding command keyword, using the technique
  of mouse hovering with @{verbatim CONTROL}/@{verbatim COMMAND}
  modifier key as explained in \secref{sec:tooltips-hyperlinks}.
  Actual display of timing depends on the global option
  @{system_option_ref jedit_timing_threshold}, which can be configured in
  "Plugin Options~/ Isabelle~/ General".

  \medskip The \emph{Monitor} panel provides a general impression of
  recent activity of the farm of worker threads in Isabelle/ML.  Its
  display is continuously updated according to @{system_option_ref
  editor_chart_delay}.  Note that the painting of the chart takes
  considerable runtime itself --- on the Java Virtual Machine that
  runs Isabelle/Scala, not Isabelle/ML.  Internally, the
  Isabelle/Scala module @{verbatim isabelle.ML_Statistics} provides
  further access to statistics of Isabelle/ML.  *}


section {* Low-level output *}

text {* Prover output is normally shown directly in the main text area
  or secondary \emph{Output} panels, as explained in
  \secref{sec:output}.

  Beyond this, it is occasionally useful to inspect low-level output
  channels via some of the following additional panels:

  \begin{itemize}

  \item \emph{Protocol} shows internal messages between the
  Isabelle/Scala and Isabelle/ML side of the PIDE editing protocol.
  Recording of messages starts with the first activation of the
  corresponding dockable window; earlier messages are lost.

  Actual display of protocol messages causes considerable slowdown, so
  it is important to undock all \emph{Protocol} panels for production
  work.

  \item \emph{Raw Output} shows chunks of text from the @{verbatim
  stdout} and @{verbatim stderr} channels of the prover process.
  Recording of output starts with the first activation of the
  corresponding dockable window; earlier output is lost.

  The implicit stateful nature of physical I/O channels makes it
  difficult to relate raw output to the actual command from where it
  was originating.  Parallel execution may add to the confusion.
  Peeking at physical process I/O is only the last resort to diagnose
  problems with tools that are not PIDE compliant.

  Under normal circumstances, prover output always works via managed message
  channels (corresponding to @{ML writeln}, @{ML warning}, @{ML
  Output.error_message} etc.\ in Isabelle/ML), which are displayed by regular
  means within the document model (\secref{sec:output}).

  \item \emph{Syslog} shows system messages that might be relevant to
  diagnose problems with the startup or shutdown phase of the prover
  process; this also includes raw output on @{verbatim stderr}.

  A limited amount of syslog messages are buffered, independently of
  the docking state of the \emph{Syslog} panel.  This allows to
  diagnose serious problems with Isabelle/PIDE process management,
  outside of the actual protocol layer.

  Under normal situations, such low-level system output can be
  ignored.

  \end{itemize}
*}


chapter {* Known problems and workarounds \label{sec:problems} *}

text {*
  \begin{itemize}

  \item \textbf{Problem:} Odd behavior of some diagnostic commands with
  global side-effects, like writing a physical file.

  \textbf{Workaround:} Copy/paste complete command text from
  elsewhere, or disable continuous checking temporarily.

  \item \textbf{Problem:} No way to delete document nodes from the overall
  collection of theories.

  \textbf{Workaround:} Ignore unused files.  Restart whole
  Isabelle/jEdit session in worst-case situation.

  \item \textbf{Problem:} Keyboard shortcuts @{verbatim "C+PLUS"} and
  @{verbatim "C+MINUS"} for adjusting the editor font size depend on
  platform details and national keyboards.

  \textbf{Workaround:} Rebind keys via \emph{Global Options~/
  Shortcuts}.

  \item \textbf{Problem:} The Mac OS X key sequence @{verbatim
  "COMMAND+COMMA"} for application \emph{Preferences} is in conflict with the
  jEdit default keyboard shortcut for \emph{Incremental Search Bar} (action
  @{action_ref "quick-search"}).

  \textbf{Workaround:} Rebind key via \emph{Global Options~/
  Shortcuts} according to national keyboard, e.g.\ @{verbatim
  "COMMAND+SLASH"} on English ones.

  \item \textbf{Problem:} Mac OS X system fonts sometimes lead to
  character drop-outs in the main text area.

  \textbf{Workaround:} Use the default @{verbatim IsabelleText} font.
  (Do not install that font on the system.)

  \item \textbf{Problem:} Some Linux/X11 input methods such as IBus
  tend to disrupt key event handling of Java/AWT/Swing.

  \textbf{Workaround:} Do not use input methods, reset the environment
  variable @{verbatim XMODIFIERS} within Isabelle settings (default in
  Isabelle2013-2).

  \item \textbf{Problem:} Some Linux/X11 window managers that are
  not ``re-parenting'' cause problems with additional windows opened
  by Java. This affects either historic or neo-minimalistic window
  managers like @{verbatim awesome} or @{verbatim xmonad}.

  \textbf{Workaround:} Use a regular re-parenting window manager.

  \item \textbf{Problem:} Recent forks of Linux/X11 window managers
  and desktop environments (variants of Gnome) disrupt the handling of
  menu popups and mouse positions of Java/AWT/Swing.

  \textbf{Workaround:} Use mainstream versions of Linux desktops.

  \item \textbf{Problem:} Full-screen mode via jEdit action @{action_ref
  "toggle-full-screen"} (default keyboard shortcut @{verbatim F11}) works on
  Windows, but not on Mac OS X or various Linux/X11 window managers.

  \textbf{Workaround:} Use native full-screen control of the window
  manager (notably on Mac OS X).

  \end{itemize}
*}

end