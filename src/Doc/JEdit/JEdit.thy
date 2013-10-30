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

  \item [PIDE] is a general framework for Prover IDEs based on
  Isabelle/Scala. It is built around a concept of parallel and
  asynchronous document processing, which is supported natively by the
  parallel proof engine that is implemented in Isabelle/ML. The prover
  discontinues the traditional TTY-based command loop, and supports
  direct editing of formal source text with rich formal markup for GUI
  rendering.

  \item [Isabelle/ML] is the implementation and extension language of
  Isabelle, see also \cite{isabelle-implementation}. It is integrated
  into the logical context of Isabelle/Isar and allows to manipulate
  logical entities directly. Arbitrary add-on tools may be implemented
  for object-logics such as Isabelle/HOL.

  \item [Isabelle/Scala] is the system programming language of
  Isabelle. It extends the pure logical environment of Isabelle/ML
  towards the ``real world'' of graphical user interfaces, text
  editors, IDE frameworks, web services etc.  Special infrastructure
  allows to transfer algebraic datatype values and formatted text
  easily between ML and Scala, using asynchronous protocol commands.

  \item [jEdit] is a sophisticated text editor implemented in
  Java.\footnote{\url{http://www.jedit.org}} It is easily extensible
  by plugins written in languages that work on the JVM, e.g.\
  Scala\footnote{\url{http://www.scala-lang.org/}}.

  \item [Isabelle/jEdit] is the main example application of the PIDE
  framework and the default user-interface for Isabelle. It targets
  both beginners and experts. Technically, Isabelle/jEdit combines a
  slightly modified version of the official jEdit code base with a
  special plugin for Isabelle, integrated as standalone application
  for the main operating system platforms: Linux, Windows, Mac OS X.

  \end{description}

  The subtle differences of Isabelle/ML versus Standard ML,
  Isabelle/Scala versus Scala, Isabelle/jEdit versus jEdit need to be
  taken into account when discussing any of these PIDE building blocks
  in public forums, mailing lists, or even scientific publications.
  *}


section {* The Isabelle/jEdit Prover IDE *}

text {*
  \begin{figure}[htbp]
  \begin{center}
  \includegraphics[width=\textwidth]{isabelle-jedit}
  \end{center}
  \caption{The Isabelle/jEdit Prover IDE}
  \end{figure}

  Isabelle/jEdit consists of some plugins for the well-known jEdit
  text editor \url{http://www.jedit.org}, according to the following
  principles.

  \begin{itemize}

  \item The original jEdit look-and-feel is generally preserved,
  although some default properties are changed to accommodate Isabelle
  (e.g.\ the text area font).

  \item Formal Isabelle/Isar text is checked asynchronously while
  editing.  The user is in full command of the editor, and the prover
  refrains from locking portions of the buffer.

  \item Prover feedback works via colors, boxes, squiggly underline,
  hyperlinks, popup windows, icons, clickable output --- all based on
  semantic markup produced by Isabelle in the background.

  \item Using the mouse together with the modifier key @{verbatim
  CONTROL} (Linux, Windows) or @{verbatim COMMAND} (Mac OS X) exposes
  additional formal content via tooltips and/or hyperlinks.

  \item Formal output (in popups etc.) may be explored recursively,
  using the same techniques as in the editor source buffer.

  \item Additional panels (e.g.\ \emph{Output}, \emph{Symbols}) are
  organized by the Dockable Window Manager of jEdit, which also allows
  multiple floating instances of each window class.

  \item The prover process and source files are managed on the editor
  side.  The prover operates on timeless and stateless document
  content as provided via Isabelle/Scala.

  \item Plugin options of jEdit (for the \emph{Isabelle} plugin) give
  access to a selection of Isabelle/Scala options and its persistent
  preferences, usually with immediate effect on the prover back-end or
  editor front-end.

  \item The logic image of the prover session may be specified within
  Isabelle/jEdit.  The new image is provided automatically by the
  Isabelle build tool after restart of the application.

  \end{itemize}
*}


subsection {* Documentation *}

text {* Regular jEdit documentation is accessible via its @{verbatim
  Help} menu or @{verbatim F1} keyboard shortcut. This includes a full
  \emph{User's Guide} and \emph{Frequently Asked Questions} for this
  sophisticated text editor.

  Most of this information about jEdit is relevant for Isabelle/jEdit
  as well, but one needs to keep in mind that defaults sometimes
  differ, and the official jEdit documentation does not know about the
  Isabelle plugin with its special support for theory editing.
*}


subsection {* Plugins *}

text {* The \emph{Plugin Manager} of jEdit allows to augment editor
  functionality by JVM modules (jars) that are provided by the central
  plugin repository, which is accessible by various mirror sites.

  Connecting to the plugin server infrastructure of the jEdit project
  allows to update bundled plugins or to add further functionality.
  This needs to be done with the usual care for such an open bazaar of
  contributions. Arbitrary combinations of add-on features are apt to
  cause problems.  It is advisable to start with the default
  configuration of Isabelle/jEdit and develop some understanding how
  it is supposed to work, before loading additional plugins at a grand
  scale.

  \medskip The main \emph{Isabelle} plugin is an integral part of
  Isabelle/jEdit and needs to remain active at all times! A few
  additional plugins are bundled with Isabelle/jEdit for convenience
  or out of necessity, notably \emph{Console} with its Isabelle/Scala
  sub-plugin and \emph{SideKick} with some Isabelle-specific parsers
  for document tree structure.  The \emph{ErrorList} plugin is
  required by \emph{SideKick}, but not used specifically in
  Isabelle/jEdit. *}


subsection {* Options *}

text {* Both jEdit and Isabelle have distinctive management of
  persistent options.

  Regular jEdit options are accessible via the dialogs for
  \emph{Global Options} and \emph{Plugin Options}.  Changed properties
  are stored eventually in @{verbatim
  "$ISABELLE_HOME_USER/jedit/properties"}.  In contrast, Isabelle
  system options are managed by Isabelle/Scala and changes stored in
  @{verbatim "$ISABELLE_HOME_USER/etc/preferences"}, independently of
  the jEdit properties.  See also \cite{isabelle-sys}, especially the
  coverage of sessions and command-line tools like @{tool build} or
  @{tool options}.

  Those Isabelle options that are declared as \textbf{public} are
  configurable in jEdit via \emph{Plugin Options / Isabelle /
  General}.  Moreover, there are various options for rendering of
  document content, which are configurable via \emph{Plugin Options /
  Isabelle / Rendering}.  Thus \emph{Plugin Options / Isabelle} in
  jEdit provides a view on certain Isabelle options.  Note that some
  of these options affect general parameters that are relevant outside
  Isabelle/jEdit as well, e.g.\ @{system_option threads} or
  @{system_option parallel_proofs} for the Isabelle build tool
  \cite{isabelle-sys}.

  \medskip All options are loaded on startup and saved on shutdown of
  Isabelle/jEdit.  Editing the machine-generated files @{verbatim
  "$ISABELLE_HOME_USER/jedit/properties"} or @{verbatim
  "$ISABELLE_HOME_USER/etc/preferences"} manually while the
  application is running is likely to cause surprise due to lost
  update!  *}


subsection {* Keymaps *}

text {* Keyboard shortcuts used to be managed as jEdit properties in
  the past, but recent versions (2013) have a separate concept of
  \emph{keymap} that is configurable via \emph{Global Options /
  Shortcuts}.  The @{verbatim imported} keymap is derived from the
  initial environment of properties that is available at the first
  start of the editor; afterwards the keymap file takes precedence.

  This is relevant for Isabelle/jEdit due to various fine-tuning of
  default properties, and additional keyboard shortcuts for Isabelle
  specific functionality. Users may change their keymap, but need to
  copy Isabelle-specific key bindings manually.  *}


subsection {* Look-and-feel *}

text {* jEdit is a Java/AWT/Swing application with some ambition to
  support ``native'' look-and-feel on all platforms, within the limits
  of what Oracle as Java provider and major operating system
  distributors allow (see also \secref{sec:problems}).

  Isabelle/jEdit enables platform-specific look-and-feel by default as
  follows:

  \begin{description}

  \item[Linux] The platform-independent \emph{Nimbus} is used by
  default, but the classic \emph{Metal} also works.  \emph{GTK+} works
  under the side-condition that the overall GTK theme is selected in a
  Swing-friendly way.\footnote{GTK support in Java/Swing was once
  marketed aggressively by Sun, but never quite finished, and is today
  (2013) lagging a bit behind further development of Swing and GTK.}

  \item[Windows] Regular \emph{Windows} is used by default, but
  platform-independent \emph{Nimbus} and \emph{Metal} also work.

  \item[Mac OS X] Regular \emph{Mac OS X} is used by default, but
  platform-independent \emph{Nimbus} and \emph{Metal} also work.
  Moreover the bundled \emph{MacOSX} plugin provides various functions
  that are expected from applications on that particular platform:
  quit from menu or dock, preferences menu, drag-and-drop of text
  files on the application, full-screen mode for main editor windows
  etc.

  \end{description}

  Users may experiment with different look-and-feels, but need to keep
  in mind that this extra variance of GUI functionality is unlikely to
  work in arbitrary combinations.  The historic \emph{CDE/Motif} is
  better avoided.  After changing the look-and-feel in \emph{Global
  Options / Appearance}, it is advisable to restart Isabelle/jEdit in
  order to take full effect.  *}


subsection {* File-system access *}

text {* File specifications in jEdit follow various formats and
  conventions according to \emph{Virtual File Systems}, which may be
  also provided by additional plugins.  This allows to access remote
  files via the @{verbatim "http:"} protocol prefix, for example.
  Isabelle/jEdit attempts to work with the file-system access model of
  jEdit as far as possible.  In particular, theory sources are passed
  directly from the editor to the prover, without indirection via
  files.

  Despite the flexibility of URLs in jEdit, local files are
  particularly important and are accessible without protocol prefix.
  Here the path notation is that of the Java Virtual Machine on the
  underlying platform.  On Windows the preferred form uses
  backslashes, but happens to accept Unix/POSIX forward slashes, too.
  Further differences arise due to drive letters and network shares.

  The Java notation for files needs to be distinguished from the one
  of Isabelle, which uses POSIX notation with forward slashes on
  \emph{all} platforms.\footnote{Isabelle on Windows uses Cygwin
  file-system access.}  Moreover, environment variables from the
  Isabelle process may be used freely, e.g.\ @{file
  "$ISABELLE_HOME/etc/symbols"} or @{file
  "$ISABELLE_JDK_HOME/README.html"}.  There are special shortcuts:
  @{verbatim "~"} for @{file "$USER_HOME"}, and @{verbatim "~~"} for
  @{file "$ISABELLE_HOME"}.

  \medskip Since jEdit happens to support environment variables within
  file specifications as well, it is natural to use similar notation
  within the editor, e.g.\ in the file-browser.  This does not work in
  full generality, though, due to the bias of jEdit towards
  platform-specific notation and of Isabelle towards POSIX.  Moreover,
  the Isabelle settings environment is not yet active when starting
  Isabelle/jEdit via its standard application wrapper (in contrast to
  @{verbatim "isabelle jedit"} run from the command line).

  For convenience, Isabelle/jEdit imitates at least @{verbatim
  "$ISABELLE_HOME"} and @{verbatim "$ISABELLE_HOME_USER"} within the
  Java process environment, in order to allow easy access to these
  important places from the editor.

  Moreover note that path specifications in prover input or output
  usually include formal markup that turns it into a hyperlink (see
  also \secref{sec:tooltips-hyperlinks}).  This allows to open the
  corresponding file in the text editor, independently of the path
  notation.  *}


chapter {* Prover IDE functionality *}

section {* Text buffers and theories *}

text {* As regular text editor, jEdit maintains a collection of open
  \emph{text buffers} to store source files; each buffer may be
  associated with any number of visible \emph{text areas}.  Buffers
  are subject to an \emph{edit mode} that is determined from the file
  type.  Files with extension \texttt{.thy} are assigned to the mode
  \emph{isabelle} and treated specifically.

  \medskip Isabelle theory files are automatically added to the formal
  document model of Isabelle/Scala, which maintains a family of
  versions of all sources for the prover.  The \emph{Theories} panel
  provides an overview of the status of continuous checking of theory
  sources.  Unlike batch sessions \cite{isabelle-sys}, theory nodes
  are identified by full path names; this allows to work with multiple
  (disjoint) Isabelle sessions simultaneously within the same editor
  session.

  Certain events to open or update buffers with theory files cause
  Isabelle/jEdit to resolve dependencies of \emph{theory imports}.
  The system requests to load additional files into editor buffers, in
  order to be included in the theory document model for further
  checking.  It is also possible to resolve dependencies
  automatically, depending on \emph{Plugin Options / Isabelle /
  General / Auto load} (Isabelle system option @{system_option
  jedit_auto_load}).

  \medskip The open text area views on theory buffers define the
  visible \emph{perspective} of Isabelle/jEdit.  This is taken as a
  hint for document processing: the prover ensures that those parts of
  a theory where the user is looking are checked, while other parts
  that are presently not required are ignored.  The perspective is
  changed by opening or closing text area windows, or scrolling within
  some window.

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
  rendering, based on a standard repertoire known from IDEs for
  programming languages: colors, icons, highlighting, squiggly
  underline, tooltips, hyperlinks etc.  For outer syntax of
  Isabelle/Isar there is some traditional syntax-highlighting via
  static keyword tables and tokenization within the editor.  In
  contrast, the painting of inner syntax (term language etc.)\ uses
  semantic information that is reported dynamically from the logical
  context.  Thus the prover can provide additional markup to help the
  user to understand the meaning of formal text, and to produce more
  text with some add-on tools (e.g.\ information messages by automated
  provers or disprovers running in the background).
*}


section {* Tooltips and hyperlinks \label{sec:tooltips-hyperlinks} *}

text {* Formally processed text (prover input or output) contains rich
  markup information that can be explored further by using the
  @{verbatim CONTROL} modifier key on Linux and Windows, or @{verbatim
  COMMAND} on Mac OS X.  Hovering with the mouse while the modifier is
  pressed reveals a \emph{tooltip} (grey box over the text with a
  yellow popup) and/or a \emph{hyperlink} (black rectangle over the
  text); see also \figref{fig:tooltip}.

  \begin{figure}[htbp]
  \begin{center}
  \includegraphics[scale=0.6]{popup1}
  \end{center}
  \caption{Tooltip and hyperlink for some formal entity.}
  \label{fig:tooltip}
  \end{figure}

  Tooltip popups use the same rendering principles as the main text
  area, and further tooltips and/or hyperlinks may be exposed
  recursively by the same mechanism; see
  \figref{fig:nested-tooltips}.

  \begin{figure}[htbp]
  \begin{center}
  \includegraphics[scale=0.6]{popup2}
  \end{center}
  \caption{Nested tooltips over formal entities.}
  \label{fig:nested-tooltips}
  \end{figure}

  The tooltip popup window provides some controls to \emph{close} or
  \emph{detach} the window, turning it into a separate \emph{Info}
  dockable window managed by jEdit.  The @{verbatim ESCAPE} key closes
  \emph{all} popups, which is particularly relevant when nested
  tooltips are stacking up.

  \medskip A black rectangle in the text indicates a hyperlink that
  may be followed by a mouse click (while the @{verbatim CONTROL} or
  @{verbatim COMMAND} modifier key is still pressed). Presently (2013)
  there is no systematic way to return to the original location within
  the editor.

  Also note that the link target may be a file that is itself not
  subject to formal document processing of the editor session and thus
  prevents further exploration: the chain of hyperlinks may end in
  some source file of the underlying logic image, even within the
  Isabelle/ML bootstrap sources of Isabelle/Pure, where the formal
  markup is less detailed. *}


section {* Isabelle symbols *}

text {* Isabelle sources consist of \emph{symbols} that extend plain
  ASCII to allow infinitely many mathematical symbols within the
  formal sources.  This works without depending on particular
  encodings or varying Unicode standards
  \cite{Wenzel:2011:CICM}.\footnote{Raw Unicode characters within
  formal sources would compromise portability and reliability in the
  face of changing interpretation of various unexpected features of
  Unicode.}

  For the prover back-end, formal text consists of ASCII characters
  that are grouped according to some simple rules, e.g.\ as plain
  ``@{verbatim a}'' or symbolic ``@{verbatim "\<alpha>"}''.

  For the editor front-end, a certain subset of symbols is rendered
  physically via Unicode glyphs, in order to show ``@{verbatim "\<alpha>"}''
  as ``@{text "\<alpha>"}'', for example.  This symbol interpretation is
  specified by the Isabelle system distribution in @{file
  "$ISABELLE_HOME/etc/symbols"} and may be augmented by the user in
  @{verbatim "$ISABELLE_HOME_USER/etc/symbols"}.

  The appendix of \cite{isabelle-isar-ref} gives an overview of the
  standard interpretation of finitely many symbols from the infinite
  collection.  Uninterpreted symbols are displayed literally, e.g.\
  ``@{verbatim "\<foobar>"}''.  Overlap of Unicode characters used in
  symbol interpretation with informal ones that might appear e.g.\ in
  comments needs to be avoided!

  \medskip \paragraph{Encoding.} Technically, the Unicode view on
  Isabelle symbols is an \emph{encoding} in jEdit (not in the
  underlying JVM) that is called @{verbatim "UTF-8-Isabelle"}.  It is
  provided by the Isabelle/jEdit plugin and enabled by default for all
  source files.  Sometimes such defaults are reset accidentally, or
  malformed UTF-8 sequences in the text force jEdit to fall back on a
  different encoding like @{verbatim "ISO-8859-15"}.  In that case,
  verbatim ``@{verbatim "\<alpha>"}'' will be shown in the text buffer
  instead of its Unicode rendering ``@{text "\<alpha>"}''.  The jEdit menu
  operation \emph{File / Reload with Encoding / UTF-8-Isabelle} helps
  to resolve such problems, potentially after repairing malformed
  parts of the text.

  \medskip \paragraph{Font.} Correct rendering via Unicode requires a
  font that contains glyphs for the corresponding codepoints.  Most
  system fonts lack that, so Isabelle/jEdit prefers its own
  application font @{verbatim IsabelleText}, which ensures that
  standard collection of Isabelle symbols are actually seen on the
  screen (or printer).

  Note that a Java/AWT/Swing application can load additional fonts
  only if they are not installed as system font already!  This means
  some old version of @{verbatim IsabelleText} that happens to be
  already present prevents Isabelle/jEdit from using its current
  bundled version.  This results in missing glyphs (black rectangles),
  when some obsolete version of @{verbatim IsabelleText} is used by
  accident.  This problem can be avoided by refraining to ``install''
  any version of @{verbatim IsabelleText} in the first place.

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

  \item The \emph{Symbols} panel with some GUI buttons to insert
  certain symbols in the text buffer.  There are also tooltips to
  reveal to official Isabelle representation with some additional
  information about \emph{symbol abbreviations} (see below).

  \item Copy / paste from decoded source files: text that is rendered
  as Unicode already can be re-used to produce further text.  This
  also works between different applications, e.g.\ Isabelle/jEdit and
  some web browser or mail client, as long as the same Unicode view on
  Isabelle symbols is used uniformly.

  \item Copy / paste from prover output within Isabelle/jEdit.  The
  same principles as for text buffers apply, but note that \emph{copy}
  in secondary Isabelle/jEdit windows works via the keyboard shortcut
  @{verbatim "C+c"}.  The jEdit menu actions always refer to the
  primary text area!

  \item Completion provided by Isabelle plugin (see
  \secref{sec:completion}).  Isabelle symbols have a canonical name
  and optional abbreviations.  This can be used with the text
  completion mechanism of Isabelle/jEdit, to replace a prefix of the
  actual symbol like @{verbatim "\<lambda>"}, or its backslashed name
  @{verbatim "\\"}@{verbatim "lambda"}, or its ASCII abbreviation
  @{verbatim "%"} by the Unicode rendering.

  The following table is an extract of the information provided by the
  standard @{file "$ISABELLE_HOME/etc/symbols"} file:

  \medskip
  \begin{tabular}{lll}
    \textbf{symbol} & \textbf{abbreviation} & \textbf{backslashed name} \\\hline
    @{text "\<lambda>"}   & @{verbatim "%"}     &  @{verbatim "\\lambda"}         \\
    @{text "\<Rightarrow>"}  & @{verbatim "=>"}    &  @{verbatim "\\Rightarrow"}     \\
    @{text "\<Longrightarrow>"} & @{verbatim "==>"}   &  @{verbatim "\\Longrightarrow"} \\

    @{text "\<And>"}  & @{verbatim "!!"}    &  @{verbatim "\\And"}            \\
    @{text "\<equiv>"}  & @{verbatim "=="}    &  @{verbatim "\\equiv"}          \\

    @{text "\<forall>"}   & @{verbatim "!"}     &  @{verbatim "\\forall"}         \\
    @{text "\<exists>"}   & @{verbatim "?"}     &  @{verbatim "\\exists"}         \\
    @{text "\<longrightarrow>"} & @{verbatim "-->"}   &  @{verbatim "\\longrightarrow"} \\
    @{text "\<and>"}   & @{verbatim "&"}     &  @{verbatim "\\and"}            \\
    @{text "\<or>"}   & @{verbatim "|"}     &  @{verbatim "\\or"}             \\
    @{text "\<not>"}   & @{verbatim "~"}     &  @{verbatim "\\not"}            \\
    @{text "\<noteq>"}   & @{verbatim "~="}    &  @{verbatim "\\noteq"}          \\
    @{text "\<in>"}   & @{verbatim ":"}     &  @{verbatim "\\in"}             \\
    @{text "\<notin>"}   & @{verbatim "~:"}    &  @{verbatim "\\notin"}          \\
  \end{tabular}
  \medskip

  Note that the above abbreviations refer to the input method. The
  logical notation provides ASCII alternatives that often coincide,
  but deviate occasionally.  This occasionally causes user confusion
  with very old-fashioned Isabelle source that use ASCII replacement
  notation like @{verbatim "!"} or @{verbatim "ALL"} directly.

  \end{enumerate}

  Raw Unicode characters within prover source files should be
  restricted to informal parts, e.g.\ to write text in non-latin
  alphabets.  Mathematical symbols should be defined via the official
  rendering tables, to avoid problems with portability and long-term
  storage of formal text.

  \paragraph{Control symbols.} There are some special control symbols
  to modify the style of a single symbol (without nesting). Control
  symbols may be applied to a region of selected text, either using
  the \emph{Symbols} panel or keyboard shortcuts or jEdit actions.
  These editor operations produce a separate control symbol for each
  symbol in the text, in order to make the whole text appear in a
  certain style.

  \medskip
  \begin{tabular}{llll}
    style & \textbf{symbol} & shortcut & action \\\hline
    superscript & @{verbatim "\<^sup>"} & @{verbatim "C+e UP"} & @{verbatim "isabelle.control-sup"} \\
    subscript & @{verbatim "\<^sub>"} & @{verbatim "C+e DOWN"} & @{verbatim "isabelle.control-sub"} \\
    bold face & @{verbatim "\<^bold>"} & @{verbatim "C+e RIGHT"} & @{verbatim "isabelle.control-bold"} \\
    reset & & @{verbatim "C+e LEFT"} & @{verbatim "isabelle.control-reset"} \\
  \end{tabular}
  \medskip

  To produce a single control symbol, it is also possible to complete
  on @{verbatim "\\"}@{verbatim sup}, @{verbatim "\\"}@{verbatim sub},
  @{verbatim "\\"}@{verbatim bold} as for regular symbols.  *}


section {* Text completion \label{sec:completion} *}

text {*
  Text completion works via some light-weight GUI popup, which is triggered by
  keyboard events during the normal editing process in the main jEdit text
  area and a few additional text fields. The popup interprets special keys:
  @{verbatim TAB}, @{verbatim ESCAPE}, @{verbatim UP}, @{verbatim DOWN},
  @{verbatim PAGE_UP}, @{verbatim PAGE_DOWN}. All other key events are passed
  to the jEdit text area --- this allows to ignore unwanted completions most
  of the time and continue typing quickly.

  Various Isabelle plugin options control the popup behavior and immediate
  insertion into buffer.

  Isabelle Symbols are completed in backslashed forms, e.g.\ @{verbatim
  "\\"}@{verbatim "forall"} or @{verbatim "\<forall>"} that both produce the Isabelle
  symbol @{text "\<forall>"} in its Unicode rendering. Alternatively, symbol
  abbreviations may be used as specified in @{file
  "$ISABELLE_HOME/etc/symbols"}.

  \emph{Explicit completion} works via standard jEdit shortcut @{verbatim
  "C+b"}, which is remapped to action @{verbatim "isabelle.complete"}, with a
  fall-back on regular @{verbatim "complete-word"} for non-Isabelle buffers.

  \emph{Implicit completion} works via keyboard input on text area, with popup
  or immediate insertion into buffer. Plain words require at least 3
  characters to be completed.

  \emph{Immediate completion} means the (unique) replacement text is inserted
  into the buffer without popup. This mode ignores plain words and requires
  more than one characters for symbol abbreviations. Otherwise it falls back
  on completion popup.
*}


chapter {* Known problems and workarounds \label{sec:problems} *}

text {*
  \begin{itemize}

  \item \textbf{Problem:} Lack of dependency management for auxiliary files
  that contribute to a theory (e.g.\ @{command ML_file}).

  \textbf{Workaround:} Re-load files manually within the prover, by
  editing corresponding command in the text.

  \item \textbf{Problem:} Odd behavior of some diagnostic commands with
  global side-effects, like writing a physical file.

  \textbf{Workaround:} Avoid such commands.

  \item \textbf{Problem:} No way to delete document nodes from the overall
  collection of theories.

  \textbf{Workaround:} Ignore unused files.  Restart whole
  Isabelle/jEdit session in worst-case situation.

  \item \textbf{Problem:} Keyboard shortcuts @{verbatim "C+PLUS"} and
  @{verbatim "C+MINUS"} for adjusting the editor font size depend on
  platform details and national keyboards.

  \textbf{Workaround:} Use numeric keypad or rebind keys in the
  jEdit Shortcuts options dialog.

  \item \textbf{Problem:} The Mac OS X keyboard shortcut @{verbatim
  "COMMAND+COMMA"} for application \emph{Preferences} is in conflict
  with the jEdit default shortcut for \emph{Incremental Search Bar}
  (action @{verbatim "quick-search"}).

  \textbf{Workaround:} Remap in jEdit manually according to national
  keyboard, e.g.\ @{verbatim "COMMAND+SLASH"} on English ones.

  \item \textbf{Problem:} Mac OS X system fonts sometimes lead to
  character drop-outs in the main text area.

  \textbf{Workaround:} Use the default @{verbatim IsabelleText} font.
  (Do not install that font on the system.)

  \item \textbf{Problem:} Some Linux / X11 input methods such as IBus
  tend to disrupt key event handling of Java/AWT/Swing.

  \textbf{Workaround:} Do not use input methods, reset the environment
  variable @{verbatim XMODIFIERS} within Isabelle settings (default in
  Isabelle2013-1).

  \item \textbf{Problem:} Some Linux / X11 window managers that are
  not ``re-parenting'' cause problems with additional windows opened
  by Java. This affects either historic or neo-minimalistic window
  managers like @{verbatim awesome} or @{verbatim xmonad}.

  \textbf{Workaround:} Use regular re-parenting window manager.

  \item \textbf{Problem:} Recent forks of Linux / X11 window managers
  and desktop environments (variants of Gnome) disrupt the handling of
  menu popups and mouse positions of Java/AWT/Swing.

  \textbf{Workaround:} Use mainstream versions of Linux desktops.

  \item \textbf{Problem:} Full-screen mode via jEdit action @{verbatim
  "toggle-full-screen"} (default shortcut @{verbatim F11}) works on
  Windows, but not on Mac OS X or various Linux / X11 window managers.

  \textbf{Workaround:} Use native full-screen control of the window
  manager, if available (notably on Mac OS X).

  \item \textbf{Problem:} Full-screen mode and dockable windows in
  \emph{floating} state may lead to confusion about window placement
  (depending on platform characteristics).

  \textbf{Workaround:} Avoid this combination.

  \end{itemize}
*}

end