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
  building blocks are as follows:

  \begin{description}

  \item [PIDE] is a general framework for Prover IDEs based on the
  Isabelle/Scala. It is built around a concept of asynchronous
  document processing, which is supported natively by the parallel
  proof engine that is implemented in Isabelle/ML. The prover
  discontinues the traditional TTY-based command loop in favor of
  direct editing of formal source text.

  \item [Isabelle/ML] is the implementation and extension language of
  Isabelle, see also \cite{isabelle-implementation}. It is integrated
  into the formal logical context and allows to manipulate logical
  entities directly. Arbitrary add-on tools may be implemented for
  object-logics such as Isabelle/HOL.

  \item [Isabelle/Scala] is the system programming language of
  Isabelle. It extends the pure logical environment of Isabelle/ML
  towards the ``real world'' of graphical user interfaces, text
  editors, IDE frameworks, web services etc.  Special infrastructure
  allows to transfer algebraic datatypes and formatted text easily
  between ML and Scala, using asynchronous protocol commands.

  \item [jEdit] is a sophisticated text
  editor\footnote{\url{http://www.jedit.org}} implemented in Java. It
  is easily extensible by plugins written in languages that work on
  the JVM, e.g.\ Scala\footnote{\url{http://www.scala-lang.org/}}.

  \item [Isabelle/jEdit] is the main example application of the PIDE
  framework and the default user-interface for Isabelle. It is
  targeted at beginners and experts alike. Technically, Isabelle/jEdit
  combines a slightly modified version of the official jEdit code base
  with a special plugin for Isabelle, which is then integrated as
  standalone application for the main operating system platforms:
  Linux, Windows, Mac OS X.

  \end{description}

  The subtle differences of Isabelle/ML versus Standard ML,
  Isabelle/Scala versus Scala, Isabelle/jEdit versus regular jEdit
  need to be taken into account when discussing any of these PIDE
  building blocks on public forums, mailing lists, or even scientific
  publications.
*}


section {* The Isabelle/jEdit Prover IDE *}

text {*
  \includegraphics[width=\textwidth]{isabelle-jedit}

  Isabelle/jEdit consists of some plugins for the well-known jEdit
  text editor \url{http://www.jedit.org}, according to the following
  principles.

  \begin{itemize}

  \item The original jEdit look-and-feel is generally preserved,
  although some default properties have been changed to accommodate
  Isabelle (e.g.\ the text area font).

  \item Formal Isabelle/Isar text is checked asynchronously while
  editing.  The user is in full command of the editor, and the prover
  refrains from locking portions of the buffer.

  \item Prover feedback works via colors, boxes, squiggly underline,
  hyperlinks, popup windows, icons, clickable output, all based on
  semantic markup produced by Isabelle in the background.

  \item Using the mouse together with the modifier key @{verbatim
  CONTROL} (Linux, Windows) or @{verbatim COMMAND} (Mac OS X) exposes
  additional formal content via tooltips and/or hyperlinks.

  \item Dockable windows (e.g.\ \emph{Output}, \emph{Symbols}) are
  managed separately by jEdit, which also allows multiple instances.

  \item Formal output (in popups etc.) may be explored recursively,
  using the same techniques as in the editor source buffer.

  \item The prover process and source files are managed on the editor
  side.  The prover operates on timeless and stateless document
  content via Isabelle/Scala.

  \item Plugin options of jEdit (for the \emph{Isabelle} plugin) give
  access to a selection of Isabelle/Scala options and its persistence
  preferences, usually with immediate effect on the prover back-end or
  editor front-end.

  \item The logic image of the prover session may be specified within
  Isabelle/jEdit, but this requires restart. The new image is provided
  automatically by the Isabelle build tool.

  \end{itemize}
*}


subsection {* Documentation *}

text {* Regular jEdit documentation is accessible via its @{verbatim
  Help} menu or @{verbatim F1} keyboard shortcut. This includes a full
  \emph{User's Guide} and \emph{Frequently Asked Questions} for this
  sophisticated text editor.

  Most of the information is relevant for Isabelle/jEdit as well, but
  one needs to keep in mind that defaults sometimes differ, and the
  official jEdit documentation does not know about the Isabelle plugin
  with its bias towards theory editing.
*}


subsection {* Plugins *}

text {* The \emph{Plugin Manager} of jEdit allows to augment editor
  functionality by JVM modules (jars) that are provided by the central
  plugin repository, or one of various mirror sites. The main
  \emph{Isabelle} plugin that is bundled with Isabelle/jEdit needs to
  remain active at all times! A few additional plugins are bundled
  with Isabelle/jEdit for convenience or out of necessity, notably
  \emph{Console} with its Isabelle/Scala sub-plugin and
  \emph{SideKick} with some Isabelle-specific parsers for tree
  structure.

  Connecting to the plugin server infrastructure of the jEdit project
  allows to update bundled plugins or to add further
  functionality. This needs to be done with the usual care for such an
  open bazaar, with contributions of very mixed quality. Arbitrary
  combinations of add-on features are apt to cause problems.

  It is advisable to start with the default configuration of
  Isabelle/jEdit and develop some understanding how it is supposed to
  work, before loading additional plugins at a grand scale.
*}


subsection {* Options *}

text {* jEdit and Isabelle have separate management of persistent
  options.  Regular jEdit options are accessible via the dialogs for
  \emph{Global Options} and \emph{Plugin Options}.  This results in an
  environment of name-value properties that is stored within the
  \emph{settings directory} of jEdit; see also the menu
  \emph{Utilities / Settings Directory}.

  In contrast, Isabelle system options are managed by Isabelle/Scala;
  see also \cite{isabelle-sys}, especially the coverage of Isabelle
  sessions and build.  Options that are declared as \textbf{public}
  are exposed to the \emph{Plugin Options} dialog of jEdit in its
  section \emph{Isabelle / General}.  This provides a view on Isabelle
  options and persistent preferences in @{verbatim
  "$ISABELLE_HOME_USER/etc/preferences"}, independently of the jEdit
  properties in its settings directory.

  Isabelle options are loaded once on startup and saved on shutdown.
  Editing the machine-generated @{verbatim "etc/preferences"} manually
  while the application is running is likely to cause a lost-update!

  Some Isabelle options that are accessible in the Isabelle/jEdit
  Plugin Options dialog affect general parameters that are relevant
  outside Isabelle/jEdit as well, e.g.\ @{system_option threads} or
  @{system_option parallel_proofs} for the Isabelle build tool
  \cite{isabelle-sys}.
*}


subsection {* Keymaps *}

text {* Keyboard shortcuts used to be managed as jEdit properties in
  the past, but recent versions (2013) have a separate concept of
  \emph{keymap}.  The ``imported'' keymap is produced initially from
  the environment of properties that is available at the first start
  of the editor.

  This is relevant for Isabelle/jEdit due to various fine-tuning of
  default properties, and additional keyboard shortcuts for Isabelle
  specific functionality. Users may change their keymap later on, but
  may need to copy important key bindings manually.
*}


section {* Platform look-and-feel *}

text {* jEdit is a Java/Swing application with some ambition to
  support ``native'' platform look-and-feel, within the limits of what
  Oracle as Java provider and major operating system vendors and
  distributors allow.

  Isabelle/jEdit uses platform-specific look-and-feel as follows:

  \begin{description}

  \item[Linux] The platform-independent \emph{Nimbus} is used by
  default, but the classic \emph{Metal} also works.

  Quasi-native \emph{GTK+} works under the side-condition that the
  overall GTK theme is selected in a Java/Swing friendly way: the
  success rate is @{text "\<approx>"} 50\%.

  \item[Windows] Regular \emph{Windows} is used by default, but
  platform-independent \emph{Nimbus} and \emph{Metal} also work.

  \item[Mac OS X] standard \emph{Apple Aqua} is used by default.
  Moreover the bundled \emph{MacOSX} plugin provides various functions
  that are expected from applications on that particular platform:
  quit from menu or dock, preferences menu, drag-and-drop of text
  files on the application, full-screen mode for main editor windows
  etc.

  \end{description}

  Users may experiment with different look-and-feels, but need to keep
  in mind that this extra dimension of GUI functionality is unlikely
  to work in arbitrary combinations.  The \emph{GTK+} look-and-feel is
  particularly critical due to its additional dimension of ``themes''.
  It is also important to ensure that the fonts of standard GUI
  components use anti-aliasing as usual.

  After changing the look-and-feel in \emph{Global Options /
  Appearance}, it is advisable to restart Isabelle/jEdit in order to
  take full effect.
*}


chapter {* Prover IDE functionality *}

section {* Main text area *}

text {*

  Source files with \texttt{.thy} extension are treated specifically:
  Isabelle/jEdit adds them to the formal document-model of Isabelle/PIDE, that
  maintains semantic information provided by the prover in the background,
  while the user is editing the text in the foreground.

  \medskip Physical rendering of document content draws from the
  standard repertoire of known IDEs for programming languages, with
  highlighting, squiggles, tooltips, hyperlinks etc.  In the above
  screenshot, only the bold keywords of the Isar language use
  traditional syntax-highlighting in jEdit with static tables; all
  other coloring is based on dynamic information from the logical
  context of the prover.

  Such annotated text regions can be explored further by using the
  \texttt{CONTROL} modifier key (or \texttt{COMMAND} on Mac OS X),
  together with mouse hovering or clicking.  It reveals tooltips and
  hyperlinks, e.g.\ see \texttt{constant "Example.path"} above, and
  thus explains how a certain piece of source text has been
  interpreted.
 *}


section {* Isabelle symbols and fonts *}

text {*
  Isabelle supports infinitely many symbols:

  \medskip
  \begin{tabular}{l}
    @{text "\<alpha>"}, @{text "\<beta>"}, @{text "\<gamma>"}, @{text "\<dots>"} \\
    @{text "\<forall>"}, @{text "\<exists>"}, @{text "\<or>"}, @{text "\<and>"}, @{text "\<longrightarrow>"}, @{text "\<longleftrightarrow>"}, @{text "\<dots>"} \\
    @{text "\<le>"}, @{text "\<ge>"}, @{text "\<sqinter>"}, @{text "\<squnion>"}, @{text "\<dots>"} \\
    @{text "\<aleph>"}, @{text "\<triangle>"}, @{text "\<nabla>"}, @{text "\<dots>"} \\
    @{verbatim "\<foo>"}, @{verbatim "\<bar>"}, @{verbatim "\<baz>"}, @{text "\<dots>"} \\
  \end{tabular}
  \medskip

  A default mapping relates some Isabelle symbols to Unicode points (see
  @{file "$ISABELLE_HOME/etc/symbols"} and @{verbatim
  "$ISABELLE_HOME_USER/etc/symbols"}.

  The \emph{IsabelleText} font ensures that Unicode points are actually seen
  on the screen (or printer).

  \medskip
  Input methods:
  \begin{enumerate}
  \item use the \emph{Symbols} dockable window
  \item copy/paste from decoded source files
  \item copy/paste from prover output
  \item completion provided by Isabelle plugin, e.g.\

  \medskip
  \begin{tabular}{lll}
    \textbf{symbol} & \textbf{abbreviation} & \textbf{backslash escape} \\[1ex]

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

  \end{enumerate}

  \paragraph{Notes:}
  \begin{itemize}

  \item The above abbreviations refer to the input method. The logical
  notation provides ASCII alternatives that often coincide, but deviate
  occasionally.

  \item Generic jEdit abbreviations or plugins perform similar source
  replacement operations; this works for Isabelle as long as the Unicode
  sequences coincide with the symbol mapping.

  \item Raw Unicode characters within prover source files should be
  restricted to informal parts, e.g.\ to write text in non-latin alphabets.
  Mathematical symbols should be defined via the official rendering tables.

  \end{itemize}

  \paragraph{Control symbols.} There are some special control symbols to
  modify the style of a \emph{single} symbol (without nesting). Control
  symbols may be applied to a region of selected text, either using the
  \emph{Symbols} dockable window or keyboard shortcuts.

  \medskip
  \begin{tabular}{lll}
    \textbf{symbol}      & style       & keyboard shortcut \\\hline
    @{verbatim "\<sup>"} & superscript & @{verbatim "C+e UP"} \\
    @{verbatim "\<sub>"} & subscript   & @{verbatim "C+e DOWN"} \\
    @{verbatim "\<bold>"} & bold face  & @{verbatim "C+e RIGHT"} \\
                          & reset      & @{verbatim "C+e LEFT"} \\
  \end{tabular}
*}


section {* Text completion *}

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


chapter {* Known problems and workarounds *}

text {*
  \begin{itemize}

  \item \textbf{Problem:} Keyboard shortcuts @{verbatim "C+PLUS"} and
  @{verbatim "C+MINUS"} for adjusting the editor font size depend on
  platform details and national keyboards.

  \textbf{Workaround:} Use numeric keypad or rebind keys in the
  jEdit Shortcuts options dialog.

  \item \textbf{Problem:} Lack of dependency management for auxiliary files
  that contribute to a theory (e.g.\ @{command ML_file}).

  \textbf{Workaround:} Re-load files manually within the prover.

  \item \textbf{Problem:} Odd behavior of some diagnostic commands with
  global side-effects, like writing a physical file.

  \textbf{Workaround:} Avoid such commands.

  \item \textbf{Problem:} No way to delete document nodes from the overall
  collection of theories.

  \textbf{Workaround:} Restart whole Isabelle/jEdit session in worst-case
  situation.

  \item \textbf{Problem:} Linux: some desktop environments with extreme
  animation effects may disrupt Java 7 window placement and/or keyboard
  focus.

  \textbf{Workaround:} Disable such effects.

  \item \textbf{Problem:} Linux: some X11 input methods such as IBus tend
  to disrupt key event handling of Java/Swing.

  \textbf{Workaround:} Do not use input methods, reset the environment
  variable @{verbatim XMODIFIERS} within Isabelle settings (default in
  Isabelle2013-1).

  \item \textbf{Problem:} Linux: some X11 window managers that are not
  ``re-parenting'' cause problems with additional windows opened by the Java
  VM. This affects either historic or neo-minimalistic window managers like
  ``@{verbatim awesome}'' or ``@{verbatim xmonad}''.

  \textbf{Workaround:} Use regular re-parenting window manager.

  \item \textbf{Problem:} The Mac OS X keyboard shortcut @{verbatim
  "COMMAND+COMMA"} for Preferences is in conflict with the jEdit default
  binding for @{verbatim "quick-search"}.

  \textbf{Workaround:} Remap in jEdit manually according to national
  keyboard, e.g.\ @{verbatim "COMMAND+SLASH"} on English ones.

  \item \textbf{Problem:} Mac OS X: Java 7 is officially supported on Lion
  and Mountain Lion, but not Snow Leopard. It usually works on the latter,
  although with a small risk of instabilities.

  \textbf{Workaround:} Update to OS X Mountain Lion, or later.

  \end{itemize}
*}

end