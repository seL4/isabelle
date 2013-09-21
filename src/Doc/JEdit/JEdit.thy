theory JEdit
imports Base
begin

chapter {* Introduction *}

section {* Concepts and terminology *}

text {* FIXME

parallel proof checking \cite{Wenzel:2009} \cite{Wenzel:2013:ITP}

asynchronous user interaction \cite{Wenzel:2010},
\cite{Wenzel:2012:UITP-EPTCS}

document-oriented proof processing and Prover IDE \cite{Wenzel:2011:CICM}
\cite{Wenzel:2012}

\begin{description}

\item [PIDE] is a general framework for Prover IDEs based on the
Isabelle/Scala. It is built around a concept of \emph{asynchronous document
processing}, which is supported natively by the \emph{parallel proof engine}
that is implemented in Isabelle/ML.

\item [jEdit] is a sophisticated text editor \url{http://www.jedit.org}
implemented in Java. It is easily extensible by plugins written in any
language that works on the JVM, e.g.\ Scala.

\item [Isabelle/jEdit] is the main example application of the PIDE framework
and the default user-interface for Isabelle. It is targeted at beginners and
experts alike.

\end{description}
*}


section {* The Isabelle/jEdit Prover IDE *}

text {*
  Isabelle/jEdit consists of some plugins for the well-known jEdit text
  editor \url{http://www.jedit.org}, according to the following
  principles.

  \begin{itemize}

  \item The original jEdit look-and-feel is generally preserved, although
  some default properties have been changed to accommodate Isabelle (e.g.
  the text area font).

  \item Formal Isabelle/Isar text is checked asynchronously while editing.
  The user is in full command of the editor, and the prover refrains from
  locking portions of the buffer.

  \item Prover feedback works via colors, boxes, squiggly underline,
  hyperlinks, popup windows, icons, clickable output, all based on semantic
  markup produced by Isabelle in the background.

  \item Using the mouse together with the modifier key @{verbatim CONTROL}
  (Linux, Windows) or @{verbatim COMMAND} (Mac OS X) exposes additional
  formal content via tooltips and/or hyperlinks.

  \item Dockable panels (e.g. \emph{Output}, \emph{Symbols}) are managed as
  independent windows by jEdit, which also allows multiple instances.

  \item Formal output (in popups etc.) may be explored recursively, using
  the same techniques as in the editor source buffer.

  \item The prover process and source files are managed on the editor side.
  The prover operates on timeless and stateless document content via
  Isabelle/Scala.

  \item Plugin options of jEdit (for the \emph{Isabelle} plugin) give access
  to a selection of Isabelle/Scala options and its persistence preferences,
  usually with immediate effect on the prover back-end or editor front-end.

  \item The logic image of the prover session may be specified within
  Isabelle/jEdit, but this requires restart. The new image is provided
  automatically by the Isabelle build process.

  \end{itemize}
*}


chapter {* Prover IDE functionality *}

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
  @{file "~~/etc/symbols"} and @{verbatim
  "$ISABELLE_HOME_USER/etc/symbols"}.

  The \emph{IsabelleText} font ensures that Unicode points are actually seen
  on the screen (or printer).

  \medskip
  Input methods:
  \begin{enumerate}
  \item use the \emph{Symbols} dockable window
  \item copy/paste from decoded source files
  \item copy/paste from prover output
  \item completion provided by Isabelle plugin, e.g.

  \medskip
  \begin{tabular}{lll}
    \textbf{backslash escape} & \textbf{abbreviation} & \textbf{symbol} \\[1ex]

    @{verbatim "\\lambda"}         & @{verbatim "%"}     & @{text "\<lambda>"} \\
    @{verbatim "\\Rightarrow"}     & @{verbatim "=>"}    & @{text "\<Rightarrow>"} \\
    @{verbatim "\\Longrightarrow"} & @{verbatim "==>"}   & @{text "\<Longrightarrow>"} \\

    @{verbatim "\\And"}            & @{verbatim "!!"}    & @{text "\<And>"} \\
    @{verbatim "\\equiv"}          & @{verbatim "=="}    & @{text "\<equiv>"} \\

    @{verbatim "\\forall"}         & @{verbatim "!"}     & @{text "\<forall>"} \\
    @{verbatim "\\exists"}         & @{verbatim "?"}     & @{text "\<exists>"} \\
    @{verbatim "\\longrightarrow"} & @{verbatim "-->"}   & @{text "\<longrightarrow>"} \\
    @{verbatim "\\and"}            & @{verbatim "&"}     & @{text "\<and>"} \\
    @{verbatim "\\or"}             & @{verbatim "|"}     & @{text "\<or>"} \\
    @{verbatim "\\not"}            & @{verbatim "~"}     & @{text "\<not>"} \\
    @{verbatim "\\noteq"}          & @{verbatim "~="}    & @{text "\<noteq>"} \\
    @{verbatim "\\in"}             & @{verbatim ":"}     & @{text "\<in>"} \\
    @{verbatim "\\notin"}          & @{verbatim "~:"}    & @{text "\<notin>"} \\
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
  restricted to informal parts, e.g. to write text in non-latin alphabets.
  Mathematical symbols should be defined via the official rendering tables.

  \end{itemize}

  \paragraph{Control symbols.} There are some special control symbols to
  modify the style of a \emph{single} symbol (without nesting). Control
  symbols may be applied to a region of selected text, either using the
  \emph{Symbols} dockable window or keyboard shortcuts.

  \medskip
  \begin{tabular}{lll}
    \textbf{symbol}      & style       & keyboard shortcure \\
    @{verbatim "\<sup>"} & superscript & @{verbatim "C+e UP"} \\
    @{verbatim "\<sub>"} & subscript   & @{verbatim "C+e DOWN"} \\
    @{verbatim "\<bold>"} & bold face  & @{verbatim "C+e RIGHT"} \\
                          & reset      & @{verbatim "C+e LEFT"} \\
  \end{tabular}
*}


section {* Text completion *}

text {* FIXME *}


chapter {* Known problems and workarounds *}

text {*
  \begin{itemize}

  \item \textbf{Problem:} Keyboard shortcuts @{verbatim "C+PLUS"} and
  @{verbatim "C+MINUS"} for adjusting the editor font size depend on
  platform details and national keyboards.

  \textbf{Workaround:} Use numeric keypad or rebind keys in the
  jEdit Shortcuts options dialog.

  \item \textbf{Problem:} Lack of dependency management for auxiliary files
  that contribute to a theory (e.g. @{command ML_file}).

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

  \item \textbf{Problem:} Linux: some X11 window managers that are not
  ``re-parenting'' cause problems with additional windows opened by the Java
  VM. This affects either historic or neo-minimalistic window managers like
  ``@{verbatim awesome}'' or ``@{verbatim xmonad}''.

  \textbf{Workaround:} Use regular re-parenting window manager.

  \item \textbf{Problem:} Mac OS X: the native MacOSX plugin for jEdit tends
  to be disruptive and is off by default. Enabling it might or might not
  improve the user experience.

  \textbf{Workaround:} Disable @{verbatim MacOSX} plugin.

  \item \textbf{Problem:} Mac OS X: Java 7 is officially supported on Lion
  and Mountain Lion, but not Snow Leopard. It usually works on the latter,
  although with a small risk of instabilities.

  \textbf{Workaround:} Update to OS X Mountain Lion, or later.

  \end{itemize}
*}

end