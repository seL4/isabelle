theory Presentation
imports Base
begin

chapter {* Presenting theories \label{ch:present} *}

text {* Isabelle provides several ways to present the outcome of
  formal developments, including WWW-based browsable libraries or
  actual printable documents.  Presentation is centered around the
  concept of \emph{sessions} (\chref{ch:session}).  The global session
  structure is that of a tree, with Isabelle Pure at its root, further
  object-logics derived (e.g.\ HOLCF from HOL, and HOL from Pure), and
  application sessions further on in the hierarchy.

  The tools @{tool_ref mkroot} and @{tool_ref build} provide the
  primary means for managing Isabelle sessions, including proper setup
  for presentation; @{tool build} takes care to have @{executable_ref
  "isabelle-process"} run any additional stages required for document
  preparation, notably the @{tool_ref document} and @{tool_ref latex}.
  The complete tool chain for managing batch-mode Isabelle sessions is
  illustrated in \figref{fig:session-tools}.

  \begin{figure}[htbp]
  \begin{center}
  \begin{tabular}{lp{0.6\textwidth}}

      @{tool_ref mkroot} & invoked once by the user to initialize the
      session @{verbatim ROOT} with optional @{verbatim document}
      directory; \\

      @{tool_ref build} & invoked repeatedly by the user to keep
      session output up-to-date (HTML, documents etc.); \\

      @{executable "isabelle-process"} & run through @{tool_ref
      build}; \\

      @{tool_ref document} & run by the Isabelle process if document
      preparation is enabled; \\

      @{tool_ref latex} & universal {\LaTeX} tool wrapper invoked
      multiple times by @{tool_ref document}; also useful for manual
      experiments; \\

  \end{tabular}
  \caption{The tool chain of Isabelle session presentation} \label{fig:session-tools}
  \end{center}
  \end{figure}
*}


section {* Generating theory browser information \label{sec:info} *}

text {*
  \index{theory browsing information|bold}

  As a side-effect of building sessions, Isabelle is able to generate
  theory browsing information, including HTML documents that show the
  theory sources and the relationship with its ancestors and
  descendants.  Besides the HTML file that is generated for every
  theory, Isabelle stores links to all theories in an index
  file. These indexes are linked with other indexes to represent the
  overall tree structure of the sessions.

  Isabelle also generates graph files that represent the theory
  dependencies within a session.  There is a graph browser Java applet
  embedded in the generated HTML pages, and also a stand-alone
  application that allows browsing theory graphs without having to
  start a WWW client first.  The latter version also includes features
  such as generating Postscript files, which are not available in the
  applet version.  See \secref{sec:browse} for further information.

  \medskip

  The easiest way to let Isabelle generate theory browsing information
  for existing sessions is to invoke @{tool build} with suitable
  options:

\begin{ttbox}
isabelle build -o browser_info -v -c FOL
\end{ttbox}

  The presentation output will appear in @{verbatim
  "$ISABELLE_BROWSER_INFO/FOL"} as reported by the above verbose
  invocation of the build process.

  Many Isabelle sessions (such as @{verbatim "HOL-Library"} in @{file
  "~~/src/HOL/Library"}) also provide actual printable documents.
  These are prepared automatically as well if enabled like this:
\begin{ttbox}
isabelle build -o browser_info -o document=pdf -v -c HOL-Library
\end{ttbox}

  Enabling both browser info and document preparation simultaneously
  causes an appropriate ``document'' link to be included in the HTML
  index.  Documents may be generated independently of browser
  information as well, see \secref{sec:tool-document} for further
  details.

  \bigskip The theory browsing information is stored in a
  sub-directory directory determined by the @{setting_ref
  ISABELLE_BROWSER_INFO} setting plus a prefix corresponding to the
  session identifier (according to the tree structure of sub-sessions
  by default).  In order to present Isabelle applications on the web,
  the corresponding subdirectory from @{setting ISABELLE_BROWSER_INFO}
  can be put on a WWW server.
*}

section {* Preparing session root directories \label{sec:tool-mkroot} *}

text {* The @{tool_def mkroot} tool configures a given directory as
  session root, with some @{verbatim ROOT} file and optional document
  source directory.  Its usage is:
\begin{ttbox}
Usage: isabelle mkroot [OPTIONS] [DIR]

  Options are:
    -d           enable document preparation
    -n NAME      alternative session name (default: DIR base name)

  Prepare session root DIR (default: current directory).
\end{ttbox}

  The results are placed in the given directory @{text dir}, which
  refers to the current directory by default.  The @{tool mkroot} tool
  is conservative in the sense that it does not overwrite existing
  files or directories.  Earlier attempts to generate a session root
  need to be deleted manually.

  \medskip Option @{verbatim "-d"} indicates that the session shall be
  accompanied by a formal document, with @{text dir}@{verbatim
  "/document/root.tex"} as its {\LaTeX} entry point (see also
  \chref{ch:present}).

  Option @{verbatim "-n"} allows to specify an alternative session
  name; otherwise the base name of the given directory is used.

  \medskip The implicit Isabelle settings variable @{setting
  ISABELLE_LOGIC} specifies the parent session, and @{setting
  ISABELLE_DOCUMENT_FORMAT} the document format to be filled filled
  into the generated @{verbatim ROOT} file.  *}


subsubsection {* Examples *}

text {* Produce session @{verbatim Test} (with document preparation)
  within a separate directory of the same name:
\begin{ttbox}
isabelle mkroot -d Test && isabelle build -D Test
\end{ttbox}

  \medskip Upgrade the current directory into a session ROOT with
  document preparation, and build it:
\begin{ttbox}
isabelle mkroot -d && isabelle build -D .
\end{ttbox}
*}


section {* Preparing Isabelle session documents
  \label{sec:tool-document} *}

text {* The @{tool_def document} tool prepares logic session
  documents, processing the sources both as provided by the user and
  generated by Isabelle.  Its usage is:
\begin{ttbox}
Usage: isabelle document [OPTIONS] [DIR]

  Options are:
    -c           cleanup -- be aggressive in removing old stuff
    -n NAME      specify document name (default 'document')
    -o FORMAT    specify output format: dvi (default), dvi.gz, ps,
                 ps.gz, pdf
    -t TAGS      specify tagged region markup

  Prepare the theory session document in DIR (default 'document')
  producing the specified output format.
\end{ttbox}
  This tool is usually run automatically as part of the Isabelle build
  process, provided document preparation has been enabled via suitable
  options.  It may be manually invoked on the generated browser
  information document output as well, e.g.\ in case of errors
  encountered in the batch run.

  \medskip The @{verbatim "-c"} option tells @{tool document} to
  dispose the document sources after successful operation!  This is
  the right thing to do for sources generated by an Isabelle process,
  but take care of your files in manual document preparation!

  \medskip The @{verbatim "-n"} and @{verbatim "-o"} option specify
  the final output file name and format, the default is ``@{verbatim
  document.dvi}''.  Note that the result will appear in the parent of
  the target @{verbatim DIR}.

  \medskip The @{verbatim "-t"} option tells {\LaTeX} how to interpret
  tagged Isabelle command regions.  Tags are specified as a comma
  separated list of modifier/name pairs: ``@{verbatim "+"}@{text
  foo}'' (or just ``@{text foo}'') means to keep, ``@{verbatim
  "-"}@{text foo}'' to drop, and ``@{verbatim "/"}@{text foo}'' to
  fold text tagged as @{text foo}.  The builtin default is equivalent
  to the tag specification ``@{verbatim
  "+theory,+proof,+ML,+visible,-invisible"}''; see also the {\LaTeX}
  macros @{verbatim "\\isakeeptag"}, @{verbatim "\\isadroptag"}, and
  @{verbatim "\\isafoldtag"}, in @{file
  "~~/lib/texinputs/isabelle.sty"}.

  \medskip Document preparation requires a @{verbatim document}
  directory within the session sources.  This directory is supposed to
  contain all the files needed to produce the final document --- apart
  from the actual theories which are generated by Isabelle.

  \medskip For most practical purposes, @{tool document} is smart
  enough to create any of the specified output formats, taking
  @{verbatim root.tex} supplied by the user as a starting point.  This
  even includes multiple runs of {\LaTeX} to accommodate references
  and bibliographies (the latter assumes @{verbatim root.bib} within
  the same directory).

  In more complex situations, a separate @{verbatim build} script for
  the document sources may be given.  It is invoked with command-line
  arguments for the document format and the document variant name.
  The script needs to produce corresponding output files, e.g.\
  @{verbatim root.pdf} for target format @{verbatim pdf} (and default
  default variants).  The main work can be again delegated to @{tool
  latex}, but it is also possible to harvest generated {\LaTeX}
  sources and copy them elsewhere, for example.

  \medskip When running the session, Isabelle copies the content of
  the original @{verbatim document} directory into its proper place
  within @{setting ISABELLE_BROWSER_INFO}, according to the session
  path and document variant.  Then, for any processed theory @{text A}
  some {\LaTeX} source is generated and put there as @{text
  A}@{verbatim ".tex"}.  Furthermore, a list of all generated theory
  files is put into @{verbatim session.tex}.  Typically, the root
  {\LaTeX} file provided by the user would include @{verbatim
  session.tex} to get a document containing all the theories.

  The {\LaTeX} versions of the theories require some macros defined in
  @{file "~~/lib/texinputs/isabelle.sty"}.  Doing @{verbatim
  "\\usepackage{isabelle}"} in @{verbatim root.tex} should be fine;
  the underlying @{tool latex} already includes an appropriate path
  specification for {\TeX} inputs.

  If the text contains any references to Isabelle symbols (such as
  @{verbatim "\\"}@{verbatim "<forall>"}) then @{verbatim
  "isabellesym.sty"} should be included as well.  This package
  contains a standard set of {\LaTeX} macro definitions @{verbatim
  "\\isasym"}@{text foo} corresponding to @{verbatim "\\"}@{verbatim
  "<"}@{text foo}@{verbatim ">"}, see \cite{isabelle-implementation} for a
  complete list of predefined Isabelle symbols.  Users may invent
  further symbols as well, just by providing {\LaTeX} macros in a
  similar fashion as in @{file "~~/lib/texinputs/isabellesym.sty"} of
  the distribution.

  For proper setup of DVI and PDF documents (with hyperlinks and
  bookmarks), we recommend to include @{file
  "~~/lib/texinputs/pdfsetup.sty"} as well.

  \medskip As a final step of Isabelle document preparation, @{tool
  document}~@{verbatim "-c"} is run on the resulting copy of the
  @{verbatim document} directory.  Thus the actual output document is
  built and installed in its proper place.  The generated sources are
  deleted after successful run of {\LaTeX} and friends.

  Some care is needed if the document output location is configured
  differently, say within a directory whose content is still required
  afterwards!
*}


section {* Running {\LaTeX} within the Isabelle environment
  \label{sec:tool-latex} *}

text {* The @{tool_def latex} tool provides the basic interface for
  Isabelle document preparation.  Its usage is:
\begin{ttbox}
Usage: isabelle latex [OPTIONS] [FILE]

  Options are:
    -o FORMAT    specify output format: dvi (default), dvi.gz, ps,
                 ps.gz, pdf, bbl, idx, sty, syms

  Run LaTeX (and related tools) on FILE (default root.tex),
  producing the specified output format.
\end{ttbox}

  Appropriate {\LaTeX}-related programs are run on the input file,
  according to the given output format: @{executable latex},
  @{executable pdflatex}, @{executable dvips}, @{executable bibtex}
  (for @{verbatim bbl}), and @{executable makeindex} (for @{verbatim
  idx}).  The actual commands are determined from the settings
  environment (@{setting ISABELLE_LATEX} etc.).

  The @{verbatim sty} output format causes the Isabelle style files to
  be updated from the distribution.  This is useful in special
  situations where the document sources are to be processed another
  time by separate tools.

  The @{verbatim syms} output is for internal use; it generates lists
  of symbols that are available without loading additional {\LaTeX}
  packages.
*}


subsubsection {* Examples *}

text {* Invoking @{tool latex} by hand may be occasionally useful when
  debugging failed attempts of the automatic document preparation
  stage of batch-mode Isabelle.  The abortive process leaves the
  sources at a certain place within @{setting ISABELLE_BROWSER_INFO},
  see the runtime error message for details.  This enables users to
  inspect {\LaTeX} runs in further detail, e.g.\ like this:

\begin{ttbox}
  cd ~/.isabelle/IsabelleXXXX/browser_info/HOL/Test/document
  isabelle latex -o pdf
\end{ttbox}
*}

end