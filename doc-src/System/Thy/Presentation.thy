theory Presentation
imports Base
begin

chapter {* Presenting theories \label{ch:present} *}

text {*
  Isabelle provides several ways to present the outcome of formal
  developments, including WWW-based browsable libraries or actual
  printable documents.  Presentation is centered around the concept of
  \emph{logic sessions}.  The global session structure is that of a
  tree, with Isabelle Pure at its root, further object-logics derived
  (e.g.\ HOLCF from HOL, and HOL from Pure), and application sessions
  in leaf positions (usually without a separate image).

  The Isabelle tools @{tool_ref mkdir} and @{tool_ref make} provide
  the primary means for managing Isabelle sessions, including proper
  setup for presentation.  Here the @{tool_ref usedir} tool takes care
  to let @{executable_ref "isabelle-process"} process run any
  additional stages required for document preparation, notably the
  tools @{tool_ref document} and @{tool_ref latex}.  The complete tool
  chain for managing batch-mode Isabelle sessions is illustrated in
  \figref{fig:session-tools}.

  \begin{figure}[htbp]
  \begin{center}
  \begin{tabular}{lp{0.6\textwidth}}

      @{verbatim isabelle} @{tool_ref mkdir} & invoked once by the user
      to create the initial source setup (common @{verbatim
      IsaMakefile} plus a single session directory); \\

      @{verbatim isabelle} @{tool make} & invoked repeatedly by the
      user to keep session output up-to-date (HTML, documents etc.); \\

      @{verbatim isabelle} @{tool usedir} & part of the standard
      @{verbatim IsaMakefile} entry of a session; \\

      @{executable "isabelle-process"} & run through @{verbatim
      isabelle} @{tool_ref usedir}; \\

      @{verbatim isabelle} @{tool_ref document} & run by the Isabelle
      process if document preparation is enabled; \\

      @{verbatim isabelle} @{tool_ref latex} & universal {\LaTeX} tool
      wrapper invoked multiple times by @{verbatim isabelle} @{tool_ref
      document}; also useful for manual experiments; \\

  \end{tabular}
  \caption{The tool chain of Isabelle session presentation} \label{fig:session-tools}
  \end{center}
  \end{figure}
*}


section {* Generating theory browser information \label{sec:info} *}

text {*
  \index{theory browsing information|bold}

  As a side-effect of running a logic sessions, Isabelle is able to
  generate theory browsing information, including HTML documents that
  show a theory's definition, the theorems proved in its ML file and
  the relationship with its ancestors and descendants.  Besides the
  HTML file that is generated for every theory, Isabelle stores links
  to all theories in an index file. These indexes are linked with
  other indexes to represent the overall tree structure of logic
  sessions.

  Isabelle also generates graph files that represent the theory
  hierarchy of a logic.  There is a graph browser Java applet embedded
  in the generated HTML pages, and also a stand-alone application that
  allows browsing theory graphs without having to start a WWW client
  first.  The latter version also includes features such as generating
  Postscript files, which are not available in the applet version.
  See \secref{sec:browse} for further information.

  \medskip

  The easiest way to let Isabelle generate theory browsing information
  for existing sessions is to append ``@{verbatim "-i true"}'' to the
  @{setting_ref ISABELLE_USEDIR_OPTIONS} before invoking @{verbatim
  isabelle} @{tool make} (or @{file "$ISABELLE_HOME/build"}).  For
  example, add something like this to your Isabelle settings file

\begin{ttbox}
ISABELLE_USEDIR_OPTIONS="-i true"
\end{ttbox}

  and then change into the @{file "~~/src/FOL"} directory and run
  @{verbatim isabelle} @{tool make}, or even @{verbatim isabelle}
  @{tool make}~@{verbatim all}.  The presentation output will appear
  in @{verbatim "ISABELLE_BROWSER_INFO/FOL"}, which usually refers to
  something like @{verbatim
  "~/.isabelle/IsabelleXXXX/browser_info/FOL"}.  Note that option
  @{verbatim "-v true"} will make the internal runs of @{tool usedir}
  more explicit about such details.

  Many standard Isabelle sessions (such as @{file "~~/src/HOL/ex"})
  also provide actual printable documents.  These are prepared
  automatically as well if enabled like this, using the @{verbatim
  "-d"} option
\begin{ttbox}
ISABELLE_USEDIR_OPTIONS="-i true -d dvi"
\end{ttbox}
  Enabling options @{verbatim "-i"} and @{verbatim "-d"}
  simultaneously as shown above causes an appropriate ``document''
  link to be included in the HTML index.  Documents (or raw document
  sources) may be generated independently of browser information as
  well, see \secref{sec:tool-document} for further details.

  \bigskip The theory browsing information is stored in a
  sub-directory directory determined by the @{setting_ref
  ISABELLE_BROWSER_INFO} setting plus a prefix corresponding to the
  session identifier (according to the tree structure of sub-sessions
  by default).  A complete WWW view of all standard object-logics and
  examples of the Isabelle distribution is available at the usual
  Isabelle sites:
  \begin{center}\small
  \begin{tabular}{l}
    \url{http://isabelle.in.tum.de/dist/library/} \\
    \url{http://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/} \\
    \url{http://mirror.cse.unsw.edu.au/pub/isabelle/dist/library/} \\
  \end{tabular}
  \end{center}
  
  \medskip In order to present your own theories on the web, simply
  copy the corresponding subdirectory from @{setting
  ISABELLE_BROWSER_INFO} to your WWW server, having generated browser
  info like this:
\begin{ttbox}
isabelle usedir -i true HOL Foo
\end{ttbox}

  This assumes that directory @{verbatim Foo} contains some @{verbatim
  ROOT.ML} file to load all your theories, and HOL is your parent
  logic image (@{verbatim isabelle} @{tool_ref mkdir} assists in
  setting up Isabelle session directories.  Theory browser information
  for HOL should have been generated already beforehand.
  Alternatively, one may specify an external link to an existing body
  of HTML data by giving @{tool usedir} a @{verbatim "-P"} option like
  this:
\begin{ttbox}
isabelle usedir -i true -P http://isabelle.in.tum.de/library/ HOL Foo
\end{ttbox}

  \medskip For production use, the @{tool usedir} tool is usually
  invoked in an appropriate @{verbatim IsaMakefile}, via the Isabelle
  @{tool make} tool.  There is a separate @{tool mkdir} tool to
  provide easy setup of all this, with only minimal manual editing
  required.
\begin{ttbox}
isabelle mkdir HOL Foo && isabelle make
\end{ttbox}
  See \secref{sec:tool-mkdir} for more information on preparing
  Isabelle session directories, including the setup for documents.
*}


section {* Creating Isabelle session directories
  \label{sec:tool-mkdir} *}

text {*
  The @{tool_def mkdir} utility prepares Isabelle session source
  directories, including a sensible default setup of @{verbatim
  IsaMakefile}, @{verbatim ROOT.ML}, and a @{verbatim document}
  directory with a minimal @{verbatim root.tex} that is sufficient to
  print all theories of the session (in the order of appearance); see
  \secref{sec:tool-document} for further information on Isabelle
  document preparation.  The usage of @{verbatim isabelle} @{tool
  mkdir} is:

\begin{ttbox}
Usage: mkdir [OPTIONS] [LOGIC] NAME

  Options are:
    -I FILE      alternative IsaMakefile output
    -P           include parent logic target
    -b           setup build mode (session outputs heap image)
    -q           quiet mode

  Prepare session directory, including IsaMakefile and document source,
  with parent LOGIC (default ISABELLE_LOGIC=\$ISABELLE_LOGIC)
\end{ttbox}

  The @{tool mkdir} tool is conservative in the sense that any
  existing @{verbatim IsaMakefile} etc.\ is left unchanged.  Thus it
  is safe to invoke it multiple times, although later runs may not
  have the desired effect.

  Note that @{tool mkdir} is unable to change @{verbatim IsaMakefile}
  incrementally --- manual changes are required for multiple
  sub-sessions.  On order to get an initial working session, the only
  editing needed is to add appropriate @{ML use_thy} calls to the
  generated @{verbatim ROOT.ML} file.
*}


subsubsection {* Options *}

text {*
  The @{verbatim "-I"} option specifies an alternative to @{verbatim
  IsaMakefile} for dependencies.  Note that ``@{verbatim "-"}'' refers
  to \emph{stdout}, i.e.\ ``@{verbatim "-I-"}'' provides an easy way
  to peek at @{tool mkdir}'s idea of @{tool make} setup required for
  some particular of Isabelle session.

  \medskip The @{verbatim "-P"} option includes a target for the
  parent @{verbatim LOGIC} session in the generated @{verbatim
  IsaMakefile}.  The corresponding sources are assumed to be located
  within the Isabelle distribution.

  \medskip The @{verbatim "-b"} option sets up the current directory
  as the base for a new session that provides an actual logic image,
  as opposed to one that only runs several theories based on an
  existing image.  Note that in the latter case, everything except
  @{verbatim IsaMakefile} would be placed into a separate directory
  @{verbatim NAME}, rather than the current one.  See
  \secref{sec:tool-usedir} for further information on \emph{build
  mode} vs.\ \emph{example mode} of the @{tool usedir} utility.

  \medskip The @{verbatim "-q"} option enables quiet mode, suppressing
  further notes on how to proceed.
*}


subsubsection {* Examples *}

text {*
  The standard setup of a single ``example session'' based on the
  default logic, with proper document generation is generated like
  this:
\begin{ttbox}
isabelle mkdir Foo && isabelle make
\end{ttbox}

  \noindent The theory sources should be put into the @{verbatim Foo}
  directory, and its @{verbatim ROOT.ML} should be edited to load all
  required theories.  Invoking @{verbatim isabelle} @{tool make} again
  would run the whole session, generating browser information and the
  document automatically.  The @{verbatim IsaMakefile} is typically
  tuned manually later, e.g.\ adding source dependencies, or changing
  the options passed to @{tool usedir}.

  \medskip Large projects may demand further sessions, potentially
  with separate logic images being created.  This usually requires
  manual editing of the generated @{verbatim IsaMakefile}, which is
  meant to cover all of the sub-session directories at the same time
  (this is the deeper reasong why @{verbatim IsaMakefile} is not made
  part of the initial session directory created by @{verbatim
  isabelle} @{tool mkdir}).  See @{file "~~/src/HOL/IsaMakefile"} for
  a full-blown example.
*}


section {* Running Isabelle sessions \label{sec:tool-usedir} *}

text {*
  The @{tool_def usedir} utility builds object-logic images, or runs
  example sessions based on existing logics. Its usage is:
\begin{ttbox}
Usage: usedir [OPTIONS] LOGIC NAME

  Options are:
    -C BOOL      copy existing document directory to -D PATH (default true)
    -D PATH      dump generated document sources into PATH
    -M MAX       multithreading: maximum number of worker threads (default 1)
    -P PATH      set path for remote theory browsing information
    -Q INT       set threshold for sub-proof parallelization (default 50)
    -T LEVEL     multithreading: trace level (default 0)
    -V VARIANT   declare alternative document VARIANT
    -b           build mode (output heap image, using current dir)
    -d FORMAT    build document as FORMAT (default false)
    -f NAME      use ML file NAME (default ROOT.ML)
    -g BOOL      generate session graph image for document (default false)
    -i BOOL      generate theory browser information (default false)
    -m MODE      add print mode for output
    -p LEVEL     set level of detail for proof objects (default 0)
    -q LEVEL     set level of parallel proof checking (default 1)
    -r           reset session path
    -s NAME      override session NAME
    -t BOOL      internal session timing (default false)
    -v BOOL      be verbose (default false)

  Build object-logic or run examples. Also creates browsing
  information (HTML etc.) according to settings.

  ISABELLE_USEDIR_OPTIONS=...

  ML_PLATFORM=...
  ML_HOME=...
  ML_SYSTEM=...
  ML_OPTIONS=...
\end{ttbox}

  Note that the value of the @{setting_ref ISABELLE_USEDIR_OPTIONS}
  setting is implicitly prefixed to \emph{any} @{tool usedir}
  call. Since the @{verbatim IsaMakefile}s of all object-logics
  distributed with Isabelle just invoke @{tool usedir} for the real
  work, one may control compilation options globally via above
  variable. In particular, generation of \rmindex{HTML} browsing
  information and document preparation is controlled here.
*}


subsubsection {* Options *}

text {*
  Basically, there are two different modes of operation: \emph{build
  mode} (enabled through the @{verbatim "-b"} option) and
  \emph{example mode} (default).

  Calling @{tool usedir} with @{verbatim "-b"} runs @{executable
  "isabelle-process"} with input image @{verbatim LOGIC} and output to
  @{verbatim NAME}, as provided on the command line. This will be a
  batch session, running @{verbatim ROOT.ML} from the current
  directory and then quitting.  It is assumed that @{verbatim ROOT.ML}
  contains all ML commands required to build the logic.

  In example mode, @{tool usedir} runs a read-only session of
  @{verbatim LOGIC} and automatically runs @{verbatim ROOT.ML} from
  within directory @{verbatim NAME}.  It assumes that this file
  contains appropriate ML commands to run the desired examples.

  \medskip The @{verbatim "-i"} option controls theory browser data
  generation. It may be explicitly turned on or off --- as usual, the
  last occurrence of @{verbatim "-i"} on the command line wins.

  The @{verbatim "-P"} option specifies a path (or actual URL) to be
  prefixed to any \emph{non-local} reference of existing theories.
  Thus user sessions may easily link to existing Isabelle libraries
  already present on the WWW.

  The @{verbatim "-m"} options specifies additional print modes to be
  activated temporarily while the session is processed.

  \medskip The @{verbatim "-d"} option controls document preparation.
  Valid arguments are @{verbatim false} (do not prepare any document;
  this is default), or any of @{verbatim dvi}, @{verbatim dvi.gz},
  @{verbatim ps}, @{verbatim ps.gz}, @{verbatim pdf}.  The logic
  session has to provide a properly setup @{verbatim document}
  directory.  See \secref{sec:tool-document} and
  \secref{sec:tool-latex} for more details.

  \medskip The @{verbatim "-V"} option declares alternative document
  variants, consisting of name/tags pairs (cf.\ options @{verbatim
  "-n"} and @{verbatim "-t"} of the @{tool_ref document} tool).  The
  standard document is equivalent to ``@{verbatim
  "document=theory,proof,ML"}'', which means that all theory begin/end
  commands, proof body texts, and ML code will be presented
  faithfully.  An alternative variant ``@{verbatim
  "outline=/proof/ML"}'' would fold proof and ML parts, replacing the
  original text by a short place-holder.  The form ``@{text
  name}@{verbatim "=-"},'' means to remove document @{text name} from
  the list of variants to be processed.  Any number of @{verbatim
  "-V"} options may be given; later declarations have precedence over
  earlier ones.

  \medskip The @{verbatim "-g"} option produces images of the theory
  dependency graph (cf.\ \secref{sec:browse}) for inclusion in the
  generated document, both as @{verbatim session_graph.eps} and
  @{verbatim session_graph.pdf} at the same time.  To include this in
  the final {\LaTeX} document one could say @{verbatim
  "\\includegraphics{session_graph}"} in @{verbatim
  "document/root.tex"} (omitting the file-name extension enables
  {\LaTeX} to select to correct version, either for the DVI or PDF
  output path).

  \medskip The @{verbatim "-D"} option causes the generated document
  sources to be dumped at location @{verbatim PATH}; this path is
  relative to the session's main directory.  If the @{verbatim "-C"}
  option is true, this will include a copy of an existing @{verbatim
  document} directory as provided by the user.  For example,
  @{verbatim isabelle} @{tool usedir}~@{verbatim "-D generated HOL
  Foo"} produces a complete set of document sources at @{verbatim
  "Foo/generated"}.  Subsequent invocation of @{verbatim
  isabelle} @{tool document}~@{verbatim "Foo/generated"} (see also
  \secref{sec:tool-document}) will process the final result
  independently of an Isabelle job.  This decoupled mode of operation
  facilitates debugging of serious {\LaTeX} errors, for example.

  \medskip The @{verbatim "-p"} option determines the level of detail
  for internal proof objects, see also the \emph{Isabelle Reference
  Manual}~\cite{isabelle-ref}.

  \medskip The @{verbatim "-q"} option specifies the level of parallel
  proof checking: @{verbatim 0} no proofs, @{verbatim 1} toplevel
  proofs (default), @{verbatim 2} toplevel and nested Isar proofs.
  The option @{verbatim "-Q"} specifies a threshold for @{verbatim
  "-q2"}: nested proofs are only parallelized when the current number
  of forked proofs falls below the given value (default 50),
  multiplied by the number of worker threads (see option @{verbatim
  "-M"}).

  \medskip The @{verbatim "-t"} option produces a more detailed
  internal timing report of the session.

  \medskip The @{verbatim "-v"} option causes additional information
  to be printed while running the session, notably the location of
  prepared documents.

  \medskip The @{verbatim "-M"} option specifies the maximum number of
  parallel worker threads used for processing independent tasks when
  checking theory sources (multithreading only works on suitable ML
  platforms).  The special value of @{verbatim 0} or @{verbatim max}
  refers to the number of actual CPU cores of the underlying machine,
  which is a good starting point for optimal performance tuning.  The
  @{verbatim "-T"} option determines the level of detail in tracing
  output concerning the internal locking and scheduling in
  multithreaded operation.  This may be helpful in isolating
  performance bottle-necks, e.g.\ due to excessive wait states when
  locking critical code sections.

  \medskip Any @{tool usedir} session is named by some \emph{session
  identifier}. These accumulate, documenting the way sessions depend
  on others. For example, consider @{verbatim "Pure/FOL/ex"}, which
  refers to the examples of FOL, which in turn is built upon Pure.

  The current session's identifier is by default just the base name of
  the @{verbatim LOGIC} argument (in build mode), or of the @{verbatim
  NAME} argument (in example mode). This may be overridden explicitly
  via the @{verbatim "-s"} option.
*}


subsubsection {* Examples *}

text {*
  Refer to the @{verbatim IsaMakefile}s of the Isabelle distribution's
  object-logics as a model for your own developments.  For example,
  see @{file "~~/src/FOL/IsaMakefile"}.  The Isabelle @{tool_ref
  mkdir} tool creates @{verbatim IsaMakefile}s with proper invocation
  of @{tool usedir} as well.
*}


section {* Preparing Isabelle session documents
  \label{sec:tool-document} *}

text {*
  The @{tool_def document} utility prepares logic session documents,
  processing the sources both as provided by the user and generated by
  Isabelle.  Its usage is:
\begin{ttbox}
Usage: document [OPTIONS] [DIR]

  Options are:
    -c           cleanup -- be aggressive in removing old stuff
    -n NAME      specify document name (default 'document')
    -o FORMAT    specify output format: dvi (default), dvi.gz, ps,
                 ps.gz, pdf
    -t TAGS      specify tagged region markup

  Prepare the theory session document in DIR (default 'document')
  producing the specified output format.
\end{ttbox}
  This tool is usually run automatically as part of the corresponding
  Isabelle batch process, provided document preparation has been
  enabled (cf.\ the @{verbatim "-d"} option of the @{tool_ref usedir}
  tool).  It may be manually invoked on the generated browser
  information document output as well, e.g.\ in case of errors
  encountered in the batch run.

  \medskip The @{verbatim "-c"} option tells the @{tool document} tool
  to dispose the document sources after successful operation.  This is
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

  \medskip Document preparation requires a properly setup ``@{verbatim
  document}'' directory within the logic session sources.  This
  directory is supposed to contain all the files needed to produce the
  final document --- apart from the actual theories which are
  generated by Isabelle.

  \medskip For most practical purposes, the @{tool document} tool is
  smart enough to create any of the specified output formats, taking
  @{verbatim root.tex} supplied by the user as a starting point.  This
  even includes multiple runs of {\LaTeX} to accommodate references
  and bibliographies (the latter assumes @{verbatim root.bib} within
  the same directory).

  In more complex situations, a separate @{verbatim IsaMakefile} for
  the document sources may be given instead.  This should provide
  targets for any admissible document format; these have to produce
  corresponding output files named after @{verbatim root} as well,
  e.g.\ @{verbatim root.dvi} for target format @{verbatim dvi}.

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
  the underlying Isabelle @{tool latex} tool already includes an
  appropriate path specification for {\TeX} inputs.

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

  \medskip As a final step of document preparation within Isabelle,
  @{verbatim isabelle} @{tool document}~@{verbatim "-c"} is run on the
  resulting @{verbatim document} directory.  Thus the actual output
  document is built and installed in its proper place (as linked by
  the session's @{verbatim index.html} if option @{verbatim "-i"} of
  @{tool_ref usedir} has been enabled, cf.\ \secref{sec:info}).  The
  generated sources are deleted after successful run of {\LaTeX} and
  friends.  Note that a separate copy of the sources may be retained
  by passing an option @{verbatim "-D"} to the @{tool usedir} utility
  when running the session.
*}


section {* Running {\LaTeX} within the Isabelle environment
  \label{sec:tool-latex} *}

text {*
  The @{tool_def latex} utility provides the basic interface for
  Isabelle document preparation.  Its usage is:
\begin{ttbox}
Usage: latex [OPTIONS] [FILE]

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
  time by separate tools (cf.\ option @{verbatim "-D"} of the @{tool
  usedir} utility).

  The @{verbatim syms} output is for internal use; it generates lists
  of symbols that are available without loading additional {\LaTeX}
  packages.
*}


subsubsection {* Examples *}

text {*
  Invoking @{verbatim isabelle} @{tool latex} by hand may be
  occasionally useful when debugging failed attempts of the automatic
  document preparation stage of batch-mode Isabelle.  The abortive
  process leaves the sources at a certain place within @{setting
  ISABELLE_BROWSER_INFO}, see the runtime error message for details.
  This enables users to inspect {\LaTeX} runs in further detail, e.g.\
  like this:
\begin{ttbox}
  cd ~/.isabelle/IsabelleXXXX/browser_info/HOL/Test/document
  isabelle latex -o pdf
\end{ttbox}
*}

end