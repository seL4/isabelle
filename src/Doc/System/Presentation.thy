(*:maxLineLen=78:*)

theory Presentation
imports Base
begin

chapter \<open>Presenting theories \label{ch:present}\<close>

text \<open>
  Isabelle provides several ways to present the outcome of formal
  developments, including WWW-based browsable libraries or actual printable
  documents. Presentation is centered around the concept of \<^emph>\<open>sessions\<close>
  (\chref{ch:session}). The global session structure is that of a tree, with
  Isabelle Pure at its root, further object-logics derived (e.g.\ HOLCF from
  HOL, and HOL from Pure), and application sessions further on in the
  hierarchy.

  The tools @{tool_ref mkroot} and @{tool_ref build} provide the primary means
  for managing Isabelle sessions, including proper setup for presentation;
  @{tool build} tells the Isabelle process to run any additional stages
  required for document preparation, notably the @{tool_ref document} and
  @{tool_ref latex}. The complete tool chain for managing batch-mode Isabelle
  sessions is illustrated in \figref{fig:session-tools}.

  \begin{figure}[htbp]
  \begin{center}
  \begin{tabular}{lp{0.6\textwidth}}

      @{tool_ref mkroot} & invoked once by the user to initialize the
      session \<^verbatim>\<open>ROOT\<close> with optional \<^verbatim>\<open>document\<close>
      directory; \\

      @{tool_ref build} & invoked repeatedly by the user to keep
      session output up-to-date (HTML, documents etc.); \\

      @{tool_ref process} & run through @{tool_ref build}; \\

      @{tool_ref document} & run by the Isabelle process if document
      preparation is enabled; \\

      @{tool_ref latex} & universal {\LaTeX} tool wrapper invoked
      multiple times by @{tool_ref document}; also useful for manual
      experiments; \\

  \end{tabular}
  \caption{The tool chain of Isabelle session presentation} \label{fig:session-tools}
  \end{center}
  \end{figure}
\<close>


section \<open>Generating HTML browser information \label{sec:info}\<close>

text \<open>
  As a side-effect of building sessions, Isabelle is able to generate theory
  browsing information, including HTML documents that show the theory sources
  and the relationship with its ancestors and descendants. Besides the HTML
  file that is generated for every theory, Isabelle stores links to all
  theories of a session in an index file. As a second hierarchy, groups of
  sessions are organized as \<^emph>\<open>chapters\<close>, with a separate index. Note that the
  implicit tree structure of the session build hierarchy is \<^emph>\<open>not\<close> relevant
  for the presentation.

  \<^medskip>
  To generate theory browsing information for an existing session, just invoke
  @{tool build} with suitable options:
  @{verbatim [display] \<open>isabelle build -o browser_info -v -c FOL\<close>}

  The presentation output will appear in \<^verbatim>\<open>$ISABELLE_BROWSER_INFO/FOL/FOL\<close> as
  reported by the above verbose invocation of the build process.

  Many Isabelle sessions (such as \<^session>\<open>HOL-Library\<close> in
  \<^dir>\<open>~~/src/HOL/Library\<close>) also provide printable documents in PDF. These are
  prepared automatically as well if enabled like this:
  @{verbatim [display] \<open>isabelle build -o browser_info -o document=pdf -v -c HOL-Library\<close>}

  Enabling both browser info and document preparation simultaneously causes an
  appropriate ``document'' link to be included in the HTML index. Documents
  may be generated independently of browser information as well, see
  \secref{sec:tool-document} for further details.

  \<^bigskip>
  The theory browsing information is stored in a sub-directory directory
  determined by the @{setting_ref ISABELLE_BROWSER_INFO} setting plus a prefix
  corresponding to the session chapter and identifier. In order to present
  Isabelle applications on the web, the corresponding subdirectory from
  @{setting ISABELLE_BROWSER_INFO} can be put on a WWW server.
\<close>


section \<open>Preparing session root directories \label{sec:tool-mkroot}\<close>

text \<open>
  The @{tool_def mkroot} tool configures a given directory as session root,
  with some \<^verbatim>\<open>ROOT\<close> file and optional document source directory. Its usage is:
  @{verbatim [display]
\<open>Usage: isabelle mkroot [OPTIONS] [DIRECTORY]

  Options are:
    -A LATEX     provide author in LaTeX notation (default: user name)
    -I           init Mercurial repository and add generated files
    -T LATEX     provide title in LaTeX notation (default: session name)
    -n NAME      alternative session name (default: directory base name)

  Prepare session root directory (default: current directory).
\<close>}

  The results are placed in the given directory \<open>dir\<close>, which refers to the
  current directory by default. The @{tool mkroot} tool is conservative in the
  sense that it does not overwrite existing files or directories. Earlier
  attempts to generate a session root need to be deleted manually.

  The generated session template will be accompanied by a formal document,
  with \<open>DIRECTORY\<close>\<^verbatim>\<open>/document/root.tex\<close> as its {\LaTeX} entry point (see also
  \chref{ch:present}).

  Options \<^verbatim>\<open>-T\<close> and \<^verbatim>\<open>-A\<close> specify the document title and author explicitly,
  using {\LaTeX} source notation.

  Option \<^verbatim>\<open>-I\<close> initializes a Mercurial repository in the target directory, and
  adds all generated files (without commit).

  Option \<^verbatim>\<open>-n\<close> specifies an alternative session name; otherwise the base name
  of the given directory is used.

  \<^medskip>
  The implicit Isabelle settings variable @{setting ISABELLE_LOGIC} specifies
  the parent session.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Produce session \<^verbatim>\<open>Test\<close> within a separate directory of the same name:
  @{verbatim [display] \<open>isabelle mkroot Test && isabelle build -D Test\<close>}

  \<^medskip>
  Upgrade the current directory into a session ROOT with document preparation,
  and build it:
  @{verbatim [display] \<open>isabelle mkroot && isabelle build -D .\<close>}
\<close>


section \<open>Preparing Isabelle session documents \label{sec:tool-document}\<close>

text \<open>
  The @{tool_def document} tool prepares logic session documents, processing
  the sources as provided by the user and generated by Isabelle. Its usage is:
  @{verbatim [display]
\<open>Usage: isabelle document [OPTIONS]

  Options are:
    -d DIR       document output directory (default "output/document")
    -n NAME      document name (default "document")
    -o FORMAT    document format: pdf (default), dvi
    -t TAGS      markup for tagged regions

  Prepare the theory session document in document directory, producing the
  specified output format.
\<close>}

  This tool is usually run automatically as part of the Isabelle build
  process, provided document preparation has been enabled via suitable
  options. It may be manually invoked on the generated browser information
  document output as well, e.g.\ in case of errors encountered in the batch
  run.

  \<^medskip>
  Option \<^verbatim>\<open>-d\<close> specifies an laternative document output directory. The default
  is \<^verbatim>\<open>output/document\<close> (derived from the document name). Note that the result
  will appear in the parent of this directory.

  \<^medskip>
  The \<^verbatim>\<open>-n\<close> and \<^verbatim>\<open>-o\<close> option specify the final output file name and format,
  the default is ``\<^verbatim>\<open>document.pdf\<close>''.

  \<^medskip>
  The \<^verbatim>\<open>-t\<close> option tells {\LaTeX} how to interpret tagged Isabelle command
  regions. Tags are specified as a comma separated list of modifier/name
  pairs: ``\<^verbatim>\<open>+\<close>\<open>foo\<close>'' (or just ``\<open>foo\<close>'') means to keep, ``\<^verbatim>\<open>-\<close>\<open>foo\<close>'' to
  drop, and ``\<^verbatim>\<open>/\<close>\<open>foo\<close>'' to fold text tagged as \<open>foo\<close>. The builtin default is
  equivalent to the tag specification
  ``\<^verbatim>\<open>+document,+theory,+proof,+ML,+visible,-invisible,+important,+unimportant\<close>'';
  see also the {\LaTeX} macros \<^verbatim>\<open>\isakeeptag\<close>, \<^verbatim>\<open>\isadroptag\<close>, and
  \<^verbatim>\<open>\isafoldtag\<close>, in \<^file>\<open>~~/lib/texinputs/isabelle.sty\<close>.

  \<^medskip>
  Document preparation requires a \<^verbatim>\<open>document\<close> directory within the session
  sources. This directory is supposed to contain all the files needed to
  produce the final document --- apart from the actual theories which are
  generated by Isabelle.

  \<^medskip>
  For most practical purposes, @{tool document} is smart enough to create any
  of the specified output formats, taking \<^verbatim>\<open>root.tex\<close> supplied by the user as
  a starting point. This even includes multiple runs of {\LaTeX} to
  accommodate references and bibliographies (the latter assumes \<^verbatim>\<open>root.bib\<close>
  within the same directory).

  In more complex situations, a separate \<^verbatim>\<open>build\<close> script for the document
  sources may be given. It is invoked with command-line arguments for the
  document format and the document variant name. The script needs to produce
  corresponding output files, e.g.\ \<^verbatim>\<open>root.pdf\<close> for target format \<^verbatim>\<open>pdf\<close> (and
  default variants). The main work can be again delegated to @{tool latex},
  but it is also possible to harvest generated {\LaTeX} sources and copy them
  elsewhere.

  \<^medskip>
  When running the session, Isabelle copies the content of the original
  \<^verbatim>\<open>document\<close> directory into its proper place within @{setting
  ISABELLE_BROWSER_INFO}, according to the session path and document variant.
  Then, for any processed theory \<open>A\<close> some {\LaTeX} source is generated and put
  there as \<open>A\<close>\<^verbatim>\<open>.tex\<close>. Furthermore, a list of all generated theory files is
  put into \<^verbatim>\<open>session.tex\<close>. Typically, the root {\LaTeX} file provided by the
  user would include \<^verbatim>\<open>session.tex\<close> to get a document containing all the
  theories.

  The {\LaTeX} versions of the theories require some macros defined in
  \<^file>\<open>~~/lib/texinputs/isabelle.sty\<close>. Doing \<^verbatim>\<open>\usepackage{isabelle}\<close> in
  \<^verbatim>\<open>root.tex\<close> should be fine; the underlying @{tool latex} already includes an
  appropriate path specification for {\TeX} inputs.

  If the text contains any references to Isabelle symbols (such as \<^verbatim>\<open>\<forall>\<close>) then
  \<^verbatim>\<open>isabellesym.sty\<close> should be included as well. This package contains a
  standard set of {\LaTeX} macro definitions \<^verbatim>\<open>\isasym\<close>\<open>foo\<close> corresponding to
  \<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>foo\<close>\<^verbatim>\<open>>\<close>, see @{cite "isabelle-implementation"} for a complete list
  of predefined Isabelle symbols. Users may invent further symbols as well,
  just by providing {\LaTeX} macros in a similar fashion as in
  \<^file>\<open>~~/lib/texinputs/isabellesym.sty\<close> of the Isabelle distribution.

  For proper setup of DVI and PDF documents (with hyperlinks and bookmarks),
  we recommend to include \<^file>\<open>~~/lib/texinputs/pdfsetup.sty\<close> as well.

  \<^medskip>
  As a final step of Isabelle document preparation, @{tool document} is run on
  the generated \<^verbatim>\<open>output/document\<close> directory. Thus the actual output document
  is built and installed in its proper place. The generated sources are
  deleted after successful run of {\LaTeX} and friends.

  Some care is needed if the document output location is configured
  differently, say within a directory whose content is still required
  afterwards!
\<close>


section \<open>Running {\LaTeX} within the Isabelle environment
  \label{sec:tool-latex}\<close>

text \<open>
  The @{tool_def latex} tool provides the basic interface for Isabelle
  document preparation. Its usage is:
  @{verbatim [display]
\<open>Usage: isabelle latex [OPTIONS] [FILE]

  Options are:
    -o FORMAT    specify output format: pdf (default), dvi,
                 bbl, idx, sty, syms

  Run LaTeX (and related tools) on FILE (default root.tex),
  producing the specified output format.\<close>}

  Appropriate {\LaTeX}-related programs are run on the input file, according
  to the given output format: @{executable latex}, @{executable pdflatex},
  @{executable dvips}, @{executable bibtex} (for \<^verbatim>\<open>bbl\<close>), and @{executable
  makeindex} (for \<^verbatim>\<open>idx\<close>). The actual commands are determined from the
  settings environment (@{setting ISABELLE_PDFLATEX} etc.).

  The \<^verbatim>\<open>sty\<close> output format causes the Isabelle style files to be updated from
  the distribution. This is useful in special situations where the document
  sources are to be processed another time by separate tools.

  The \<^verbatim>\<open>syms\<close> output is for internal use; it generates lists of symbols that
  are available without loading additional {\LaTeX} packages.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Invoking @{tool latex} by hand may be occasionally useful when debugging
  failed attempts of the automatic document preparation stage of batch-mode
  Isabelle. The abortive process leaves the sources at a certain place within
  @{setting ISABELLE_BROWSER_INFO}, see the runtime error message for details.
  This enables users to inspect {\LaTeX} runs in further detail, e.g.\ like
  this:

  @{verbatim [display]
\<open>cd "$(isabelle getenv -b ISABELLE_BROWSER_INFO)/Unsorted/Test/document"
isabelle latex -o pdf\<close>}
\<close>

end