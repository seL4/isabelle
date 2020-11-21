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

  The command-line tools @{tool_ref mkroot} and @{tool_ref build} provide the
  primary means for managing Isabelle sessions, including options for
  presentation: ``\<^verbatim>\<open>document=pdf\<close>'' generates PDF output from the theory
  session, and ``\<^verbatim>\<open>document_output=dir\<close>'' emits a copy of the document sources
  with the PDF into the given directory (relative to the session directory).

  Alternatively, @{tool_ref document} may be used to turn the generated
  {\LaTeX} sources of a session (exports from its build database) into PDF,
  using suitable invocations of @{tool_ref latex}.
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
  The @{tool_def document} tool prepares logic session documents. Its usage
  is:
  @{verbatim [display]
\<open>Usage: isabelle document [OPTIONS] SESSION

  Options are:
    -O DIR       output directory for LaTeX sources and resulting PDF
    -P DIR       output directory for resulting PDF
    -S DIR       output directory for LaTeX sources
    -V           verbose latex
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose build

  Prepare the theory document of a session.\<close>}

  Generated {\LaTeX} sources are taken from the session build database:
  @{tool_ref build} is invoked beforehand to ensure that it is up-to-date.
  Further files are generated on the spot, notably essential Isabelle style
  files, and \<^verbatim>\<open>session.tex\<close> to input all theory sources from the session
  (excluding imports from other sessions).

  \<^medskip> Options \<^verbatim>\<open>-d\<close>, \<^verbatim>\<open>-o\<close>, \<^verbatim>\<open>-v\<close> have the same meaning as for @{tool
  build}.

  \<^medskip> Option \<^verbatim>\<open>-V\<close> prints full output of {\LaTeX} tools.

  \<^medskip> Option \<^verbatim>\<open>-O\<close>~\<open>dir\<close> specifies the output directory for generated {\LaTeX}
  sources and the result PDF file. Options \<^verbatim>\<open>-P\<close> and \<^verbatim>\<open>-S\<close> only refer to the
  PDF and sources, respectively.

  For example, for output directory ``\<^verbatim>\<open>output\<close>'' and the default document
  variant ``\<^verbatim>\<open>document\<close>'', the generated document sources are placed into the
  subdirectory \<^verbatim>\<open>output/document/\<close> and the resulting PDF into
  \<^verbatim>\<open>output/document.pdf\<close>.

  \<^medskip> Isabelle is usually smart enough to create the PDF from the given
  \<^verbatim>\<open>root.tex\<close> and optional \<^verbatim>\<open>root.bib\<close> (bibliography) and \<^verbatim>\<open>root.idx\<close> (index)
  using standard {\LaTeX} tools. Alternatively, \isakeyword{document\_files}
  in the session \<^verbatim>\<open>ROOT\<close> may include an executable \<^verbatim>\<open>build\<close> script to take
  care of that. It is invoked with command-line arguments for the document
  format (\<^verbatim>\<open>pdf\<close>) and the document variant name. The script needs to produce
  corresponding output files, e.g.\ \<^verbatim>\<open>root.pdf\<close> for default document variants
  (the main work can be delegated to @{tool latex}). \<close>

subsubsection \<open>Examples\<close>

text \<open>
  Produce the document from session \<^verbatim>\<open>FOL\<close> with full verbosity, and a copy in
  the current directory (subdirectory \<^verbatim>\<open>document\<close> and file \<^verbatim>\<open>document.pdf)\<close>:

  @{verbatim [display] \<open>isabelle document -v -V -O. FOL\<close>}
\<close>


section \<open>Running {\LaTeX} within the Isabelle environment
  \label{sec:tool-latex}\<close>

text \<open>
  The @{tool_def latex} tool provides the basic interface for Isabelle
  document preparation. Its usage is:
  @{verbatim [display]
\<open>Usage: isabelle latex [OPTIONS] [FILE]

  Options are:
    -o FORMAT    specify output format: pdf (default), bbl, idx, sty

  Run LaTeX (and related tools) on FILE (default root.tex),
  producing the specified output format.\<close>}

  Appropriate {\LaTeX}-related programs are run on the input file, according
  to the given output format: @{executable pdflatex}, @{executable bibtex}
  (for \<^verbatim>\<open>bbl\<close>), and @{executable makeindex} (for \<^verbatim>\<open>idx\<close>). The actual commands
  are determined from the settings environment (@{setting ISABELLE_PDFLATEX}
  etc.).

  The \<^verbatim>\<open>sty\<close> output format causes the Isabelle style files to be updated from
  the distribution. This is useful in special situations where the document
  sources are to be processed another time by separate tools.
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
