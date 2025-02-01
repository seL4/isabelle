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
  {\LaTeX} sources of a session (exports from its session build database) into PDF.
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

  The presentation output will appear in a sub-directory
  \<^path>\<open>$ISABELLE_BROWSER_INFO\<close>, according to the chapter and session name.

  Many Isabelle sessions (such as \<^session>\<open>HOL-Library\<close> in
  \<^dir>\<open>~~/src/HOL/Library\<close>) also provide theory documents in PDF. These are
  prepared automatically as well if enabled like this:
  @{verbatim [display] \<open>isabelle build -o browser_info -o document -v -c HOL-Library\<close>}

  Enabling both browser info and document preparation simultaneously causes an
  appropriate ``document'' link to be included in the HTML index. Documents
  may be generated independently of browser information as well, see
  \secref{sec:tool-document} for further details.

  \<^bigskip>
  The theory browsing information is stored in the directory determined by the
  @{setting_ref ISABELLE_BROWSER_INFO} setting, with sub-directory structure
  according to the chapter and session name. In order to present Isabelle
  applications on the web, the corresponding subdirectory from @{setting
  ISABELLE_BROWSER_INFO} can be put on a WWW server.
\<close>


section \<open>Creating session root directories \label{sec:tool-mkroot}\<close>

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
    -q           quiet mode: less verbosity

  Create session root directory (default: current directory).
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

  Option \<^verbatim>\<open>-q\<close> reduces verbosity.

  \<^medskip>
  The implicit Isabelle settings variable @{setting ISABELLE_LOGIC} specifies
  the parent session.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Produce session \<^verbatim>\<open>Test\<close> within a separate directory of the same name:
  @{verbatim [display] \<open>isabelle mkroot -q Test && isabelle build -D Test\<close>}

  \<^medskip>
  Upgrade the current directory into a session ROOT with document preparation,
  and build it:
  @{verbatim [display] \<open>isabelle mkroot -q && isabelle build -D .\<close>}
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
  using standard {\LaTeX} tools. Actual command-lines are given by settings
  @{setting_ref ISABELLE_LUALATEX} (or @{setting_ref ISABELLE_PDFLATEX}),
  @{setting_ref ISABELLE_BIBTEX}, @{setting_ref ISABELLE_MAKEINDEX}: these
  variables are used without quoting in shell scripts, and thus may contain
  additional options.

  The system option @{system_option_def "document_build"} specifies an
  alternative build engine, e.g. within the session \<^verbatim>\<open>ROOT\<close> file as
  ``\<^verbatim>\<open>options [document_build = pdflatex]\<close>''. The following standard engines
  are available:

    \<^item> \<^verbatim>\<open>lualatex\<close> (default) uses the shell command \<^verbatim>\<open>$ISABELLE_LUALATEX\<close> on
    the main \<^verbatim>\<open>root.tex\<close> file, with further runs of \<^verbatim>\<open>$ISABELLE_BIBTEX\<close> and
    \<^verbatim>\<open>$ISABELLE_MAKEINDEX\<close> as required.

    \<^item> \<^verbatim>\<open>pdflatex\<close> uses \<^verbatim>\<open>$ISABELLE_PDFLATEX\<close> instead of \<^verbatim>\<open>$ISABELLE_LUALATEX\<close>,
    and the other tools as above.

    \<^item> \<^verbatim>\<open>build\<close> invokes an executable script of the same name in a private
    directory containing all \isakeyword{document\_files} and other generated
    document sources. The script is invoked as ``\<^verbatim>\<open>./build pdf\<close>~\<open>name\<close>'' for
    the document variant name; it needs to produce a corresponding
    \<open>name\<close>\<^verbatim>\<open>.pdf\<close> file by arbitrary means on its own.

  Further engines can be defined by add-on components in Isabelle/Scala
  (\secref{sec:scala-build}), providing a service class derived from
  \<^scala_type>\<open>isabelle.Document_Build.Engine\<close>.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Produce the document from session \<^verbatim>\<open>FOL\<close> with full verbosity, and a copy in
  the current directory (subdirectory \<^verbatim>\<open>document\<close> and file \<^verbatim>\<open>document.pdf)\<close>:

  @{verbatim [display] \<open>isabelle document -v -V -O. FOL\<close>}
\<close>


section \<open>Full-text search for formal theory content\<close>

text \<open>
  The session information of a regular @{tool_ref build} can also be used to
  generate a search index for full-text search over formal theory content. To
  that end, the \<^verbatim>\<open>Find_Facts\<close> module integrates Apache Solr\<^footnote>\<open>\<^url>\<open>https://solr.apache.org/\<close>\<close>,
  a full-text search engine, that can run embedded in a JVM process. Solr is
  bundled as a separate Isabelle component, and its run-time dependencies 
  (as specified in  @{setting SOLR_JARS}) need to be added separately to the
  classpath of a regular Isabelle/Scala process.

  \<^medskip>
  
  A search index can be created using the @{tool_def find_facts_index} tool,
  which has options similar to the regular @{tool_ref build}. User data such
  as search indexes is stored in @{setting FIND_FACTS_HOME_USER}. The name of
  the search index can be specified via system option 
  @{system_option find_facts_database_name}. A finished search index can be
  packed for later use as a regular Isabelle component using the 
  @{tool_def find_facts_index_build} tool: Initializing such a component
  causes it to be added to the list of managed components in
  @{setting FIND_FACTS_INDEXES}.

  \<^medskip>
  The user interface of the search is available as web application that 
  can be started with the @{tool_def find_facts_server} tool. Its usage is:
  @{verbatim [display]
\<open>Usage: isabelle find_facts_server [OPTIONS]

  Options are:
    -d           devel mode
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit web server port
    -v           verbose server

  Run server for Find_Facts.
\<close>}

  This Isabelle/Scala HTTP server provides the both the front-end
  (implemented in the Elm\<^footnote>\<open>\<^url>\<open>https://elm-lang.org/\<close>\<close> language) and REST
  endpoints for search queries with JSON data.

  Options \<^verbatim>\<open>-o\<close>, \<open>-v\<close> have the same meaning as usual.

  Option \<^verbatim>\<open>-d\<close> re-compiles the front-end in \<^path>\<open>$FIND_FACTS_HOME_USER/web\<close>
  on page reload (when sources are changed).

  Option \<^verbatim>\<open>-p\<close> specifies an explicit TCP port for the server socket 
  (assigned by the operating system per default). For public-facing servers,
  a common scheme is \<^verbatim>\<open>-p 8080\<close> that is access-restricted via firewall rules,
  with a reverse proxy in system space (that also handles SSL) on ports 80 and
  443. 
\<close>

end
