(*:maxLineLen=78:*)

theory Misc
imports Base
begin

chapter \<open>Miscellaneous tools \label{ch:tools}\<close>

text \<open>
  Subsequently we describe various Isabelle related utilities, given in
  alphabetical order.
\<close>

section \<open>Building Isabelle docker images\<close>

text \<open>
  Docker\<^footnote>\<open>\<^url>\<open>https://docs.docker.com\<close>\<close> provides a self-contained environment
  for complex applications called \<^emph>\<open>container\<close>, although it does not fully
  contain the program in a strict sense of the word. This includes basic
  operating system services (usually based on Linux), shared libraries and
  other required packages. Thus Docker is a light-weight alternative to
  regular virtual machines, or a heavy-weight alternative to conventional
  self-contained applications.

  Although Isabelle can be easily run on a variety of OS environments without
  extra containment, Docker images may occasionally be useful when a
  standardized Linux environment is required, even on
  Windows\<^footnote>\<open>\<^url>\<open>https://docs.docker.com/docker-for-windows\<close>\<close> and
  macOS\<^footnote>\<open>\<^url>\<open>https://docs.docker.com/docker-for-mac\<close>\<close>. Further uses are in
  common cloud computing environments, where applications need to be submitted
  as Docker images in the first place.

  \<^medskip>
  The @{tool_def docker_build} tool builds docker images from a standard
  Isabelle application archive for Linux:

  @{verbatim [display]
\<open>Usage: isabelle docker_build [OPTIONS] APP_ARCHIVE

  Options are:
    -B NAME      base image (default "ubuntu:22.04")
    -E           set Isabelle/bin/isabelle as entrypoint
    -P NAME      additional Ubuntu package collection ("X11", "latex")
    -W DIR       working directory that is accessible to docker,
                 potentially via snap (default: ".")
    -l NAME      default logic (default ISABELLE_LOGIC="HOL")
    -n           no docker build
    -o FILE      output generated Dockerfile
    -p NAME      additional Ubuntu package
    -t TAG       docker build tag
    -v           verbose

  Build Isabelle docker image with default logic image, using a standard
  Isabelle application archive for Linux (local file or remote URL).\<close>}

  Option \<^verbatim>\<open>-E\<close> sets \<^verbatim>\<open>bin/isabelle\<close> of the contained Isabelle distribution as
  the standard entry point of the Docker image. Thus \<^verbatim>\<open>docker run\<close> will
  imitate the \<^verbatim>\<open>isabelle\<close> command-line tool (\secref{sec:isabelle-tool}) of a
  regular local installation, but it lacks proper GUI support: \<^verbatim>\<open>isabelle jedit\<close>
  will not work without further provisions. Note that the default entrypoint
  may be changed later via \<^verbatim>\<open>docker run --entrypoint="..."\<close>.

  Option \<^verbatim>\<open>-t\<close> specifies the Docker image tag: this a symbolic name within the
  local Docker name space, but also relevant for Docker
  Hub\<^footnote>\<open>\<^url>\<open>https://hub.docker.com\<close>\<close>.

  Option \<^verbatim>\<open>-l\<close> specifies the default logic image of the Isabelle distribution
  contained in the Docker environment: it will be produced by \<^verbatim>\<open>isabelle build -b\<close>
  as usual (\secref{sec:tool-build}) and stored within the image.

  \<^medskip>
  Option \<^verbatim>\<open>-B\<close> specifies the Docker image taken as starting point for the
  Isabelle installation: it needs to be a suitable version of Ubuntu Linux,
  see also \<^url>\<open>https://hub.docker.com/_/ubuntu\<close>. The default for Isabelle2024
  is \<^verbatim>\<open>ubuntu:22.04\<close>, but \<^verbatim>\<open>ubuntu:20.04\<close> and \<^verbatim>\<open>ubuntu:24.04\<close> should work as
  well. Other versions might require experimentation with the package
  selection.

  Option \<^verbatim>\<open>-p\<close> includes additional Ubuntu packages, using the terminology
  of \<^verbatim>\<open>apt-get install\<close> within the underlying Linux distribution.

  Option \<^verbatim>\<open>-P\<close> refers to high-level package collections: \<^verbatim>\<open>X11\<close> or \<^verbatim>\<open>latex\<close> as
  provided by \<^verbatim>\<open>isabelle docker_build\<close> (assuming Ubuntu 20.04/22.04/24.04
  LTS). This imposes extra weight on the resulting Docker images. Note that
  \<^verbatim>\<open>X11\<close> will only provide remote X11 support according to the modest GUI
  quality standards of the late 1990-ies.

  \<^medskip>
  Option \<^verbatim>\<open>-n\<close> suppresses the actual \<^verbatim>\<open>docker build\<close> process. Option \<^verbatim>\<open>-o\<close>
  outputs the generated \<^verbatim>\<open>Dockerfile\<close>. Both options together produce a
  Dockerfile only, which might be useful for informative purposes or other
  tools.

  Option \<^verbatim>\<open>-v\<close> disables quiet-mode of the underlying \<^verbatim>\<open>docker build\<close> process.

  \<^medskip>
  Option \<^verbatim>\<open>-W\<close> specifies an alternative work directory: it needs to be
  accessible to docker, even if this is run via Snap (e.g.\ on Ubuntu 22.04).
  The default ``\<^verbatim>\<open>.\<close>'' usually works, if this is owned by the user: the tool
  will create a fresh directory within it, and remove it afterwards.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Produce a Dockerfile (without image) from a remote Isabelle distribution:
  @{verbatim [display]
\<open>  isabelle docker_build -E -n -o Dockerfile
    https://isabelle.in.tum.de/website-Isabelle2024/dist/Isabelle2024_linux.tar.gz\<close>}

  Build a standard Isabelle Docker image from a local Isabelle distribution,
  with \<^verbatim>\<open>bin/isabelle\<close> as executable entry point:

  @{verbatim [display]
\<open>  isabelle docker_build -E -t test/isabelle:Isabelle2024 Isabelle2024_linux.tar.gz\<close>}

  Invoke the raw Isabelle/ML process within that image:
  @{verbatim [display]
\<open>  docker run test/isabelle:Isabelle2024 process -e "Session.welcome ()"\<close>}

  Invoke a Linux command-line tool within the contained Isabelle system
  environment:
  @{verbatim [display]
\<open>  docker run test/isabelle:Isabelle2024 env uname -a\<close>}
  The latter should always report a Linux operating system, even when running
  on Windows or macOS.
\<close>


section \<open>Managing Isabelle components \label{sec:tool-components}\<close>

text \<open>
  The @{tool_def components} tool manages Isabelle components:
  @{verbatim [display]
\<open>Usage: isabelle components [OPTIONS] [COMPONENTS ...]

  Options are:
    -I           init user settings
    -R URL       component repository (default $ISABELLE_COMPONENT_REPOSITORY)
    -a           resolve all missing components
    -l           list status
    -u DIR       update $ISABELLE_HOME_USER/components: add directory
    -x DIR       update $ISABELLE_HOME_USER/components: remove directory

  Resolve Isabelle components via download and installation: given COMPONENTS
  are identified via base name. Further operations manage etc/settings and
  etc/components in $ISABELLE_HOME_USER.

  ISABELLE_COMPONENT_REPOSITORY="..."
  ISABELLE_HOME_USER="..."
\<close>}

  Components are initialized as described in \secref{sec:components} in a
  permissive manner, which can mark components as ``missing''. This state is
  amended by letting @{tool "components"} download and unpack components that
  are published on the default component repository
  \<^url>\<open>https://isabelle.in.tum.de/components\<close> in particular.

  Option \<^verbatim>\<open>-R\<close> specifies an alternative component repository. Note that
  \<^verbatim>\<open>file:///\<close> URLs can be used for local directories.

  Option \<^verbatim>\<open>-a\<close> selects all missing components to be resolved. Explicit
  components may be named as command line-arguments as well. Note that
  components are uniquely identified by their base name, while the
  installation takes place in the location that was specified in the attempt
  to initialize the component before.

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> lists the current state of available and missing components
  with their location (full name) within the file-system.

  \<^medskip>
  Option \<^verbatim>\<open>-I\<close> initializes the user settings file to subscribe to the standard
  components specified in the Isabelle repository clone --- this does not make
  any sense for regular Isabelle releases. An existing file that does not
  contain a suitable line ``\<^verbatim>\<open>init_components\<close>\<open>\<dots>\<close>\<^verbatim>\<open>components/main\<close>'' needs
  to be edited according to the printed explanation.

  \<^medskip>
  Options \<^verbatim>\<open>-u\<close> and \<^verbatim>\<open>-x\<close> operate on user components listed in
  \<^path>\<open>$ISABELLE_HOME_USER/etc/components\<close>: this avoids manual editing of
  Isabelle configuration files.
\<close>


section \<open>Viewing documentation \label{sec:tool-doc}\<close>

text \<open>
  The @{tool_def doc} tool displays Isabelle documentation:
  @{verbatim [display]
\<open>Usage: isabelle doc [DOC ...]

  View Isabelle documentation.\<close>}

  If called without arguments, it lists all available documents. Each line
  starts with an identifier, followed by a short description. Any of these
  identifiers may be specified as arguments, in order to display the
  corresponding document.

  \<^medskip>
  The @{setting ISABELLE_DOCS} setting specifies the list of directories
  (separated by colons) to be scanned for documentations.
\<close>


section \<open>Shell commands within the settings environment \label{sec:tool-env}\<close>

text \<open>
  The @{tool_def env} tool is a direct wrapper for the standard
  \<^verbatim>\<open>/usr/bin/env\<close> command on POSIX systems, running within the Isabelle
  settings environment (\secref{sec:settings}).

  The command-line arguments are that of the underlying version of \<^verbatim>\<open>env\<close>. For
  example, the following invokes an instance of the GNU Bash shell within the
  Isabelle environment:
  @{verbatim [display] \<open>isabelle env bash\<close>}
\<close>


section \<open>Inspecting the settings environment \label{sec:tool-getenv}\<close>

text \<open>The Isabelle settings environment --- as provided by the
  site-default and user-specific settings files --- can be inspected
  with the @{tool_def getenv} tool:
  @{verbatim [display]
\<open>Usage: isabelle getenv [OPTIONS] [VARNAMES ...]

  Options are:
    -a           display complete environment
    -b           print values only (doesn't work for -a)
    -d FILE      dump complete environment to file (NUL terminated entries)

  Get value of VARNAMES from the Isabelle settings.\<close>}

  With the \<^verbatim>\<open>-a\<close> option, one may inspect the full process environment that
  Isabelle related programs are run in. This usually contains much more
  variables than are actually Isabelle settings. Normally, output is a list of
  lines of the form \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close>. The \<^verbatim>\<open>-b\<close> option causes only the values
  to be printed.

  Option \<^verbatim>\<open>-d\<close> produces a dump of the complete environment to the specified
  file. Entries are terminated by the ASCII NUL character, i.e.\ the string
  terminator in C. Thus the Isabelle/Scala operation
  \<^scala_method>\<open>isabelle.Isabelle_System.init\<close> can import the settings
  environment robustly, and provide its own
  \<^scala_method>\<open>isabelle.Isabelle_System.getenv\<close> function.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Get the location of @{setting ISABELLE_HOME_USER} where user-specific
  information is stored:
  @{verbatim [display] \<open>isabelle getenv ISABELLE_HOME_USER\<close>}

  \<^medskip>
  Get the value only of the same settings variable, which is particularly
  useful in shell scripts:
  @{verbatim [display] \<open>isabelle getenv -b ISABELLE_HOME_USER\<close>}
\<close>


section \<open>Mercurial repository setup \label{sec:hg-setup}\<close>

text \<open>
  The @{tool_def hg_setup} tool simplifies the setup of Mercurial
  repositories, with hosting via Phabricator (\chref{ch:phabricator}) or SSH
  file server access.

  @{verbatim [display]
\<open>Usage: isabelle hg_setup [OPTIONS] REMOTE LOCAL_DIR

  Options are:
    -n NAME      remote repository name (default: base name of LOCAL_DIR)
    -p PATH      Mercurial path name (default: "default")
    -r           assume that remote repository already exists

  Setup a remote vs. local Mercurial repository: REMOTE either refers to a
  Phabricator server "user@host" or SSH file server "ssh://user@host/path".\<close>}

  The \<^verbatim>\<open>REMOTE\<close> repository specification \<^emph>\<open>excludes\<close> the actual repository
  name: that is given by the base name of \<^verbatim>\<open>LOCAL_DIR\<close>, or via option \<^verbatim>\<open>-n\<close>.

  By default, both sides of the repository are created on demand by default.
  In contrast, option \<^verbatim>\<open>-r\<close> assumes that the remote repository already exists:
  it avoids accidental creation of a persistent repository with unintended
  name.

  The local \<^verbatim>\<open>.hg/hgrc\<close> file is changed to refer to the remote repository,
  usually via the symbolic path name ``\<^verbatim>\<open>default\<close>''; option \<^verbatim>\<open>-p\<close> allows to
  provide a different name.
\<close>

subsubsection \<open>Examples\<close>

text \<open>
  Setup the current directory as a repository with Phabricator server hosting:
  @{verbatim [display] \<open>  isabelle hg_setup vcs@vcs.example.org .\<close>}

  \<^medskip>
  Setup the current directory as a repository with plain SSH server hosting:
  @{verbatim [display] \<open>  isabelle hg_setup ssh://files.example.org/data/repositories .\<close>}

  \<^medskip>
  Both variants require SSH access to the target server, via public key
  without password.
\<close>


section \<open>Mercurial repository synchronization \label{sec:tool-hg-sync}\<close>

text \<open>
  The @{tool_def hg_sync} tool synchronizes a local Mercurial repository with
  a target directory.

  @{verbatim [display]
\<open>Usage: isabelle hg_sync [OPTIONS] TARGET

  Options are:
    -F RULE      add rsync filter RULE
                 (e.g. "protect /foo" to avoid deletion)
    -R ROOT      explicit repository root directory
                 (default: implicit from current directory)
    -T           thorough treatment of file content and directory times
    -n           no changes: dry-run
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit SSH port
    -r REV       explicit revision (default: state of working directory)
    -s HOST      SSH host name for remote target (default: local)
    -u USER      explicit SSH user name
    -v           verbose

  Synchronize Mercurial repository with TARGET directory,
  which can be local or remote (see options -s -p -u).\<close>}

  The \<^verbatim>\<open>TARGET\<close> specifies a directory, which can be local or an a remote SSH
  host; the latter requires option \<^verbatim>\<open>-s\<close> for the host name. The content is
  written directly into the target, \<^emph>\<open>without\<close> creating a separate
  sub-directory. The special sub-directory \<^verbatim>\<open>.hg_sync\<close> within the target
  contains meta data from the original Mercurial repository. Repeated
  synchronization is guarded by the presence of a \<^verbatim>\<open>.hg_sync\<close> sub-directory:
  this sanity check prevents accidental changes (or deletion!) of targets that
  were not created by @{tool hg_sync}.

  \<^medskip> Option \<^verbatim>\<open>-r\<close> specifies an explicit revision of the repository; the default
  is the current state of the working directory (which might be uncommitted).

  \<^medskip> Option \<^verbatim>\<open>-v\<close> enables verbose mode. Option \<^verbatim>\<open>-n\<close> enables ``dry-run'' mode:
  operations are only simulated; use it with option \<^verbatim>\<open>-v\<close> to actually see
  results.

  \<^medskip> Option \<^verbatim>\<open>-F\<close> adds a filter rule to the underlying \<^verbatim>\<open>rsync\<close> command;
  multiple \<^verbatim>\<open>-F\<close> options may be given to accumulate a list of rules.

  \<^medskip> Option \<^verbatim>\<open>-R\<close> specifies an explicit repository root directory. The default
  is to derive it from the current directory, searching upwards until a
  suitable \<^verbatim>\<open>.hg\<close> directory is found.

  \<^medskip> Option \<^verbatim>\<open>-T\<close> indicates thorough treatment of file content and directory
  times. The default is to consider files with equal time and size already as
  equal, and to ignore time stamps on directories.

  \<^medskip> Options \<^verbatim>\<open>-s\<close>, \<^verbatim>\<open>-p\<close>, \<^verbatim>\<open>-u\<close> specify the SSH connection precisely. If no
  SSH host name is given, the local file-system is used. An explicit port and
  user are only required in special situations.

  \<^medskip> Option \<^verbatim>\<open>-p\<close> specifies an explicit port for the SSH connection underlying
  \<^verbatim>\<open>rsync\<close>; the default is taken from the user's \<^path>\<open>ssh_config\<close> file.
\<close>

subsubsection \<open>Examples\<close>

text \<open>
  Synchronize the current repository onto a remote host, with accurate
  treatment of all content:
  @{verbatim [display] \<open>  isabelle hg_sync -T -s remotename test/repos\<close>}
\<close>


section \<open>Installing standalone Isabelle executables \label{sec:tool-install}\<close>

text \<open>
  By default, the main Isabelle binaries (@{executable "isabelle"} etc.) are
  just run from their location within the distribution directory, probably
  indirectly by the shell through its @{setting PATH}. Other schemes of
  installation are supported by the @{tool_def install} tool:
  @{verbatim [display]
\<open>Usage: isabelle install [OPTIONS] BINDIR

  Options are:
    -d DISTDIR   refer to DISTDIR as Isabelle distribution
                 (default ISABELLE_HOME)

  Install Isabelle executables with absolute references to the
  distribution directory.\<close>}

  The \<^verbatim>\<open>-d\<close> option overrides the current Isabelle distribution directory as
  determined by @{setting ISABELLE_HOME}.

  The \<open>BINDIR\<close> argument tells where executable wrapper scripts for
  @{executable "isabelle"} and @{executable isabelle_java} should be
  placed, which is typically a directory in the shell's @{setting PATH}, such
  as \<^verbatim>\<open>$HOME/bin\<close>.

  \<^medskip>
  It is also possible to make symbolic links of the main Isabelle executables
  manually, but making separate copies outside the Isabelle distribution
  directory will not work!
\<close>


section \<open>Creating instances of the Isabelle logo\<close>

text \<open>
  The @{tool_def logo} tool creates variants of the Isabelle logo, for
  inclusion in PDF{\LaTeX} documents.

  @{verbatim [display]
\<open>Usage: isabelle logo [OPTIONS] [NAME]

  Options are:
    -o FILE      alternative output file
    -q           quiet mode

  Create variant NAME of the Isabelle logo as "isabelle_name.pdf".\<close>}

  Option \<^verbatim>\<open>-o\<close> provides an alternative output file, instead of the default in
  the current directory: \<^verbatim>\<open>isabelle_\<close>\<open>name\<close>\<^verbatim>\<open>.pdf\<close> with the lower-case version
  of the given name.

  \<^medskip>
  Option \<^verbatim>\<open>-q\<close> omits printing of the resulting output file name.

  \<^medskip>
  Implementors of Isabelle tools and applications are encouraged to make
  derived Isabelle logos for their own projects using this template. The
  license is the same as for the regular Isabelle distribution (BSD).
\<close>


section \<open>Output the version identifier of the Isabelle distribution\<close>

text \<open>
  The @{tool_def version} tool displays Isabelle version information:
  @{verbatim [display]
\<open>Usage: isabelle version [OPTIONS]

  Options are:
    -i           short identification (derived from Mercurial id)
    -t           symbolic tags (derived from Mercurial id)

  Display Isabelle version information.\<close>}

  \<^medskip>
  The default is to output the Isabelle distribution name, e.g.\
  ``\<^verbatim>\<open>Isabelle2024\<close>''.

  \<^medskip>
  Option \<^verbatim>\<open>-i\<close> produces a short identification derived from the Mercurial id
  of the @{setting ISABELLE_HOME} directory; option \<^verbatim>\<open>-t\<close> prints version tags
  (if available).

  These options require either a repository clone or a repository archive
  (e.g. download of
  \<^url>\<open>https://isabelle.sketis.net/repos/isabelle/archive/tip.tar.gz\<close>).
\<close>


section \<open>Managed installations of \<^text>\<open>Haskell\<close> and \<^text>\<open>OCaml\<close>\<close>

text \<open>
  Code generated in Isabelle \<^cite>\<open>"Haftmann-codegen"\<close> for \<^text>\<open>SML\<close>
  or \<^text>\<open>Scala\<close> integrates easily using Isabelle/ML or Isabelle/Scala
  respectively.

  To facilitate integration with further target languages, there are
  tools to provide managed installations of the required ecosystems:

  \<^item> Tool @{tool_def ghc_setup} provides a basic \<^text>\<open>Haskell\<close> \<^cite>\<open>"Thompson-Haskell"\<close> environment
    consisting of the Glasgow Haskell Compiler and the Haskell Tool Stack.

  \<^item> Tool @{tool_def ghc_stack} provides an interface to that \<^text>\<open>Haskell\<close>
    environment; use \<^verbatim>\<open>isabelle ghc_stack --help\<close> for elementary
    instructions.

  \<^item> Tool @{tool_def ocaml_setup} provides a basic \<^text>\<open>OCaml\<close> \<^cite>\<open>OCaml\<close> environment
    consisting of the OCaml compiler and the OCaml Package Manager.

  \<^item> Tool @{tool_def ocaml_opam} provides an interface to that \<^text>\<open>OCaml\<close>
    environment; use \<^verbatim>\<open>isabelle ocaml_opam --help\<close> for elementary
    instructions.
\<close>

end
