(*:maxLineLen=78:*)

theory Server
imports Base
begin

chapter \<open>The Isabelle server\<close>

text \<open>
  An Isabelle session requires at least two processes, which are both rather
  heavy: Isabelle/Scala for the system infrastructure and Isabelle/ML for the
  logic session (e.g.\ HOL). In principle, these processes can be invoked
  directly on the command-line, e.g.\ via @{tool java}, @{tool scala}, @{tool
  process}, @{tool console}, but this approach is inadequate for reactive
  applications that require quick responses from the prover.

  In contrast, the Isabelle server exposes Isabelle/Scala as a
  ``terminate-stay-resident'' application that manages multiple logic
  \<^emph>\<open>sessions\<close> and concurrent tasks to use \<^emph>\<open>theories\<close>. This provides an
  analogous to @{ML Thy_Info.use_theories} in Isabelle/ML, but with full
  concurrency and Isabelle/PIDE markup.

  The client/server arrangement via TCP sockets also opens possibilities for
  remote Isabelle services that are accessed by local applications, e.g.\ via
  an SSH tunnel.
\<close>


section \<open>Command-line tools\<close>

subsection \<open>Server \label{sec:tool-server}\<close>

text \<open>
  The @{tool_def server} tool manages resident server processes:
  @{verbatim [display]
\<open>Usage: isabelle server [OPTIONS]

  Options are:
    -L FILE      logging on FILE
    -c           console interaction with specified server
    -l           list servers (alternative operation)
    -n NAME      explicit server name (default: isabelle)
    -p PORT      explicit server port
    -s           assume existing server, no implicit startup
    -x           exit specified server (alternative operation)

  Manage resident Isabelle servers.\<close>}

  The main operation of \<^verbatim>\<open>isabelle server\<close> is to ensure that a named server is
  running, either by finding an already running process (according to the
  central database file @{path "$ISABELLE_HOME_USER/servers.db"}) or by
  becoming itself a new server that accepts connections on a particular TCP
  socket. The server name and its address are printed as initial output line.
  If another server instance is already running, the current
  \<^verbatim>\<open>isabelle server\<close> process will terminate; otherwise, it keeps running as a
  new server process until an explicit \<^verbatim>\<open>shutdown\<close> command is received.
  Further details of the server socket protocol are explained in
  \secref{sec:server-protocol}.

  Other server management operations are invoked via options \<^verbatim>\<open>-l\<close> and \<^verbatim>\<open>-x\<close>
  (see below).

  \<^medskip>
  Option \<^verbatim>\<open>-n\<close> specifies an alternative server name: at most one process for
  each name may run, but each server instance supports multiple connections
  and logic sessions.

  \<^medskip>
  Option \<^verbatim>\<open>-p\<close> specifies an explicit TCP port for the server socket (which is
  always on \<^verbatim>\<open>localhost\<close>): the default is to let the operating system assign a
  free port number.

  \<^medskip>
  Option \<^verbatim>\<open>-s\<close> strictly assumes that the specified server process is already
  running, skipping the optional server startup phase.

  \<^medskip>
  Option \<^verbatim>\<open>-c\<close> connects the console in/out channels after the initial check
  for a suitable server process. Note that the @{tool client} tool
  (\secref{sec:tool-client}) provides a more convenient way to do this
  interactively, together with command-line editor support.

  \<^medskip>
  Option \<^verbatim>\<open>-l\<close> lists all active server processes with their connection
  details.

  \<^medskip>
  Option \<^verbatim>\<open>-x\<close> exits the specified server process by sending it a \<^verbatim>\<open>shutdown\<close>
  command.

  \<^medskip>
  Option \<^verbatim>\<open>-L\<close> specifies a log file for exceptional output of internal server
  and session operations.
\<close>


subsection \<open>Client \label{sec:tool-client}\<close>

text \<open>
  The @{tool_def client} provides console interaction for Isabelle servers:
  @{verbatim [display]
\<open>Usage: isabelle client [OPTIONS]

  Options are:
    -n NAME      explicit server name
    -p PORT      explicit server port

  Console interaction for Isabelle server (with line-editor).\<close>}

  This is a convenient wrapper to \<^verbatim>\<open>isabelle server -s -c\<close> for interactive
  experimentation, wrapped into @{setting ISABELLE_LINE_EDITOR} if available.
  The server name is sufficient for identification, as the client can
  determine the connection details from the local database of active servers.

  \<^medskip>
  Option \<^verbatim>\<open>-n\<close> specifies an explicit server name as in @{tool server}.

  \<^medskip>
  Option \<^verbatim>\<open>-p\<close> specifies an explicit server port as in @{tool server}.
\<close>


subsection \<open>Examples\<close>

text \<open>
  Ensure that a particular server instance is running in the background:
  @{verbatim [display] \<open>isabelle server -n test &\<close>}

  Here the first line of output presents the connection details:\<^footnote>\<open>This
  information may be used in an independent TCP client, while the
  Isabelle/Scala tool merely needs the server name to access the database of
  servers.\<close>
  @{verbatim [display] \<open>server "test" = 127.0.0.1:4711 (password "XYZ")\<close>}

  \<^medskip>
  List available server processes:
  @{verbatim [display] \<open>isabelle server -l\<close>}

  \<^medskip>
  Connect the command-line client to the above test server:
  @{verbatim [display] \<open>isabelle client -n test\<close>}

  Interaction now works on a line-by-line basis, with commands like \<^verbatim>\<open>help\<close> or
  \<^verbatim>\<open>echo\<close>. For example, some JSON values may be echoed like this:

  @{verbatim [display]
\<open>echo 42
echo [1, 2, 3]
echo {"a": "text", "b": true, "c": 42}\<close>}

  Closing the connection (via CTRL-D) leaves the server running: it is
  possible to reconnect again, and have multiple connections at the same time.

  \<^medskip>
  Finally, exit the named server on the command-line:
  @{verbatim [display] \<open>isabelle server -n test -x\<close>}
\<close>


section \<open>Protocol messages \label{sec:server-protocol}\<close>

text \<open>
  The Isabelle server listens on a regular TCP socket, using a line-oriented
  protocol of structured messages: input \<^emph>\<open>commands\<close> and output \<^emph>\<open>results\<close>
  (via \<^verbatim>\<open>OK\<close> or \<^verbatim>\<open>ERROR\<close>) are strictly alternating on the toplevel, but
  commands may also return a \<^emph>\<open>task\<close> identifier to indicate an ongoing
  asynchronous process that is joined later (via \<^verbatim>\<open>FINISHED\<close> or \<^verbatim>\<open>FAILED\<close>).
  Asynchronous \<^verbatim>\<open>NOTE\<close> messages may occur at any time: they are independent of
  the main command-reply protocol.

  For example, the synchronous \<^verbatim>\<open>echo\<close> command immediately returns its
  argument as \<^verbatim>\<open>OK\<close> result. In contrast, the asynchronous \<^verbatim>\<open>session_build\<close>
  command returns \<^verbatim>\<open>OK {"task":\<close>\<open>id\<close>\<^verbatim>\<open>}\<close> and continues in the background. It
  will eventually produce \<^verbatim>\<open>FINISHED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> or
  \<^verbatim>\<open>FAILED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> with the final result. Intermediately, it
  may emit asynchronous messages of the form \<^verbatim>\<open>NOTE {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close>
  to inform about its progress. Due to the explicit task identifier, the
  client can show these messages in the proper context, e.g.\ a GUI window for
  the session build job.

  \medskip Subsequently, the protocol message formats are described in further
  detail.
\<close>


subsection \<open>Byte messages\<close>

text \<open>
  The client-server connection is a raw byte-channel for bidirectional
  communication, but the Isabelle server always works with messages of a
  particular length. Messages are written as a single chunk that is flushed
  immediately.

  The message boundary is determined as follows:

    \<^item> A \<^emph>\<open>short message\<close> consists of a single line: it is a sequence of
    arbitrary bytes excluding CR (13) and LF (10), and terminated by CR-LF or
    just LF.

    \<^item> A \<^emph>\<open>long message\<close> starts with a single line as above, which consists
    only of decimal digits: that is interpreted as length of the subsequent
    block of arbitrary bytes. A final line-terminator may be included here,
    but is not required.

  Messages in JSON format (see below) always fit on a single line, due to
  escaping of newline characters within string literals. This is convenient
  for interactive experimentation, but it can impact performance for very long
  messages. If the message byte-length is given on the preceding line, the
  server can read the message efficiently as a single block.
\<close>


subsection \<open>Text messages\<close>

text \<open>
  Messages are read and written as byte streams (with byte lengths), but the
  content is always interpreted as plain text in terms of the UTF-8
  encoding.\<^footnote>\<open>See also the ``UTF-8 Everywhere Manifesto''
  \<^url>\<open>http://utf8everywhere.org\<close>.\<close>

  Note that line-endings and other formatting characters are invariant wrt.
  UTF-8 representation of text: thus implementations are free to determine the
  overall message structure before or after applying the text encoding.
\<close>


subsection \<open>Input and output messages\<close>

text \<open>
  Server input and output messages have a uniform format as follows:

    \<^item> \<open>name argument\<close> such that:

    \<^item> \<open>name\<close> is the longest prefix consisting of ASCII letters, digits,
    ``\<^verbatim>\<open>_\<close>'' (underscore), or ``\<^verbatim>\<open>.\<close>'' (dot),

    \<^item> the separator between \<open>name\<close> and \<open>argument\<close> is the longest possible
    sequence of ASCII blanks (it could be empty, e.g.\ when the argument
    starts with a quote or bracket),

    \<^item> \<open>argument\<close> is the rest of the message without the line terminator.

  \<^medskip>
  Input messages are sent from the client to the server. Here the \<open>name\<close>
  specifies a \<^emph>\<open>server command\<close>: the list of known commands may be
  retrieved via the \<^verbatim>\<open>help\<close> command.

  \<^medskip>
  Output messages are sent from the server to the client. Here the \<open>name\<close>
  specifies the \<^emph>\<open>server reply\<close>, which always has a specific meaning as
  follows:

    \<^item> synchronous results: \<^verbatim>\<open>OK\<close> or \<^verbatim>\<open>ERROR\<close>
    \<^item> asynchronous results: \<^verbatim>\<open>FINISHED\<close> or \<^verbatim>\<open>FAILED\<close>
    \<^item> intermediate notifications: \<^verbatim>\<open>NOTE\<close>

  \<^medskip>
  The \<open>argument\<close> format is uniform for both input and output messages:

    \<^item> empty argument (Scala type \<^verbatim>\<open>Unit\<close>)
    \<^item> XML element in YXML notation (Scala type \<^verbatim>\<open>XML.Elem\<close>)
    \<^item> JSON value (Scala type \<^verbatim>\<open>JSON.T\<close>)

  JSON values may consist of objects (records), arrays (lists), strings,
  numbers, bools, null.\<^footnote>\<open>See also the official specification
  \<^url>\<open>https://www.json.org\<close> and unofficial explorations ``Parsing JSON is a
  Minefield'' \<^url>\<open>http://seriot.ch/parsing_json.php\<close>.\<close> Since JSON requires
  explicit quotes and backslash-escapes to represent arbitrary text, the YXML
  notation for XML trees (\secref{sec:yxml-vs-xml}) works better
  for large messages with a lot of PIDE markup.

  Nonetheless, the most common commands use JSON by default: big chunks of
  text (theory sources etc.) are taken from the underlying file-system and
  results are pre-formatted for plain-text output, without PIDE markup
  information. This is a concession to simplicity: the server imitates the
  appearance of command-line tools on top of the Isabelle/PIDE infrastructure.
\<close>


subsection \<open>Initial password exchange\<close>

text \<open>
  Whenever a new client opens the server socket, the initial message needs to
  be its unique password. The server replies either with \<^verbatim>\<open>OK\<close> (and some
  information about the Isabelle version) or by silent disconnection of what
  is considered an illegal connection attempt.

  Server passwords are created as Universally Unique Identifier (UUID) in
  Isabelle/Scala and stored in a per-user database, with restricted
  file-system access only for the current user. The Isabelle/Scala server
  implementation is careful to expose the password only on private output
  channels, and not on a process command-line (which is accessible to other
  users, e.g.\ via the \<^verbatim>\<open>ps\<close> command).
\<close>


subsection \<open>Synchronous commands\<close>

text \<open>
  A \<^emph>\<open>synchronous command\<close> corresponds to regular function application in
  Isabelle/Scala, with single argument and result (regular or error). Both the
  argument and the result may consist of type \<^verbatim>\<open>Unit\<close>, \<^verbatim>\<open>XML.Elem\<close>, \<^verbatim>\<open>JSON.T\<close>.
  An error result typically consists of a JSON object with error message and
  potentially further fields (this resembles exceptions in Scala).

  These are the protocol exchanges for both cases of command execution:
  \begin{center}
  \begin{tabular}{rl}
  \<^bold>\<open>input:\<close> & \<open>command argument\<close> \\
  (a) regular \<^bold>\<open>output:\<close> & \<^verbatim>\<open>OK\<close> \<open>result\<close> \\
  (b) error \<^bold>\<open>output:\<close> & \<^verbatim>\<open>ERROR\<close> \<open>result\<close> \\
  \end{tabular}
  \end{center}
\<close>


subsection \<open>Asynchronous commands\<close>

text \<open>
  An \<^emph>\<open>asynchronous command\<close> corresponds to an ongoing process that finishes
  or fails eventually, while emitting arbitrary notifications intermediately.
  Formally, it starts as synchronous command with immediate result \<^verbatim>\<open>OK\<close> and
  the \<^verbatim>\<open>task\<close> identifier, or an immediate \<^verbatim>\<open>ERROR\<close> that indicates bad command
  syntax. For a running task, the termination is indicated later by
  \<^verbatim>\<open>FINISHED\<close> or \<^verbatim>\<open>FAILED\<close>, together with its ultimate result.

  These are the protocol exchanges for various cases of command task
  execution:

  \begin{center}
  \begin{tabular}{rl}
  \<^bold>\<open>input:\<close> & \<open>command argument\<close> \\
  immediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>OK {"task":\<close>\<open>id\<close>\<^verbatim>\<open>}\<close> \\
  intermediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>NOTE {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\
  intermediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>NOTE {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\
  (a) regular \<^bold>\<open>output:\<close> & \<^verbatim>\<open>FINISHED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\
  (b) error \<^bold>\<open>output:\<close> & \<^verbatim>\<open>FAILED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\[3ex]
  \<^bold>\<open>input:\<close> & \<open>command argument\<close> \\
  immediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>ERROR\<close>~\<open>\<dots>\<close> \\
  \end{tabular}
  \end{center}

  All asynchronous messages are decorated with the task identifier that was
  revealed in the immediate (synchronous) result. Thus it is possible to emit
  further asynchronous commands and dispatch the mingled stream of
  asynchronous messages properly.

  The synchronous command \<^verbatim>\<open>cancel\<close>~\<open>id\<close> tells the specified task to terminate
  prematurely: usually causing a \<^verbatim>\<open>FAILED\<close> result with error message
  \<^verbatim>\<open>Interrupt\<close>, but this is not guaranteed: the cancel event may come too
  late or the task may just ignore it.
\<close>

end
