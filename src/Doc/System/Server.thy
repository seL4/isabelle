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


subsection \<open>Input and output messages \label{sec:input-output-messages}\<close>

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
  prematurely: usually causing a \<^verbatim>\<open>FAILED\<close> result, but this is not guaranteed:
  the cancel event may come too late or the task may just ignore it.
\<close>


section \<open>Server commands and results\<close>

text \<open>
  Here follows an overview of particular Isabelle server commands with their
  results, which are usually represented as JSON values. The general format of
  input and output messages is described in
  \secref{sec:input-output-messages}. The relevant Isabelle/Scala source files
  are:

  \<^medskip>
  \begin{tabular}{l}
  \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/server_commands.scala\<close> \\
  \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/server.scala\<close>
  \end{tabular}
\<close>


subsection \<open>Types for JSON values\<close>

text \<open>
  In order to specify concrete JSON types for command arguments and result
  messages, the following type definition language shall be used:

  \<^rail>\<open>
    @{syntax type_def}: @'type' @{syntax name} '=' @{syntax type}
    ;
    @{syntax type}: @{syntax name} | @{syntax value} | 'any' | 'null' |
      'bool' | 'int' | 'long' | 'double' | 'string' | '[' @{syntax type} ']' |
      '{' (@{syntax field_type} ',' *) '}' |
      @{syntax type} '\<oplus>' @{syntax type} |
      @{syntax type} '|' @{syntax type}
    ;
    @{syntax field_type}: @{syntax name} ('?'?) ':' @{syntax type}
  \<close>

  This is a simplified version of interfaces in
  TypeScript.\<^footnote>\<open>\<^url>\<open>https://www.typescriptlang.org/docs/handbook/interfaces.html\<close>\<close>
  The meaning of these types is specified wrt. the implementation in
  Isabelle/Scala as follows.

  \<^item> A \<open>name\<close> refers to a type defined elsewhere. The environment of type
  definitions is given informally: put into proper foundational order, it
  needs to specify a strongly normalizing system; type definitions may not be
  recursive.

  \<^item> A \<open>value\<close> in JSON notation represents the singleton type of the given
  item. For example, the string \<^verbatim>\<open>"error"\<close> can be used is the type for a slot
  that is guaranteed to contain that constant.

  \<^item> Type \<open>any\<close> is the super type of all other types: it is an untyped slot in
  the specification and corresponds to \<^verbatim>\<open>Any\<close> or \<^verbatim>\<open>JSON.T\<close> in Isabelle/Scala.

  \<^item> Type \<open>null\<close> is the type of the improper value \<open>null\<close>; it corresponds to
  type \<^verbatim>\<open>Null\<close> in Scala and is normally not used in Isabelle/Scala.\<^footnote>\<open>See also
  ``Null References: The Billion Dollar Mistake'' by Tony Hoare
  \<^url>\<open>https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare\<close>.\<close>

  \<^item> Type \<open>bool\<close> is the type of the truth values \<open>true\<close> and \<open>false\<close>; it
  corresponds to \<^verbatim>\<open>Boolean\<close> in Scala.

  \<^item> Types \<open>int\<close>, \<open>long\<close>, \<open>double\<close> are specific versions of the generic
  \<open>number\<close> type, corresponding to \<^verbatim>\<open>Int\<close>, \<^verbatim>\<open>Long\<close>, \<^verbatim>\<open>Double\<close> in Scala, but
  \<^verbatim>\<open>Long\<close> is limited to 53 bit precision.\<^footnote>\<open>Implementations of JSON typically
  standardize \<open>number\<close> to \<^verbatim>\<open>Double\<close>, which can absorb \<^verbatim>\<open>Int\<close> faithfully, but
  not all of \<^verbatim>\<open>Long\<close>.\<close>

  \<^item> Type \<open>string\<close> represents Unicode text; it corresponds to type \<^verbatim>\<open>String\<close> in
  Scala.

  \<^item> Type \<open>[t]\<close> is the array (or list) type over \<open>t\<close>; it corresponds to
  \<^verbatim>\<open>List[t]\<close> in Scala. The list type is co-variant as usual (i.e.\ monotonic
  wrt. the subtype order).

  \<^item> Object types describe the possible content of JSON records, with field
  names and types. A question mark after a field name means that it is
  optional: in Scala this could refer to an explicit type \<^verbatim>\<open>Option[t]\<close>. For
  example, \<open>{a: int, b?: string}\<close> corresponds to a Scala case class with
  arguments \<^verbatim>\<open>a: Int\<close>, \<^verbatim>\<open>b: Option[String]\<close>.

  Alternatively, optional fields can have a default value. If nothing else is
  specified, the standard default value is the ``empty'' value of a type,
  i.e.\ \<^verbatim>\<open>0\<close> for the number types, \<^verbatim>\<open>false\<close> for \<open>bool\<close>, or the empty string,
  array, object etc.

  Object types are \<^emph>\<open>permissive\<close> in the sense that only the specified field
  names need to conform to the given types, but unspecified fields may be
  present as well.

  \<^item> The type expression \<open>t\<^sub>1 \<oplus> t\<^sub>2\<close> only works for two object types with
  disjoint field names: it is the concatenation of the respective @{syntax
  field_type} specifications taken together. For example: \<open>{task: string} \<oplus>
  {ok: bool}\<close> is the equivalent to \<open>{task: string, ok: bool}\<close>.

  \<^item> The type expression \<open>t\<^sub>1 | t\<^sub>2\<close> is the disjoint union of two types, either
  one of the two cases may occur.


  These types correspond to JSON values in an obvious manner, which is not
  further described here. For example, the JSON array \<^verbatim>\<open>[1, 2, 3]\<close> conforms to
  types \<open>[int]\<close>, \<open>[long]\<close>, \<open>[double]\<close>, \<open>[any]\<close>, \<open>any\<close>.

  Note that JSON objects require field names to be quoted, but the type
  language omits quotes for clarity. Thus \<^verbatim>\<open>{"a": 42, "b": "xyz"}\<close> conforms to
  the type \<open>{a: int, b: string}\<close>, for example.

  \<^medskip>
  The absence of an argument or result is represented by type \<^verbatim>\<open>Unit\<close> in
  Isabelle/Scala: it is written as empty text in the message \<open>argument\<close>
  (\secref{sec:input-output-messages}). This is not part of the JSON language.

  Server replies have name tags like \<^verbatim>\<open>OK\<close>, \<^verbatim>\<open>ERROR\<close>: these are used literally
  together with type specifications to indicate the particular name with the
  type of its argument, e.g.\ \<^verbatim>\<open>OK\<close>~\<open>[string]\<close> for a regular result that is a
  list (JSON array) of strings.

  \<^bigskip>
  Here are some common type definitions, for use in the subsequent
  specifications of command arguments and results.

  \<^item> \<^bold>\<open>type\<close>~\<open>position = {line?: int, offset?: int, end_offset?: int, file?:
  string, id?: long}\<close> describes a source position within Isabelle source text.
  Only the \<open>line\<close> and \<open>file\<close> fields make immediate sense to external programs.
  Detailed \<open>offset\<close> and \<open>end_offset\<close> positions are counted according to
  Isabelle symbols, see @{ML_type Symbol.symbol} in Isabelle/ML @{cite
  "isabelle-implementation"}. The position \<open>id\<close> belongs to the internal
  representation of command transactions in the Isabelle/PIDE protocol.

  \<^item> \<^bold>\<open>type\<close>~\<open>message = {kind?: string, message: string, pos?: position}\<close> where
  the \<open>kind\<close> provides some hint about the role and importance of the message.
  The main message kinds are \<^verbatim>\<open>writeln\<close> (for regular output), \<^verbatim>\<open>warning\<close>, and
  \<^verbatim>\<open>error\<close>. The table \<^verbatim>\<open>Markup.messages\<close> in Isabelle/Scala defines further
  message kinds for more specific applications.

  \<^item> \<^bold>\<open>type\<close>~\<open>error_message = {kind:\<close>~\<^verbatim>\<open>"error"\<close>\<open>, message: string}\<close> refers to
  error messages in particular. These occur routinely with \<^verbatim>\<open>ERROR\<close> or
  \<^verbatim>\<open>FAILED\<close> replies, but also as initial command syntax errors (which are
  omitted in the command specifications below).

  \<^item> \<^bold>\<open>type\<close>~\<open>theory_progress = {kind:\<close>~\<^verbatim>\<open>"writeln"\<close>\<open>, message: string, theory:
  string, session: string}\<close> reports formal progress in loading theories (e.g.\
  when building a session image). Apart from a regular output message, it also
  reveals the formal theory name (e.g.\ \<^verbatim>\<open>HOL.Nat\<close>) and session name (e.g.\
  \<^verbatim>\<open>HOL\<close>). Note that some rare theory names lack a proper session prefix, e.g.
  theory \<^verbatim>\<open>Main\<close> in session \<^verbatim>\<open>HOL\<close>.

  \<^item> \<^bold>\<open>type\<close>~\<open>timing = {elapsed: double, cpu: double, gc: double}\<close> refers to
  common Isabelle timing information in seconds, usually with a precision of
  three digits after the point (whole milliseconds).

  \<^item> \<^bold>\<open>type\<close>~\<open>uuid = string\<close> refers to a Universally Unique Identifier (UUID)
  as plain text.\<^footnote>\<open>See \<^url>\<open>https://www.ietf.org/rfc/rfc4122.txt\<close> and
  \<^url>\<open>https://docs.oracle.com/javase/8/docs/api/java/util/UUID.html\<close>.\<close> Such
  identifiers are created as private random numbers of the server and only
  revealed to the client that creates a certain resource (e.g.\ task or
  session). A client may disclose this information for use in a different
  client connection: e.g.\ this allows to share sessions between multiple
  connections.

  Client commands need to provide syntactically wellformed UUIDs: this is
  trivial to achieve by using only identifiers that have been produced by the
  server beforehand.

  \<^item> \<^bold>\<open>type\<close>~\<open>task = {task: uuid}\<close> identifies a newly created asynchronous task
  and thus allows the client to control it by the \<^verbatim>\<open>cancel\<close> command. The same
  task identification is included in messages and the final result produced by
  this task.
\<close>


subsection \<open>Command \<^verbatim>\<open>help\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  regular result: & \<^verbatim>\<open>OK\<close> \<open>[string]\<close> \\
  \end{tabular}
  \<^medskip>

  The \<^verbatim>\<open>help\<close> command has no argument and returns the list of command names
  known to the server. This is occasionally useful for interactive
  experimentation (see also @{tool client} in \secref{sec:tool-client}).
\<close>


subsection \<open>Command \<^verbatim>\<open>echo\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>any\<close> \\
  regular result: & \<^verbatim>\<open>OK\<close> \<open>any\<close> \\
  \end{tabular}
  \<^medskip>

  The \<^verbatim>\<open>echo\<close> command is the identity function: it returns its argument as
  regular result. This is occasionally useful for testing and interactive
  experimentation (see also @{tool client} in \secref{sec:tool-client}).

  The type of \<^verbatim>\<open>echo\<close> is actually more general than given above: \<^verbatim>\<open>Unit\<close>,
  \<^verbatim>\<open>XML.Elem\<close>, \<^verbatim>\<open>JSON.T\<close> are supported uniformly. Note that \<^verbatim>\<open>XML.Elem\<close> might
  be difficult to type on the console in its YXML syntax
  (\secref{sec:yxml-vs-xml}).
\<close>


subsection \<open>Command \<^verbatim>\<open>shutdown\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  regular result: & \<^verbatim>\<open>OK\<close> \\
  \end{tabular}
  \<^medskip>

  The \<^verbatim>\<open>shutdown\<close> command has no argument and result value. It forces a
  shutdown of the connected server process, stopping all open sessions and
  closing the server socket. This may disrupt pending commands on other
  connections!

  \<^medskip>
  Likewise, the command-line invocation \<^verbatim>\<open>isabelle server -x\<close> opens a server
  connection and issues a \<^verbatim>\<open>shutdown\<close> command (see also
  \secref{sec:tool-server}).
\<close>


subsection \<open>Command \<^verbatim>\<open>cancel\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>uuid\<close> \\
  regular result: & \<^verbatim>\<open>OK\<close> \\
  \end{tabular}
  \<^medskip>

  The command invocation \<^verbatim>\<open>cancel "\<close>\<open>id\<close>\<^verbatim>\<open>"\<close> attempts to cancel the specified
  task.

  Cancellation is merely a hint that the client prefers an ongoing process to
  be stopped. The command always succeeds formally, but it may get ignored by
  a task that is still running, or it might refer to a non-existing or
  no-longer existing task without producing an error.

  Successful cancellation typically leads to an asynchronous failure of type
  \<^verbatim>\<open>FAILED {\<close>\<open>task: string, message: \<close>\<^verbatim>\<open>"Interrupt"}\<close> --- or a slightly
  different message, depending how the task handles the event.
\<close>


subsection \<open>Command \<^verbatim>\<open>session_build\<close> \label{sec:command-session-build}\<close>

text \<open>
  \begin{tabular}{lll}
  argument: & \<open>session_build_args\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  notifications: & \<^verbatim>\<open>NOTE\<close> \<open>task \<oplus> (theory_progress | message)\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>task \<oplus> session_build_results\<close> \\
  error result: & \<^verbatim>\<open>FAILED\<close> \<open>task \<oplus> error_message \<oplus> session_build_results\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{lll}
  \<^bold>\<open>type\<close> \<open>session_build_args =\<close> \\
  \quad\<open>{session: string,\<close> \\
  \quad~~\<open>preferences?: string,\<close> & \<^bold>\<open>default:\<close> server preferences \\
  \quad~~\<open>options?: [string],\<close> \\
  \quad~~\<open>dirs?: [string],\<close> \\
  \quad~~\<open>ancestor_session?: string,\<close> \\
  \quad~~\<open>all_known?: bool,\<close> \\
  \quad~~\<open>focus_session?: bool,\<close> \\
  \quad~~\<open>required_session?: bool,\<close> \\
  \quad~~\<open>system_mode?: bool,\<close> \\
  \quad~~\<open>verbose?: bool}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>session_build_results =\<close> \\
  \quad\<open>{ok: bool,\<close> \\
  \quad~~\<open>return_code: int,\<close> \\
  \quad~~\<open>sessions: [session_build_result]}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>session_build_result =\<close> \\
  \quad\<open>{session: string,\<close> \\
  \quad~~\<open>ok: bool,\<close> \\
  \quad~~\<open>return_code: int,\<close> \\
  \quad~~\<open>timeout: bool,\<close> \\
  \quad~~\<open>timing: timing}\<close> \\
  \end{tabular}
\<close>

text \<open>
  The \<^verbatim>\<open>session_build\<close> command prepares given a session image for interactive
  use of theories. This is a limited version of command-line tool @{tool
  build} (\secref{sec:tool-build}), with specific options to request a formal
  context of an interactive session: it also resembles options of @{tool
  jedit} @{cite "isabelle-jedit"}.

  The build process is asynchronous, with notifications that inform about the
  progress of loaded theories. Some further human-readable messages may be
  output as well.

  Coordination of independent build processes is at the discretion of the
  client: as for like @{tool build} there are no built-in measures against
  conflicting builds with overlapping hierarchies of session images.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The field \<open>session\<close> is mandatory. It specifies the target session name:
  either directly (default) or indirectly (if \<open>required_session\<close> is
  \<^verbatim>\<open>true\<close>).

  \<^medskip>
  The environment of Isabelle system options is determined from \<open>preferences\<close>
  that are augmented by \<open>options\<close>, which is a list individual updates of the
  form the \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close> or \<open>name\<close> (the latter abbreviates
  \<open>name\<close>\<^verbatim>\<open>=true\<close>); see also command-line option \<^verbatim>\<open>-o\<close> for @{tool build}. The
  preferences are loaded from the file
  \<^path>\<open>$ISABELLE_HOME_USER/etc/preferences\<close> by default, but the client may
  provide alternative contents for it (as text, not a file-name). This could
  be relevant in situations where client and server run in different
  operating-system contexts.

  \<^medskip>
  The \<open>dirs\<close> field specifies additional directories for session ROOT files
  (\secref{sec:session-root}). This augments the name space of available
  sessions; see also option \<^verbatim>\<open>-d\<close> in @{tool build} or @{tool jedit}.

  \<^medskip>
  The \<open>ancestor_session\<close> field specifies an alternative image as starting
  point for the target image. The default is to use the parent session
  according to the ROOT entry; see also option \<^verbatim>\<open>-A\<close> in @{tool jedit}. This
  can lead to a more light-weight build process, by skipping intermediate
  session images of the hierarchy that are not used later on.

  \<^medskip>
  The \<open>all_known\<close> field set to \<^verbatim>\<open>true\<close> includes all existing sessions from
  reachable ROOT entries in the name space of theories with a proper
  session-qualified name (instead of referring to the file-system location).
  This could be relevant for the \<^verbatim>\<open>use_theories\<close> command
  (\secref{sec:command-use-theories}) to refer to arbitrary theories from
  other sessions. Note that considerable time is required to explore all
  accessible session directories and theory dependencies.

  \<^medskip>
  The \<open>focus_session\<close> field set to \<^verbatim>\<open>true\<close> to focuses on the target session:
  the accessible name space of theories is restricted to sessions that are
  connected to it.

  \<^medskip>
  The \<open>required_session\<close> field set to \<^verbatim>\<open>true\<close> indicates that the target image
  should not be the \<open>session\<close>, but its parent (or ancestor according to
  \<open>ancestor_session\<close>). Thus it prepares a session context where theories from
  the \<open>session\<close> itself can be loaded.

  \<^medskip>
  The \<open>system_mode\<close> field may be set to \<^verbatim>\<open>true\<close> to store session images and
  log files in @{path "$ISABELLE_HOME/heaps"} instead of the default location
  @{setting ISABELLE_OUTPUT} (which is normally in @{setting
  ISABELLE_HOME_USER}, i.e.\ the user's home directory). See also option \<^verbatim>\<open>-s\<close>
  in @{tool build} and @{tool jedit}.

  \<^medskip>
  The \<open>verbose\<close> field may be set to \<^verbatim>\<open>true\<close> for extra verbosity. The effect is
  similar to option \<^verbatim>\<open>-v\<close> in @{tool build}.
\<close>


subsubsection \<open>Intermediate output\<close>

text \<open>
  The asynchronous notifications of command \<^verbatim>\<open>session_build\<close> mainly serve as
  progress indicator: the output resembles that of the session build window of
  Isabelle/jEdit after startup @{cite "isabelle-jedit"}.

  For the client it is usually sufficient to print the messages in plain text,
  but note that \<open>theory_progress\<close> also reveals the internal \<open>theory\<close> and
  \<open>session\<close> names.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The overall \<open>session_build_results\<close> contain both a summary and and entry
  \<open>session_build_result\<close> for each session in the build hierarchy, leading up
  to the specified target session. The result is always provided,
  independently of overall success (\<^verbatim>\<open>FINISHED\<close> task) or failure (\<^verbatim>\<open>FAILED\<close>
  task).

  The \<open>ok\<close> field tells abstractly, whether all required session builds came
  out as \<open>ok\<close>, i.e.\ \<open>return_code\<close>. A non-zero \<open>return_code\<close> indicates an
  error according to usual POSIX conventions for process exit.

  For individual \<open>session_build_result\<close> entries, there are additional fields:
  \<open>timeout\<close> to tell if the build process was aborted after running too long,
  and \<open>timing\<close> for the overall process timing in the usual Isabelle format
  with elapsed, CPU, gc time.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Build of a session image from the Isabelle distribution:
  @{verbatim [display] \<open>session_build {"session": "HOL-Word"}\<close>}

  Build a session image from the Archive of Formal Proofs:
  @{verbatim [display] \<open>session_build {"session": "Coinductive", "dirs": ["$AFP_BASE/thys"]}\<close>}

  Build of a session image of \<^verbatim>\<open>HOL-Number_Theory\<close> directly on top of \<^verbatim>\<open>HOL\<close>:
  @{verbatim [display] \<open>session_build {"session": "HOL-Number_Theory", "ancestor_session": "HOL"}\<close>}
\<close>


subsection \<open>Command \<^verbatim>\<open>session_start\<close> \label{sec:command-session-start}\<close>

text \<open>
  \begin{tabular}{lll}
  argument: & \<open>session_build_args \<oplus> {print_mode?: [string]}\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  notifications: & \<^verbatim>\<open>NOTE\<close> \<open>task \<oplus> (theory_progress | message)\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>task \<oplus> session_start_result\<close> \\
  error result: & \<^verbatim>\<open>FAILED\<close> \<open>task \<oplus> error_message\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{l}
  \<^bold>\<open>type\<close> \<open>session_start_result = {session: string, session_id: uuid}\<close>
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>session_start\<close> command starts a new Isabelle/PIDE session with
  underlying Isabelle/ML process, based on a session image that it produces on
  demand in the same manner as \<^verbatim>\<open>session_build\<close>. Thus it accepts all
  \<open>session_build_args\<close> and produces similar notifications, but the detailed
  \<open>session_build_results\<close> are omitted.

  The session build and startup process is asynchronous: when the task is
  finished, the session remains active for commands such as \<^verbatim>\<open>use_theories\<close>
  (\secref{sec:command-use-theories}), until a \<^verbatim>\<open>session_stop\<close> or \<^verbatim>\<open>shutdown\<close>
  command is sent to the server.

  Sessions are independent of client connections: it is possible to start a
  session and later apply \<^verbatim>\<open>use_theories\<close> on different connections, as long as
  the internal session identifier is known.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  Most of the arguments are the same as for \<^verbatim>\<open>session_build\<close>
  (\secref{sec:command-session-build}).

  \<^medskip>
  The \<open>print_mode\<close> field adds identifiers of print modes to be made active for
  this session. For example, \<^verbatim>\<open>"print_mode": ["ASCII"]\<close> prefers ASCII
  replacement syntax over mathematical Isabelle symbols. See also option \<^verbatim>\<open>-m\<close>
  in @{tool process} (\secref{sec:tool-process}).
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>session\<close> field provides the active session name for clarity.

  \<^medskip>
  The \<open>session_id\<close> field provides the internal identification of the session
  object within the sever process. It can remain active as long as the server
  is running, independently of the current client connection.
\<close>


subsection \<open>Examples\<close>

text \<open>
  Start a default Isabelle/HOL session:
  @{verbatim [display] \<open>session_start {"session": "HOL"}\<close>}
\<close>


subsection \<open>Command \<^verbatim>\<open>session_stop\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>{session_id?: uuid}\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>task \<oplus> session_stop_result\<close> \\
  error result: & \<^verbatim>\<open>FAILED\<close> \<open>task \<oplus> error_message \<oplus> session_stop_result\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{l}
  \<^bold>\<open>type\<close> \<open>session_stop_result = {ok: bool, return_code: int}\<close>
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>session_stop\<close> command forces a shutdown of the identified
  Isabelle/PIDE session. This asynchronous tasks usually finishes quickly.
  Failure only happens unusual situations, according to the return code of the
  underlying Isabelle/ML process.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session_id\<close> field is the UUID originally created by the server for the
  intended session.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>ok\<close> field tells abstractly, whether the Isabelle/ML process terminated
  properly. The \<open>return_code\<close> expresses this information according to usual
  POSIX conventions for process exit.
\<close>


subsection \<open>Command \<^verbatim>\<open>use_theories\<close> \label{sec:command-use-theories}\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>use_theories_arguments\<close> \\
  regular result: & \<^verbatim>\<open>OK\<close> \<open>use_theories_results\<close> \\
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>theory_name = string | {name: string, pos: position}\<close> \\
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>use_theories_arguments =\<close> \\
  \quad\<open>{session_id: uuid,\<close> \\
  \quad~~\<open>theories: [theory_name],\<close> \\
  \quad~~\<open>qualifier?: string,\<close> \\
  \quad~~\<open>master_dir?: string,\<close> \\
  \quad~~\<open>pretty_margin?: double\<close> & \<^bold>\<open>default:\<close> \<^verbatim>\<open>76\<close> \\
  \quad~~\<open>unicode_symbols?: bool}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>node_status =\<close> \\
  \quad\<open>{ok: bool,\<close> \\
  \quad~~\<open>total: int,\<close> \\
  \quad~~\<open>unprocessed: int,\<close> \\
  \quad~~\<open>running: int,\<close> \\
  \quad~~\<open>warned: int,\<close> \\
  \quad~~\<open>failed: int,\<close> \\
  \quad~~\<open>finished: int,\<close> \\
  \quad~~\<open>consolidated: bool}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>node_result =\<close> \\
  \quad\<open>{node_name: string,\<close> \\
  \quad~~\<open>theory: string,\<close> \\
  \quad~~\<open>status: node_status,\<close> \\
  \quad~~\<open>messages: [message]}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>use_theories_results =\<close> \\
  \quad\<open>{ok: bool,\<close> \\
  \quad~~\<open>errors: [message],\<close> \\
  \quad~~\<open>nodes: [node_result]}\<close> \\[2ex]
  \end{tabular}

  \<^medskip>

  The \<^verbatim>\<open>use_theories\<close> command updates the identified session by adding the
  current version of given theory files to it: theory dependencies are
  resolved implicitly. The command succeeds eventually, when all theories have
  been \<^emph>\<open>consolidated\<close> in the sense that the outermost command structure has
  finished (or failed) and the final \<^theory_text>\<open>end\<close> command of each theory has been
  checked.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session_id\<close> is the identifier provided by the server, when the session
  was created (possibly on a different client connection).

  \<^medskip>
  The \<open>theories\<close> field specifies theory names as in \<^theory_text>\<open>theory imports\<close> or in
  session ROOT \<^verbatim>\<open>theories\<close>: an explicit source position for these theory name
  specifications may be given as well, which is occasionally useful for
  precise error locations.

  \<^medskip>
  The \<open>qualifier\<close> field provides an alternative session qualifier for theories
  that are not formally recognized as a member of a particular session. The
  default is \<^verbatim>\<open>Draft\<close> as in Isabelle/jEdit. There is rarely a need to change
  that, as theory nodes are already uniquely identified by their physical
  file-system location.

  \<^medskip>
  The \<open>master_dir\<close> field explicit specifies the formal master directory of the
  imported theory. Normally this is determined implicitly from the parent
  directory of the physical theory file location.

  \<^medskip>
  The \<open>pretty_margin\<close> field specifies the line width for pretty-printing. The
  default is for classic console output. Formatting happens at the end of
  \<^verbatim>\<open>use_theories\<close>, when all prover messages produced are exported to the
  client.

  \<^medskip>
  The \<open>unicode_symbols\<close> field set to \<^verbatim>\<open>true\<close> means that message output is
  rendered for direct output on a Unicode capable channel, ideally with the
  Isabelle fonts as in Isabelle/jEdit (or Isabelle HTML output). The default
  is to keep the symbolic representation of Isabelle text, e.g.\ \<^verbatim>\<open>\<forall>\<close> instead
  of its rendering as \<open>\<forall>\<close>. This means the client needs to perform its own
  rendering to present it to the end-user.
\<close>

subsubsection \<open>Results\<close>

text \<open>
  The \<open>ok\<close> field indicates overall success of processing the specified
  theories with all their dependencies.

  When \<open>ok\<close> is \<^verbatim>\<open>false\<close>, the \<open>errors\<close> field lists all errors cumulatively,
  including position information for the theory nodes where the error happened
  (this includes imported theories).

  \<^medskip>
  The \<open>nodes\<close> field provides more detailed information about each imported
  theory node. Here the individual fields are as follows:

  \<^item> \<open>node_name\<close>: the physical name for the theory node, based on its
  file-system location;\<^footnote>\<open>Clients may recognize the originally provided
  file-names after careful normalization in the file-system of the server.\<close>

  \<^item> \<open>theory\<close>: the logical theory name, e.g.\ \<^verbatim>\<open>HOL-Library.AList\<close> or
  \<^verbatim>\<open>Draft.Test\<close>;

  \<^item> \<open>status\<close>: the overall node status, e.g.\ see the visualization in the
  \<open>Theories\<close> panel of Isabelle/jEdit @{cite "isabelle-jedit"};

  \<^item> \<open>messages\<close>: the main bulk of prover messages produced in this theory note
  (\<^verbatim>\<open>writeln\<close>, \<^verbatim>\<open>warning\<close>, \<^verbatim>\<open>error\<close>, etc.).
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Process some example theory from the Isabelle distribution, within the
  context of an already started session for Isabelle/HOL (see also
  \secref{sec:command-session-start}):
  @{verbatim [display] \<open>use_theories {"session_id": ..., "theories": ["~~/src/HOL/Isar_Examples/Drinker"]}\<close>}

  \<^medskip>
  Process some example theories that import other theories via
  session-qualified theory names:

  @{verbatim [display] \<open>session_start {"session": "HOL", "all_known": true}
use_theories {"session_id": ..., "theories": ["~~/src/HOL/Unix/Unix"]}
session_stop {"session_id": ...}\<close>}

  The option \<open>all_known\<close> has been used here to the full name space of
  session-qualified theory names accessible in this session. This is also the
  default in Isabelle/jEdit, although it requires significant startup time.

  \<^medskip>
  Process some example theories in the context of their (single) parent
  session:

  @{verbatim [display] \<open>session_start {"session": "HOL-Library"}
use_theories {"session_id": ..., "theories": ["~~/src/HOL/Unix/Unix"]}
session_stop {"session_id": ...}\<close>}
\<close>

end
