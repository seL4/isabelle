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
  analogous to \<^ML>\<open>Thy_Info.use_theories\<close> in Isabelle/ML, but with full
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
  central database file \<^path>\<open>$ISABELLE_HOME_USER/servers.db\<close>) or by
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
  for a suitable server process. Also note that the @{tool client} tool
  (\secref{sec:tool-client}) provides a command-line editor to interact with
  the server.

  \<^medskip>
  Option \<^verbatim>\<open>-L\<close> specifies a log file for exceptional output of internal server
  and session operations.

  \<^medskip>
  Operation \<^verbatim>\<open>-l\<close> lists all active server processes with their connection
  details.

  \<^medskip>
  Operation \<^verbatim>\<open>-x\<close> exits the specified server process by sending it a
  \<^verbatim>\<open>shutdown\<close> command.
\<close>


subsection \<open>Client \label{sec:tool-client}\<close>

text \<open>
  The @{tool_def client} tool provides console interaction for Isabelle
  servers:
  @{verbatim [display]
\<open>Usage: isabelle client [OPTIONS]

  Options are:
    -n NAME      explicit server name
    -p PORT      explicit server port

  Console interaction for Isabelle server (with line-editor).\<close>}

  This is a wrapper to \<^verbatim>\<open>isabelle server -s -c\<close> for interactive
  experimentation, which uses @{setting ISABELLE_LINE_EDITOR} if available.
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

  The first line of output presents the connection details:\<^footnote>\<open>This information
  may be used in other TCP clients, without access to Isabelle/Scala and the
  underlying database of running servers.\<close>
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
  Exit the named server on the command-line:
  @{verbatim [display] \<open>isabelle server -n test -x\<close>}
\<close>


section \<open>Protocol messages \label{sec:server-protocol}\<close>

text \<open>
  The Isabelle server listens on a regular TCP socket, using a line-oriented
  protocol of structured messages. Input \<^emph>\<open>commands\<close> and output \<^emph>\<open>results\<close>
  (via \<^verbatim>\<open>OK\<close> or \<^verbatim>\<open>ERROR\<close>) are strictly alternating on the toplevel, but
  commands may also return a \<^emph>\<open>task\<close> identifier to indicate an ongoing
  asynchronous process that is joined later (via \<^verbatim>\<open>FINISHED\<close> or \<^verbatim>\<open>FAILED\<close>).
  Asynchronous \<^verbatim>\<open>NOTE\<close> messages may occur at any time: they are independent of
  the main command-result protocol.

  For example, the synchronous \<^verbatim>\<open>echo\<close> command immediately returns its
  argument as \<^verbatim>\<open>OK\<close> result. In contrast, the asynchronous \<^verbatim>\<open>session_build\<close>
  command returns \<^verbatim>\<open>OK {"task":\<close>\<open>id\<close>\<^verbatim>\<open>}\<close> and continues in the background. It
  will eventually produce \<^verbatim>\<open>FINISHED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> or
  \<^verbatim>\<open>FAILED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> with the final result. Intermediately, it
  may emit asynchronous messages of the form \<^verbatim>\<open>NOTE {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close>
  to inform about its progress. Due to the explicit task identifier, the
  client can show these messages in the proper context, e.g.\ a GUI window for
  this particular session build job.

  \medskip Subsequently, the protocol message formats are described in further
  detail.
\<close>


subsection \<open>Byte messages \label{sec:byte-messages}\<close>

text \<open>
  The client-server connection is a raw byte-channel for bidirectional
  communication, but the Isabelle server always works with messages of a
  particular length. Messages are written as a single chunk that is flushed
  immediately.

  Message boundaries are determined as follows:

    \<^item> A \<^emph>\<open>short message\<close> consists of a single line: it is a sequence of
    arbitrary bytes excluding CR (13) and LF (10), and terminated by CR-LF or
    just LF.

    \<^item> A \<^emph>\<open>long message\<close> starts with a single that consists only of decimal
    digits: these are interpreted as length of the subsequent block of
    arbitrary bytes. A final line-terminator (as above) may be included here,
    but is not required.

  Messages in JSON format (see below) always fit on a single line, due to
  escaping of newline characters within string literals. This is convenient
  for interactive experimentation, but it can impact performance for very long
  messages. If the message byte-length is given on the preceding line, the
  server can read the message more efficiently as a single block.
\<close>


subsection \<open>Text messages\<close>

text \<open>
  Messages are read and written as byte streams (with byte lengths), but the
  content is always interpreted as plain text in terms of the UTF-8
  encoding.\<^footnote>\<open>See also the ``UTF-8 Everywhere Manifesto''
  \<^url>\<open>https://utf8everywhere.org\<close>.\<close>

  Note that line-endings and other formatting characters are invariant wrt.
  UTF-8 representation of text: thus implementations are free to determine the
  overall message structure before or after applying the text encoding.
\<close>


subsection \<open>Input and output messages \label{sec:input-output-messages}\<close>

text \<open>
  Server input and output messages have a uniform format as follows:

    \<^item> \<open>name argument\<close> such that:

    \<^item> \<open>name\<close> is the longest prefix consisting of ASCII letters, digits,
    ``\<^verbatim>\<open>_\<close>'', ``\<^verbatim>\<open>.\<close>'',

    \<^item> the separator between \<open>name\<close> and \<open>argument\<close> is the longest possible
    sequence of ASCII blanks (it could be empty, e.g.\ when the argument
    starts with a quote or bracket),

    \<^item> \<open>argument\<close> is the rest of the message without line terminator.

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
  be its unique password as a single line, without length indication (i.e.\ a
  ``short message'' in the sense of \secref{sec:byte-messages}).

  The server replies either with \<^verbatim>\<open>OK\<close> (and some information about the
  Isabelle version) or by silent disconnection of what is considered an
  illegal connection attempt. Note that @{tool client} already presents the
  correct password internally.

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
  potentially further result fields (this resembles exceptions in Scala).

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
  or fails eventually, while emitting arbitrary notifications in between.
  Formally, it starts as synchronous command with immediate result \<^verbatim>\<open>OK\<close>
  giving the \<^verbatim>\<open>task\<close> identifier, or an immediate \<^verbatim>\<open>ERROR\<close> that indicates bad
  command syntax. For a running task, the termination is indicated later by
  \<^verbatim>\<open>FINISHED\<close> or \<^verbatim>\<open>FAILED\<close>, together with its ultimate result value.

  These are the protocol exchanges for various cases of command task
  execution:

  \begin{center}
  \begin{tabular}{rl}
  \<^bold>\<open>input:\<close> & \<open>command argument\<close> \\
  immediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>OK {"task":\<close>\<open>id\<close>\<^verbatim>\<open>}\<close> \\
  intermediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>NOTE {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\
  (a) regular \<^bold>\<open>output:\<close> & \<^verbatim>\<open>FINISHED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\
  (b) error \<^bold>\<open>output:\<close> & \<^verbatim>\<open>FAILED {"task":\<close>\<open>id\<close>\<^verbatim>\<open>,\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close> \\[3ex]
  \<^bold>\<open>input:\<close> & \<open>command argument\<close> \\
  immediate \<^bold>\<open>output:\<close> & \<^verbatim>\<open>ERROR\<close>~\<open>\<dots>\<close> \\
  \end{tabular}
  \end{center}

  All asynchronous messages are decorated with the task identifier that was
  revealed in the immediate (synchronous) result. Thus the client can
  invoke further asynchronous commands and still dispatch the resulting stream of
  asynchronous messages properly.

  The synchronous command \<^verbatim>\<open>cancel {"task":\<close>~\<open>id\<close>\<^verbatim>\<open>}\<close> tells the specified task
  to terminate prematurely: usually causing a \<^verbatim>\<open>FAILED\<close> result, but this is
  not guaranteed: the cancel event may come too late or the running process
  may just ignore it.
\<close>


section \<open>Types for JSON values \label{sec:json-types}\<close>

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
      @{syntax type} '|' @{syntax type} |
      '(' @{syntax type} ')'
    ;
    @{syntax field_type}: @{syntax name} ('?'?) ':' @{syntax type}
  \<close>

  This is a simplified variation of TypeScript
  interfaces.\<^footnote>\<open>\<^url>\<open>https://www.typescriptlang.org/docs/handbook/interfaces.html\<close>\<close>
  The meaning of these types is specified wrt. the Isabelle/Scala
  implementation as follows.

  \<^item> A \<open>name\<close> refers to a type defined elsewhere. The environment of type
  definitions is given informally: put into proper foundational order, it
  needs to specify a strongly normalizing system of syntactic abbreviations;
  type definitions may not be recursive.

  \<^item> A \<open>value\<close> in JSON notation represents the singleton type of the given
  item. For example, the string \<^verbatim>\<open>"error"\<close> can be used as type for a slot that
  is guaranteed to contain that constant.

  \<^item> Type \<open>any\<close> is the super type of all other types: it is an untyped slot in
  the specification and corresponds to \<^verbatim>\<open>Any\<close> or \<^verbatim>\<open>JSON.T\<close> in Isabelle/Scala.

  \<^item> Type \<open>null\<close> is the type of the improper value \<open>null\<close>; it corresponds to
  type \<^verbatim>\<open>Null\<close> in Scala and is normally not used in Isabelle/Scala.\<^footnote>\<open>See also
  ``Null References: The Billion Dollar Mistake'' by Tony Hoare
  \<^url>\<open>https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare\<close>.\<close>

  \<^item> Type \<open>bool\<close> is the type of the truth values \<^verbatim>\<open>true\<close> and \<^verbatim>\<open>false\<close>; it
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
  wrt. the subtype relation).

  \<^item> Object types describe the possible content of JSON records, with field
  names and types. A question mark after a field name means that it is
  optional. In Scala this could refer to an explicit type \<^verbatim>\<open>Option[t]\<close>, e.g.\
  \<open>{a: int, b?: string}\<close> corresponding to a Scala case class with arguments
  \<^verbatim>\<open>a: Int\<close>, \<^verbatim>\<open>b: Option[String]\<close>.

  Alternatively, optional fields can have a default value. If nothing else is
  specified, a standard ``empty value'' is used for each type, i.e.\ \<^verbatim>\<open>0\<close> for
  the number types, \<^verbatim>\<open>false\<close> for \<open>bool\<close>, or the empty string, array, object
  etc.

  Object types are \<^emph>\<open>permissive\<close> in the sense that only the specified field
  names need to conform to the given types, but unspecified fields may be
  present as well.

  \<^item> The type expression \<open>t\<^sub>1 \<oplus> t\<^sub>2\<close> only works for two object types with
  disjoint field names: it is the concatenation of the respective @{syntax
  field_type} specifications taken together. For example: \<open>{task: string} \<oplus>
  {ok: bool}\<close> is the equivalent to \<open>{task: string, ok: bool}\<close>.

  \<^item> The type expression \<open>t\<^sub>1 | t\<^sub>2\<close> is the disjoint union of two types, either
  one of the two cases may occur.

  \<^item> Parentheses \<open>(t)\<close> merely group type expressions syntactically.


  These types correspond to JSON values in an obvious manner, which is not
  further described here. For example, the JSON array \<^verbatim>\<open>[1, 2, 3]\<close> conforms to
  types \<open>[int]\<close>, \<open>[long]\<close>, \<open>[double]\<close>, \<open>[any]\<close>, \<open>any\<close>.

  Note that JSON objects require field names to be quoted, but the type
  language omits quotes for clarity. Thus the object \<^verbatim>\<open>{"a": 42, "b": "xyz"}\<close>
  conforms to the type \<open>{a: int, b: string}\<close>, for example.

  \<^medskip>
  The absence of an argument or result is represented by the Scala type
  \<^verbatim>\<open>Unit\<close>: it is written as empty text in the message \<open>argument\<close>
  (\secref{sec:input-output-messages}). This is not part of the JSON language.

  Server replies have name tags like \<^verbatim>\<open>OK\<close>, \<^verbatim>\<open>ERROR\<close>: these are used literally
  together with type specifications to indicate the particular name with the
  type of its argument, e.g.\ \<^verbatim>\<open>OK\<close>~\<open>[string]\<close> for a regular result that is a
  list (JSON array) of strings.

  \<^bigskip>
  Here are some common type definitions, for use in particular specifications
  of command arguments and results.

  \<^item> \<^bold>\<open>type\<close>~\<open>position = {line?: int, offset?: int, end_offset?: int, file?:
  string, id?: long}\<close> describes a source position within Isabelle text. Only
  the \<open>line\<close> and \<open>file\<close> fields make immediate sense to external programs.
  Detailed \<open>offset\<close> and \<open>end_offset\<close> positions are counted according to
  Isabelle symbols, see \<^ML_type>\<open>Symbol.symbol\<close> in Isabelle/ML @{cite
  "isabelle-implementation"}. The position \<open>id\<close> belongs to the representation
  of command transactions in the Isabelle/PIDE protocol: it normally does not
  occur in externalized positions.

  \<^item> \<^bold>\<open>type\<close>~\<open>message = {kind: string, message: string, pos?: position}\<close> where
  the \<open>kind\<close> provides some hint about the role and importance of the message.
  The main message kinds are \<^verbatim>\<open>writeln\<close> (for regular output), \<^verbatim>\<open>warning\<close>,
  \<^verbatim>\<open>error\<close>.

  \<^item> \<^bold>\<open>type\<close>~\<open>error_message = {kind:\<close>~\<^verbatim>\<open>"error"\<close>\<open>, message: string}\<close> refers to
  error messages in particular. These occur routinely with \<^verbatim>\<open>ERROR\<close> or
  \<^verbatim>\<open>FAILED\<close> replies, but also as initial command syntax errors (which are
  omitted in the command specifications below).

  \<^item> \<^bold>\<open>type\<close>~\<open>theory_progress = {kind:\<close>~\<^verbatim>\<open>"writeln"\<close>\<open>, message: string, theory:
  string, session: string, percentage?: int}\<close> reports formal progress in
  loading theories (e.g.\ when building a session image). Apart from a regular
  output message, it also reveals the formal theory name (e.g.\ \<^verbatim>\<open>"HOL.Nat"\<close>)
  and session name (e.g.\ \<^verbatim>\<open>"HOL"\<close>). Note that some rare theory names lack a
  proper session prefix, e.g.\ theory \<^verbatim>\<open>"Main"\<close> in session \<^verbatim>\<open>"HOL"\<close>. The
  optional percentage has the same meaning as in \<^bold>\<open>type\<close>~\<open>node_status\<close> below.

  \<^item> \<^bold>\<open>type\<close>~\<open>timing = {elapsed: double, cpu: double, gc: double}\<close> refers to
  common Isabelle timing information in seconds, usually with a precision of
  three digits after the point (whole milliseconds).

  \<^item> \<^bold>\<open>type\<close>~\<open>uuid = string\<close> refers to a Universally Unique Identifier (UUID)
  as plain text.\<^footnote>\<open>See \<^url>\<open>https://www.ietf.org/rfc/rfc4122.txt\<close> and
  \<^url>\<open>https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/util/UUID.html\<close>.\<close> Such
  identifiers are created as private random numbers of the server and only
  revealed to the client that creates a certain resource (e.g.\ task or
  session). A client may disclose this information for use in a different
  client connection: this allows to share sessions between multiple
  connections.

  Client commands need to provide syntactically wellformed UUIDs: this is
  trivial to achieve by using only identifiers that have been produced by the
  server beforehand.

  \<^item> \<^bold>\<open>type\<close>~\<open>task = {task: uuid}\<close> identifies a newly created asynchronous task
  and thus allows the client to control it by the \<^verbatim>\<open>cancel\<close> command. The same
  task identification is included in all messages produced by this task.

  \<^item> \<^bold>\<open>type\<close> \<open>session_id = {session_id: uuid}\<close> identifies a newly created PIDE
  session managed by the server. Sessions are independent of client
  connections and may be shared by different clients, as long as the internal
  session identifier is known.

  \<^item> \<^bold>\<open>type\<close> \<open>node = {node_name: string, theory_name: string}\<close> represents the
  internal node name of a theory. The \<open>node_name\<close> is derived from the
  canonical theory file-name (e.g.\ \<^verbatim>\<open>"~~/src/HOL/Examples/Seq.thy"\<close> after
  normalization within the file-system). The \<open>theory_name\<close> is the
  session-qualified theory name (e.g.\ \<^verbatim>\<open>HOL-Examples.Seq\<close>).

  \<^item> \<^bold>\<open>type\<close> \<open>node_status = {ok: bool, total: int, unprocessed: int, running:
  int, warned: int, failed: int, finished: int, canceled: bool, consolidated:
  bool, percentage: int}\<close> represents a formal theory node status of the PIDE
  document model as follows.

    \<^item> Fields \<open>total\<close>, \<open>unprocessed\<close>, \<open>running\<close>, \<open>warned\<close>, \<open>failed\<close>, \<open>finished\<close>
      account for individual commands within a theory node; \<open>ok\<close> is an
      abstraction for \<open>failed = 0\<close>.

    \<^item> The \<open>canceled\<close> flag tells if some command in the theory has been
      spontaneously canceled (by an Interrupt exception that could also
      indicate resource problems).

    \<^item> The \<open>consolidated\<close> flag indicates whether the outermost theory command
    structure has finished (or failed) and the final \<^theory_text>\<open>end\<close> command has been
    checked.

    \<^item> The \<open>percentage\<close> field tells how far the node has been processed. It
    ranges between 0 and 99 in normal operation, and reaches 100 when the node
    has been formally consolidated as described above.
\<close>



section \<open>Server commands and results\<close>

text \<open>
  Here follows an overview of particular Isabelle server commands with their
  results, which are usually represented as JSON values with types according
  to \secref{sec:json-types}. The general format of input and output messages
  is described in \secref{sec:input-output-messages}. The relevant
  Isabelle/Scala source files are:

  \<^medskip>
  \begin{tabular}{l}
  \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/server_commands.scala\<close> \\
  \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/server.scala\<close> \\
  \<^file>\<open>$ISABELLE_HOME/src/Pure/General/json.scala\<close> \\
  \end{tabular}
\<close>


subsection \<open>Command \<^verbatim>\<open>help\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  regular result: & \<^verbatim>\<open>OK\<close> \<open>[string]\<close> \\
  \end{tabular}
  \<^medskip>

  The \<^verbatim>\<open>help\<close> command has no argument and returns the list of server command
  names. This is occasionally useful for interactive experimentation (see also
  @{tool client} in \secref{sec:tool-client}).
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

  The Scala type of \<^verbatim>\<open>echo\<close> is actually more general than given above:
  \<^verbatim>\<open>Unit\<close>, \<^verbatim>\<open>XML.Elem\<close>, \<^verbatim>\<open>JSON.T\<close> work uniformly. Note that \<^verbatim>\<open>XML.Elem\<close> might
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
  The command-line invocation \<^verbatim>\<open>isabelle server -x\<close> opens a server connection
  and issues a \<^verbatim>\<open>shutdown\<close> command (see also \secref{sec:tool-server}).
\<close>


subsection \<open>Command \<^verbatim>\<open>cancel\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>task\<close> \\
  regular result: & \<^verbatim>\<open>OK\<close> \\
  \end{tabular}
  \<^medskip>

  The command \<^verbatim>\<open>cancel {"task":\<close>~\<open>id\<close>\<^verbatim>\<open>}\<close> attempts to cancel the specified
  task.

  Cancellation is merely a hint that the client prefers an ongoing process to
  be stopped. The command always succeeds formally, but it may get ignored by
  a task that is still running; it might also refer to a non-existing or
  no-longer existing task (without producing an error).

  Successful cancellation typically leads to an asynchronous failure of type
  \<^verbatim>\<open>FAILED {\<close>\<open>task: uuid, message:\<close>~\<^verbatim>\<open>"Interrupt"}\<close>. A different message is
  also possible, depending how the task handles the event.
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
  \quad~~\<open>include_sessions: [string],\<close> \\
  \quad~~\<open>verbose?: bool}\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>session_build_result =\<close> \\
  \quad\<open>{session: string,\<close> \\
  \quad~~\<open>ok: bool,\<close> \\
  \quad~~\<open>return_code: int,\<close> \\
  \quad~~\<open>timeout: bool,\<close> \\
  \quad~~\<open>timing: timing}\<close> \\[2ex]

  \<^bold>\<open>type\<close> \<open>session_build_results =\<close> \\
  \quad\<open>{ok: bool,\<close> \\
  \quad~~\<open>return_code: int,\<close> \\
  \quad~~\<open>sessions: [session_build_result]}\<close> \\
  \end{tabular}
\<close>

text \<open>
  The \<^verbatim>\<open>session_build\<close> command prepares a session image for interactive use of
  theories. This is a limited version of command-line tool @{tool build}
  (\secref{sec:tool-build}), with specific options to request a formal context
  for an interactive PIDE session.

  The build process is asynchronous, with notifications that inform about the
  progress of loaded theories. Some further informative messages are output as
  well.

  Coordination of independent build processes is at the discretion of the
  client (or end-user), just as for @{tool build} and @{tool jedit}. There is
  no built-in coordination of conflicting builds with overlapping hierarchies
  of session images. In the worst case, a session image produced by one task
  may get overwritten by another task!
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session\<close> field specifies the target session name. The build process
  will produce all required ancestor images according to the overall session
  graph.

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
  The \<open>dirs\<close> field specifies additional directories for session ROOT and ROOTS
  files (\secref{sec:session-root}). This augments the name space of available
  sessions; see also option \<^verbatim>\<open>-d\<close> in @{tool build}.

  \<^medskip>
  The \<open>include_sessions\<close> field specifies sessions whose theories should be
  included in the overall name space of session-qualified theory names. This
  corresponds to a \<^bold>\<open>sessions\<close> specification in ROOT files
  (\secref{sec:session-root}). It enables the \<^verbatim>\<open>use_theories\<close> command
  (\secref{sec:command-use-theories}) to refer to sources from other sessions
  in a robust manner, instead of relying on directory locations.

  \<^medskip>
  The \<open>verbose\<close> field set to \<^verbatim>\<open>true\<close> yields extra verbosity. The effect is
  similar to option \<^verbatim>\<open>-v\<close> in @{tool build}.
\<close>


subsubsection \<open>Intermediate output\<close>

text \<open>
  The asynchronous notifications of command \<^verbatim>\<open>session_build\<close> mainly serve as
  progress indicator: the output resembles that of the session build window of
  Isabelle/jEdit after startup @{cite "isabelle-jedit"}.

  For the client it is usually sufficient to print the messages in plain text,
  but note that \<open>theory_progress\<close> also reveals formal \<open>theory\<close> and
  \<open>session\<close> names directly.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The overall \<open>session_build_results\<close> contain both a summary and an entry
  \<open>session_build_result\<close> for each session in the build hierarchy. The result
  is always provided, independently of overall success (\<^verbatim>\<open>FINISHED\<close> task) or
  failure (\<^verbatim>\<open>FAILED\<close> task).

  The \<open>ok\<close> field tells abstractly, whether all required session builds came
  out as \<open>ok\<close>, i.e.\ with zero \<open>return_code\<close>. A non-zero \<open>return_code\<close>
  indicates an error according to usual POSIX conventions for process exit.

  The individual \<open>session_build_result\<close> entries provide extra fields:

  \<^item> \<open>timeout\<close> tells if the build process was aborted after running too long,

  \<^item> \<open>timing\<close> gives the overall process timing in the usual Isabelle format
  with elapsed, CPU, GC time.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Build of a session image from the Isabelle distribution:
  @{verbatim [display] \<open>session_build {"session": "HOL-Algebra"}\<close>}

  Build a session image from the Archive of Formal Proofs:
  @{verbatim [display] \<open>session_build {"session": "Coinductive", "dirs": ["$AFP_BASE/thys"]}\<close>}
\<close>


subsection \<open>Command \<^verbatim>\<open>session_start\<close> \label{sec:command-session-start}\<close>

text \<open>
  \begin{tabular}{lll}
  argument: & \<open>session_build_args \<oplus> {print_mode?: [string]}\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  notifications: & \<^verbatim>\<open>NOTE\<close> \<open>task \<oplus> (theory_progress | message)\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>task \<oplus> session_id \<oplus> {tmp_dir: string}\<close> \\
  error result: & \<^verbatim>\<open>FAILED\<close> \<open>task \<oplus> error_message\<close> \\[2ex]
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>session_start\<close> command starts a new Isabelle/PIDE session with
  underlying Isabelle/ML process, based on a session image that it produces on
  demand using \<^verbatim>\<open>session_build\<close>. Thus it accepts all \<open>session_build_args\<close> and
  produces similar notifications, but the detailed \<open>session_build_results\<close> are
  omitted.

  The session build and startup process is asynchronous: when the task is
  finished, the session remains active for commands, until a \<^verbatim>\<open>session_stop\<close>
  or \<^verbatim>\<open>shutdown\<close> command is sent to the server.

  Sessions are independent of client connections: it is possible to start a
  session and later apply \<^verbatim>\<open>use_theories\<close> on different connections, as long as
  the internal session identifier is known: shared theory imports will be used
  only once (and persist until purged explicitly).
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  Most arguments are shared with \<^verbatim>\<open>session_build\<close>
  (\secref{sec:command-session-build}).

  \<^medskip>
  The \<open>print_mode\<close> field adds identifiers of print modes to be made active for
  this session. For example, \<^verbatim>\<open>"print_mode": ["ASCII"]\<close> prefers ASCII
  replacement syntax over mathematical Isabelle symbols. See also option \<^verbatim>\<open>-m\<close>
  in @{tool process} (\secref{sec:tool-process}).
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>session_id\<close> provides the internal identification of the session object
  within the sever process. It can remain active as long as the server is
  running, independently of the current client connection.

  \<^medskip>
  The \<open>tmp_dir\<close> field refers to a temporary directory that is specifically
  created for this session and deleted after it has been stopped. This may
  serve as auxiliary file-space for the \<^verbatim>\<open>use_theories\<close> command, but
  concurrent use requires some care in naming temporary files, e.g.\ by
  using sub-directories with globally unique names.

  As \<open>tmp_dir\<close> is the default \<open>master_dir\<close> for commands \<^verbatim>\<open>use_theories\<close> and
  \<^verbatim>\<open>purge_theories\<close>, theory files copied there may be used without further
  path specification.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Start a default Isabelle/HOL session:
  @{verbatim [display] \<open>session_start {"session": "HOL"}\<close>}

  Start a session from the Archive of Formal Proofs:
  @{verbatim [display] \<open>session_start {"session": "Coinductive", "dirs": ["$AFP_BASE/thys"]}\<close>}
\<close>


subsection \<open>Command \<^verbatim>\<open>session_stop\<close>\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>session_id\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>task \<oplus> session_stop_result\<close> \\
  error result: & \<^verbatim>\<open>FAILED\<close> \<open>task \<oplus> error_message \<oplus> session_stop_result\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{l}
  \<^bold>\<open>type\<close> \<open>session_stop_result = {ok: bool, return_code: int}\<close>
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>session_stop\<close> command forces a shutdown of the identified PIDE
  session. This asynchronous tasks usually finishes quickly. Failure only
  happens in unusual situations, according to the return code of the
  underlying Isabelle/ML process.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session_id\<close> provides the UUID originally created by the server for this
  session.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>ok\<close> field tells abstractly, whether the Isabelle/ML process has
  terminated properly.

  The \<open>return_code\<close> field expresses this information according to usual POSIX
  conventions for process exit.
\<close>


subsection \<open>Command \<^verbatim>\<open>use_theories\<close> \label{sec:command-use-theories}\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>use_theories_arguments\<close> \\
  immediate result: & \<^verbatim>\<open>OK\<close> \<open>task\<close> \\
  regular result: & \<^verbatim>\<open>FINISHED\<close> \<open>use_theories_results\<close> \\
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>use_theories_arguments =\<close> \\
  \quad\<open>{session_id: uuid,\<close> \\
  \quad~~\<open>theories: [string],\<close> \\
  \quad~~\<open>master_dir?: string,\<close> & \<^bold>\<open>default:\<close> session \<open>tmp_dir\<close> \\
  \quad~~\<open>pretty_margin?: double,\<close> & \<^bold>\<open>default:\<close> \<^verbatim>\<open>76\<close> \\
  \quad~~\<open>unicode_symbols?: bool,\<close> \\
  \quad~~\<open>export_pattern?: string,\<close> \\
  \quad~~\<open>check_delay?: double,\<close>  & \<^bold>\<open>default:\<close> \<^verbatim>\<open>0.5\<close> \\
  \quad~~\<open>check_limit?: int,\<close> \\
  \quad~~\<open>watchdog_timeout?: double,\<close> & \<^bold>\<open>default:\<close> \<^verbatim>\<open>600.0\<close> \\
  \quad~~\<open>nodes_status_delay?: double}\<close>  & \<^bold>\<open>default:\<close> \<^verbatim>\<open>-1.0\<close> \\
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>export =\<close> \\
  \quad~~\<open>{name: string, base64: bool, body: string}\<close> \\
  \<^bold>\<open>type\<close> \<open>node_results =\<close> \\
  \quad~~\<open>{status: node_status, messages: [message], exports: [export]}\<close> \\
  \<^bold>\<open>type\<close> \<open>nodes_status =\<close> \\
  \quad~~\<open>[node \<oplus> {status: node_status}]\<close> \\
  \<^bold>\<open>type\<close> \<open>use_theories_results =\<close> \\
  \quad\<open>{ok: bool,\<close> \\
  \quad~~\<open>errors: [message],\<close> \\
  \quad~~\<open>nodes: [node \<oplus> node_results]}\<close> \\
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>use_theories\<close> command updates the identified session by adding the
  current version of theory files to it, while dependencies are resolved
  implicitly. The command succeeds eventually, when all theories have status
  \<^emph>\<open>terminated\<close> or \<^emph>\<open>consolidated\<close> in the sense of \<open>node_status\<close>
  (\secref{sec:json-types}).

  Already used theories persist in the session until purged explicitly
  (\secref{sec:command-purge-theories}). This also means that repeated
  invocations of \<^verbatim>\<open>use_theories\<close> are idempotent: it could make sense to do
  that with different values for \<open>pretty_margin\<close> or \<open>unicode_symbols\<close> to get
  different formatting for \<open>errors\<close> or \<open>messages\<close>.

  \<^medskip> A non-empty \<open>export_pattern\<close> means that theory \<open>exports\<close> are retrieved
  (see \secref{sec:tool-export}). An \<open>export\<close> \<open>name\<close> roughly follows
  file-system standards: ``\<^verbatim>\<open>/\<close>'' separated list of base names (excluding
  special names like ``\<^verbatim>\<open>.\<close>'' or ``\<^verbatim>\<open>..\<close>''). The \<open>base64\<close> field specifies the
  format of the \<open>body\<close> string: it is true for a byte vector that cannot be
  represented as plain text in UTF-8 encoding, which means the string needs to
  be decoded as in \<^verbatim>\<open>java.util.Base64.getDecoder.decode(String)\<close>.

  \<^medskip> The status of PIDE processing is checked every \<open>check_delay\<close> seconds, and
  bounded by \<open>check_limit\<close> attempts (default: 0, i.e.\ unbounded). A
  \<open>check_limit > 0\<close> effectively specifies a global timeout of \<open>check_delay \<times>
  check_limit\<close> seconds.

  \<^medskip> If \<open>watchdog_timeout\<close> is greater than 0, it specifies the timespan (in
  seconds) after the last command status change of Isabelle/PIDE, before
  finishing with a potentially non-terminating or deadlocked execution.

  \<^medskip> A non-negative \<open>nodes_status_delay\<close> enables continuous notifications of
  kind \<open>nodes_status\<close>, with a field of name and type \<open>nodes_status\<close>. The time
  interval is specified in seconds; by default it is negative and thus
  disabled.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session_id\<close> is the identifier provided by the server, when the session
  was created (possibly on a different client connection).

  \<^medskip>
  The \<open>theories\<close> field specifies theory names as in theory \<^theory_text>\<open>imports\<close> or in
  ROOT \<^bold>\<open>theories\<close>.

  \<^medskip>
  The \<open>master_dir\<close> field specifies the master directory of imported theories:
  it acts like the ``current working directory'' for locating theory files.
  This is irrelevant for \<open>theories\<close> with an absolute path name (e.g.\
  \<^verbatim>\<open>"~~/src/HOL/Examples/Seq.thy"\<close>) or session-qualified theory name (e.g.\
  \<^verbatim>\<open>"HOL-Examples.Seq"\<close>).

  \<^medskip>
  The \<open>pretty_margin\<close> field specifies the line width for pretty-printing. The
  default is suitable for classic console output. Formatting happens at the
  end of \<^verbatim>\<open>use_theories\<close>, when all prover messages are exported to the client.

  \<^medskip>
  The \<open>unicode_symbols\<close> field set to \<^verbatim>\<open>true\<close> renders message output for direct
  output on a Unicode capable channel, ideally with the Isabelle fonts as in
  Isabelle/jEdit. The default is to keep the symbolic representation of
  Isabelle text, e.g.\ \<^verbatim>\<open>\<forall>\<close> instead of its rendering as \<open>\<forall>\<close>. This means the
  client needs to perform its own rendering before presenting it to the
  end-user.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>ok\<close> field indicates overall success of processing the specified
  theories with all their dependencies.

  When \<open>ok\<close> is \<^verbatim>\<open>false\<close>, the \<open>errors\<close> field lists all errors cumulatively
  (including imported theories). The messages contain position information for
  the original theory nodes.

  \<^medskip>
  The \<open>nodes\<close> field provides detailed information about each imported theory
  node. The individual fields are as follows:

  \<^item> \<open>node_name\<close>: the canonical name for the theory node, based on its
  file-system location;

  \<^item> \<open>theory_name\<close>: the logical theory name;

  \<^item> \<open>status\<close>: the overall node status, e.g.\ see the visualization in the
  \<open>Theories\<close> panel of Isabelle/jEdit @{cite "isabelle-jedit"};

  \<^item> \<open>messages\<close>: the main bulk of prover messages produced in this theory
  (with kind \<^verbatim>\<open>writeln\<close>, \<^verbatim>\<open>warning\<close>, \<^verbatim>\<open>error\<close>).
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Process some example theory from the Isabelle distribution, within the
  context of an already started session for Isabelle/HOL (see also
  \secref{sec:command-session-start}):
  @{verbatim [display] \<open>use_theories {"session_id": ..., "theories": ["~~/src/HOL/Examples/Seq"]}\<close>}

  \<^medskip>
  Process some example theories in the context of their (single) parent
  session:

  @{verbatim [display] \<open>session_start {"session": "HOL-Library"}
use_theories {"session_id": ..., "theories": ["~~/src/HOL/Unix/Unix"]}
session_stop {"session_id": ...}\<close>}

  \<^medskip>
  Process some example theories that import other theories via
  session-qualified theory names:

  @{verbatim [display] \<open>session_start {"session": "HOL", "include_sessions": ["HOL-Unix"]}
use_theories {"session_id": ..., "theories": ["HOL-Unix.Unix"]}
session_stop {"session_id": ...}\<close>}
\<close>


subsection \<open>Command \<^verbatim>\<open>purge_theories\<close> \label{sec:command-purge-theories}\<close>

text \<open>
  \begin{tabular}{ll}
  argument: & \<open>purge_theories_arguments\<close> \\
  regular result: & \<^verbatim>\<open>OK\<close> \<open>purge_theories_result\<close> \\
  \end{tabular}

  \begin{tabular}{lll}
  \<^bold>\<open>type\<close> \<open>purge_theories_arguments =\<close> \\
  \quad\<open>{session_id: uuid,\<close> \\
  \quad~~\<open>theories: [string],\<close> \\
  \quad~~\<open>master_dir?: string,\<close> & \<^bold>\<open>default:\<close> session \<open>tmp_dir\<close> \\
  \quad~~\<open>all?: bool}\<close> \\[2ex]
  \end{tabular}

  \begin{tabular}{ll}
  \<^bold>\<open>type\<close> \<open>purge_theories_result = {purged: [string]}\<close> \\
  \end{tabular}

  \<^medskip>
  The \<^verbatim>\<open>purge_theories\<close> command updates the identified session by removing
  theories that are no longer required: theories that are used in pending
  \<^verbatim>\<open>use_theories\<close> tasks or imported by other theories are retained.
\<close>


subsubsection \<open>Arguments\<close>

text \<open>
  The \<open>session_id\<close> is the identifier provided by the server, when the session
  was created (possibly on a different client connection).

  \<^medskip>
  The \<open>theories\<close> field specifies theory names to be purged: imported
  dependencies are \<^emph>\<open>not\<close> completed. Instead it is possible to provide the
  already completed import graph returned by \<^verbatim>\<open>use_theories\<close> as \<open>nodes\<close> /
  \<open>node_name\<close>.

  \<^medskip>
  The \<open>master_dir\<close> field specifies the master directory as in \<^verbatim>\<open>use_theories\<close>.
  This is irrelevant, when passing fully-qualified theory node names (e.g.\
  \<open>node_name\<close> from \<open>nodes\<close> in \<open>use_theories_results\<close>).

  \<^medskip>
  The \<open>all\<close> field set to \<^verbatim>\<open>true\<close> attempts to purge all presently loaded
  theories.
\<close>


subsubsection \<open>Results\<close>

text \<open>
  The \<open>purged\<close> field gives the theory nodes that were actually removed.

  \<^medskip>
  The \<open>retained\<close> field gives the remaining theory nodes, i.e.\ the complement
  of \<open>purged\<close>.
\<close>

end
