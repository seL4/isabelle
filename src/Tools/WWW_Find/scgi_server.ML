(*  Title:      Tools/WWW_Find/scgi_server.ML
    Author:     Timothy Bourke, NICTA

Simple SCGI server.
*)

signature SCGI_SERVER =
sig
  val max_threads : int Unsynchronized.ref
  type handler = ScgiReq.t * Word8Vector.vector * (string -> unit) -> unit
  val register : (string * Mime.t option * handler) -> unit
  val server : string -> int -> unit
  val server' : int -> string -> int -> unit (* keeps trying for port *)
  val simple_handler : (string Symtab.table -> (string -> unit) -> unit) -> handler
  val raw_post_handler : (string -> string) -> handler
end;

structure ScgiServer : SCGI_SERVER =
struct
val max_threads = Unsynchronized.ref 5;

type handler = ScgiReq.t * Word8Vector.vector * (string -> unit) -> unit;

local
val servers = Unsynchronized.ref (Symtab.empty : (Mime.t option * handler) Symtab.table);
in
fun register (name, mime, f) =
  Unsynchronized.change servers (Symtab.update_new (name, (mime, f)));
fun lookup name = Symtab.lookup (!servers) name;

fun dump_handlers () = (
    tracing("  with handlers:");
    app (fn (x, _) => tracing ("    - " ^ x)) (Symtab.dest (!servers)))
end;

fun server server_prefix port =
  let
    val passive_sock = Socket_Util.init_server_socket (SOME "localhost") port;

    val thread_wait = ConditionVar.conditionVar ();
    val thread_wait_mutex = Mutex.mutex ();

    local
    val threads = Unsynchronized.ref ([] : Thread.thread list);
    fun purge () = Unsynchronized.change threads (filter Thread.isActive);
    in
    fun add_thread th = Unsynchronized.change threads (cons th);

    fun launch_thread threadf =
      (purge ();
       if length (!threads) < (!max_threads) then ()
       else (tracing ("Waiting for a free thread...");
             ConditionVar.wait (thread_wait, thread_wait_mutex));
       add_thread
         (Thread.fork   (* FIXME avoid low-level Poly/ML thread primitives *)
            (fn () => exception_trace threadf,
             [Thread.EnableBroadcastInterrupt true,
              Thread.InterruptState
              Thread.InterruptAsynchOnce])))
    end;

    fun loop () =
      let
        val (sock, _)= Socket.accept passive_sock;

        val (sin, sout) = Socket_Util.make_streams sock;

        fun send msg = BinIO.output (sout, Byte.stringToBytes msg);
        fun send_log msg = (tracing msg; send msg);

        fun get_content (st, 0) = Word8Vector.fromList []
          | get_content x = BinIO.inputN x;

        fun do_req () =
          let
            val (req as ScgiReq.Req {path_info, request_method, ...},
                 content_is) =
              ScgiReq.parse sin
              handle ScgiReq.InvalidReq s =>
                (send
                   (HttpUtil.reply_header (HttpStatus.bad_request, NONE, []));
                 raise Fail ("Invalid request: " ^ s));
            val () = tracing ("request: " ^ path_info);
          in
            (case lookup (unprefix server_prefix path_info) of
               NONE => send (HttpUtil.reply_header (HttpStatus.not_found, NONE, []))
             | SOME (NONE, f) => f (req, get_content content_is, send)
             | SOME (t, f) =>
                (send (HttpUtil.reply_header (HttpStatus.ok, t, []));
                 if request_method = ScgiReq.Head then ()
                 else f (req, get_content content_is, send)))
          end;

        fun thread_req () =  (* FIXME avoid handle e *)
          (do_req () handle e => (warning (exnMessage e));
           BinIO.closeOut sout handle e => warning (exnMessage e);
           BinIO.closeIn sin handle e => warning (exnMessage e);
           Socket.close sock handle e => warning (exnMessage e);
           tracing ("request done.");
           ConditionVar.signal thread_wait);
      in
        launch_thread thread_req;
        loop ()
      end;
  in
    tracing ("SCGI server started.");
    dump_handlers ();
    loop ();
    Socket.close passive_sock
  end;

local
val delay = 5;
in
fun server' 0 server_prefix port = (warning "Giving up."; exit 1)
  | server' countdown server_prefix port =
      server server_prefix port
        handle OS.SysErr ("bind failed", _) =>
          (warning ("Could not acquire port "
                    ^ string_of_int port ^ ". Trying again in "
                    ^ string_of_int delay ^ " seconds...");
           OS.Process.sleep (Time.fromSeconds delay);
           server' (countdown - 1) server_prefix port);
end;

fun simple_handler h (ScgiReq.Req {request_method, query_string, ...}, content, send) =
  h (case request_method of
     ScgiReq.Get => query_string
   | ScgiReq.Post =>
      content
      |> Byte.bytesToString
      |> HttpUtil.parse_query_string
   | ScgiReq.Head => raise Fail "Cannot handle Head requests.")
  send;

fun raw_post_handler h (ScgiReq.Req {request_method=ScgiReq.Post, ...}, content, send) =
      send (h (Byte.bytesToString content))
  | raw_post_handler _ _ = raise Fail "Can only handle POST request.";

end;

