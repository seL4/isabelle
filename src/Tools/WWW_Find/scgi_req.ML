(*  Title:      Tools/WWW_Find/scgi_req.ML
    Author:     Timothy Bourke, NICTA

Parses an SCGI (Simple Common Gateway Interface) header.
See: http://python.ca/scgi/protocol.txt
*)

signature SCGI_REQ =
sig
  exception InvalidReq of string

  datatype req_method = Get | Head | Post

  datatype t = Req of {
      path_info : string,
      path_translated : string,
      script_name : string,
      request_method : req_method,
      query_string : string Symtab.table,
      content_type : Mime.t option,
      environment : Word8VectorSlice.slice Symtab.table
    }

  val parse : BinIO.instream ->  t * (BinIO.instream * int)
  val test : string -> unit

  val show : t -> string
end;

structure ScgiReq : SCGI_REQ =
struct

exception InvalidReq of string;

datatype req_method = Get | Head | Post;

datatype t = Req of {
    path_info : string,
    path_translated : string,
    script_name : string,
    request_method : req_method,
    query_string : string Symtab.table,
    content_type : Mime.t option,
    environment : Word8VectorSlice.slice Symtab.table
  };

fun parse_req_method "POST" = Post
  | parse_req_method "HEAD" = Head
  | parse_req_method _ = Get;

fun show_req_method Get = "Get"
  | show_req_method Post = "Post"
  | show_req_method Head = "Head";

fun find_nulls (idx, 0wx00, idxs) = idx::idxs
  | find_nulls (_, _, idxs) = idxs;

fun read_net_string fin =
  let
    fun read_size (_, NONE) = raise InvalidReq "Bad netstring length."
      | read_size (t, SOME 0wx3a) = t
      | read_size (t, SOME d) =
          let
            val n = (Word8.toInt d) - 0x30;
          in
            if n >=0 andalso n <= 9
            then read_size (t * 10 + n, BinIO.input1 fin)
            else read_size (t, NONE)
          end;
    val size = read_size (0, BinIO.input1 fin);
    val payload = BinIO.inputN (fin, size);
  in
    (case (Word8Vector.length payload = size, BinIO.input1 fin) of
       (true, SOME 0wx2c) => payload
     | _ => raise InvalidReq "Bad netstring.")
  end;

fun split_fields vec =
  let
    val nulls = ~1 :: (Word8Vector.foldri find_nulls [] vec);

    fun pr NONE = "NONE"
      | pr (SOME i) = "SOME " ^ Int.toString i;

    fun hd_diff (i1::i2::_) = SOME (i2 - i1 - 1)
      | hd_diff _ = NONE;

    fun slice [] = []
      | slice (idxs as idx::idxs') =
          Word8VectorSlice.slice (vec, idx + 1, hd_diff idxs) :: slice idxs';

    fun make_pairs (x::y::xys) = (Byte.unpackStringVec x, y) :: make_pairs xys
      | make_pairs _ = [];

  in make_pairs (slice nulls) end;

fun parse fin =
  let
    val raw_fields = read_net_string fin;
    val fields = split_fields raw_fields;
    val env = Symtab.make fields;

    fun field name =
      (case Symtab.lookup env name of
         NONE => ""
       | SOME wv => Byte.unpackStringVec wv);

    val content_length =
      (the o Int.fromString o field) "CONTENT_LENGTH"
      handle _ => raise InvalidReq "Bad CONTENT_LENGTH";

    val req = Req {
        path_info = field "PATH_INFO",
        path_translated = field "PATH_TRANSLATED",
        script_name = field "SCRIPT_NAME",
        request_method = (parse_req_method o field) "REQUEST_METHOD",
        query_string = (HttpUtil.parse_query_string o field) "QUERY_STRING",
        content_type = (Mime.parse_type o field) "CONTENT_TYPE",
        environment = env
      }

   in (req, (fin, content_length)) end; 

fun show (Req {path_info, path_translated, script_name,
               request_method, query_string, content_type, environment}) =
  let
    fun show_symtab to_string table = let
        fun show (n, v) r = ["\t", n, " = \"", to_string v, "\"\n"] @ r;
      in Symtab.fold show table [] end;
  in
    concat
      (["path_info: \"", path_info, "\"\n",
        "path_translated: \"", path_translated, "\"\n",
        "script_name: \"", script_name, "\"\n",
        "request_method: \"", show_req_method request_method, "\"\n",
        "query_string:\n"]
       @
       show_symtab I query_string
       @
       ["content_type: ",
          (the_default "" o Option.map Mime.show_type) content_type, "\n",
        "environment:\n"]
       @
       show_symtab Byte.unpackStringVec environment)
  end;

fun test path =
  let
    val fin = BinIO.openIn path;
    val (req, cs) = parse fin;
    val () = TextIO.print (show req);
    val () =
      BinIO.inputN cs
      |> Word8VectorSlice.full
      |> Byte.unpackStringVec
      |> TextIO.print;
  in BinIO.closeIn fin end;

end;

