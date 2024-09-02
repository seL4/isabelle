(*  Title:      Pure/General/bytes.ML
    Author:     Makarius

Scalable byte strings, with incremental construction (add content to the
end).

Note: type string is implicitly limited by String.maxSize (approx. 64 MB on
64_32 architecture).
*)

signature BYTES =
sig
  val chunk_size: int
  type T
  val eq: T * T -> bool
  val size: T -> int
  val contents: T -> string list
  val contents_blob: T -> XML.body
  val content: T -> string
  val is_empty: T -> bool
  val empty: T
  val build: (T -> T) -> T
  val add_substring: substring -> T -> T
  val add: string -> T -> T
  val beginning: int -> T -> string
  val exists_string: (string -> bool) -> T -> bool
  val forall_string: (string -> bool) -> T -> bool
  val last_string: T -> string option
  val trim_line: T -> T
  val append: T -> T -> T
  val appends: T list -> T
  val string: string -> T
  val newline: T
  val buffer: Buffer.T -> T
  val space_explode: string -> T -> string list
  val split_lines: T -> string list
  val trim_split_lines: T -> string list
  val cat_lines: string list -> T
  val read_block: int -> BinIO.instream -> string
  val read_stream: int -> BinIO.instream -> T
  val write_stream: BinIO.outstream -> T -> unit
  val read: Path.T -> T
  val write: Path.T -> T -> unit
end;

structure Bytes: BYTES =
struct

(* primitive operations *)

val chunk_size = 65000;

abstype T = Bytes of
  {buffer: string list, chunks: string list, m: int (*buffer size*), n: int (*chunks size*)}
with

fun size (Bytes {m, n, ...}) = m + n;

val compact = implode o rev;

fun eq (Bytes {buffer, chunks, m, n}, Bytes {buffer = buffer', chunks = chunks', m = m', n = n'}) =
  m = m' andalso n = n' andalso chunks = chunks' andalso
  (buffer = buffer' orelse compact buffer = compact buffer);

fun contents (Bytes {buffer, chunks, ...}) =
  rev (chunks |> not (null buffer) ? cons (compact buffer));

val contents_blob = contents #> map XML.Text;

val content = implode o contents;

fun is_empty bytes = size bytes = 0;

val empty = Bytes {buffer = [], chunks = [], m = 0, n = 0};

fun build (f: T -> T) = f empty;

fun add_substring s (bytes as Bytes {buffer, chunks, m, n}) =
  if Substring.isEmpty s then bytes
  else
    let val l = Substring.size s in
      if l + m < chunk_size
      then Bytes {buffer = Substring.string s :: buffer, chunks = chunks, m = l + m, n = n}
      else
        let
          val k = chunk_size - m;
          val chunk = compact (Substring.string (Substring.slice (s, 0, SOME k)) :: buffer);
          val s' = Substring.slice (s, k, SOME (l - k));
          val bytes' = Bytes {buffer = [], chunks = chunk :: chunks, m = 0, n = chunk_size + n};
        in add_substring s' bytes' end
    end;

val add = add_substring o Substring.full;

fun exists_string pred (Bytes {buffer, chunks, ...}) =
  let val ex = (exists o Library.exists_string) pred
  in ex buffer orelse ex chunks end;

fun forall_string pred = not o exists_string (not o pred);

fun last_string (Bytes {buffer, chunks, ...}) =
  (case buffer of
    s :: _ => Library.last_string s
  | [] =>
      (case chunks of
        s :: _ => Library.last_string s
      | [] => NONE));

fun trim_line (bytes as Bytes {buffer, chunks, ...}) =
  let
    val is_line =
      (case last_string bytes of
        SOME s => Symbol.is_ascii_line_terminator s
      | NONE => false);
  in
    if is_line then
      let
        val (last_chunk, chunks') =
          (case chunks of
            [] => ("", [])
          | c :: cs => (c, cs));
        val trimed = Library.trim_line (last_chunk ^ compact buffer);
      in build (fold_rev add chunks' #> add trimed) end
    else bytes
  end;

end;


(* derived operations *)

fun beginning n bytes =
  let
    val dots = " ...";
    val m = (String.maxSize - String.size dots) div chunk_size;
    val a = implode (take m (contents bytes));
    val b = String.substring (a, 0, Int.min (n, String.size a));
  in if String.size b < size bytes then b ^ dots else b end;

fun append bytes1 bytes2 =  (*left-associative*)
  if is_empty bytes1 then bytes2
  else if is_empty bytes2 then bytes1
  else bytes1 |> fold add (contents bytes2);

val appends = build o fold (fn b => fn a => append a b);

val string = build o add;

val newline = string "\n";

val buffer = build o fold add o Buffer.contents;


(* space_explode *)

fun space_explode sep bytes =
  if is_empty bytes then []
  else if String.size sep <> 1 then [content bytes]
  else
    let
      val sep_char = String.nth sep 0;

      fun add_part s part =
        Buffer.add (Substring.string s) (the_default Buffer.empty part);

      fun explode head tail part res =
        if Substring.isEmpty head then
          (case tail of
            [] =>
              (case part of
                NONE => rev res
              | SOME buf => rev (Buffer.content buf :: res))
          | chunk :: chunks => explode (Substring.full chunk) chunks part res)
        else
          (case Substring.fields (fn c => c = sep_char) head of
            [a] => explode Substring.empty tail (SOME (add_part a part)) res
          | a :: rest =>
              let
                val (bs, c) = split_last rest;
                val res' = res
                  |> cons (Buffer.content (add_part a part))
                  |> fold (cons o Substring.string) bs;
                val part' = SOME (add_part c NONE);
              in explode Substring.empty tail part' res' end)
    in explode Substring.empty (contents bytes) NONE [] end;

val split_lines = space_explode "\n";

val trim_split_lines = trim_line #> split_lines #> map Library.trim_line;

fun cat_lines lines = build (fold add (separate "\n" lines));


(* IO *)

fun read_block limit =
  File_Stream.input_size (if limit < 0 then chunk_size else Int.min (chunk_size, limit));

fun read_stream limit stream =
  let
    fun read bytes =
      (case read_block (limit - size bytes) stream of
        "" => bytes
      | s => read (add s bytes))
  in read empty end;

fun write_stream stream bytes =
  File_Stream.outputs stream (contents bytes);

fun read path = File_Stream.open_input (fn stream => read_stream ~1 stream) path;

fun write path bytes = File_Stream.open_output (fn stream => write_stream stream bytes) path;

end;
