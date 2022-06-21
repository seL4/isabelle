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
  val length: T -> int
  val contents: T -> string list
  val content: T -> string
  val is_empty: T -> bool
  val empty: T
  val add_substring: substring -> T -> T
  val add: string -> T -> T
  val append: T -> T -> T
  val build: (T -> T) -> T
  val string: string -> T
  val buffer: Buffer.T -> T
  val read_chunk: BinIO.instream -> string
  val read_stream: BinIO.instream -> T
  val write_stream: BinIO.outstream -> T -> unit
  val read: Path.T -> T
  val write: Path.T -> T -> unit
end;

structure Bytes: BYTES =
struct

val chunk_size = 1024 * 1024;

abstype T = Bytes of
  {buffer: string list, chunks: string list, m: int (*buffer size*), n: int (*chunks size*)}
with

fun length (Bytes {m, n, ...}) = m + n;

val compact = implode o rev;

fun contents (Bytes {buffer, chunks, ...}) =
  rev (chunks |> not (null buffer) ? cons (compact buffer));

val content = implode o contents;

fun is_empty bytes = length bytes = 0;

val empty = Bytes {buffer = [], chunks = [], m = 0, n = 0};

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

end;

fun append bytes1 bytes2 =  (*left-associative*)
  if is_empty bytes1 then bytes2
  else if is_empty bytes2 then bytes1
  else bytes1 |> fold add (contents bytes2);

fun build (f: T -> T) = f empty;

val string = build o add;

val buffer = build o fold add o Buffer.contents;

val read_chunk = File.input_size chunk_size;

fun read_stream stream =
  let
    fun read_bytes bytes =
      (case read_chunk stream of
        "" => bytes
      | s => read_bytes (add s bytes))
  in read_bytes empty end;

fun write_stream stream = File.outputs stream o contents;

val read = File.open_input read_stream;
val write = File.open_output write_stream;

end;
