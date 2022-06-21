(*  Title:      Pure/General/bytes.ML
    Author:     Makarius

Scalable byte strings, with incremental construction (add content to the
end). Note: type string is implicitly limited by String.maxSize (approx. 64
MB on 64_32 architecture).
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
  val add: string -> T -> T
  val build: (T -> T) -> T
  val string: string -> T
  val buffer: Buffer.T -> T
  val read: Path.T -> T
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

fun add "" bytes = bytes
  | add s (Bytes {buffer, chunks, m, n}) =
      let val l = size s in
        if l + m < chunk_size
        then Bytes {buffer = s :: buffer, chunks = chunks, m = l + m, n = n}
        else
          let
            val k = chunk_size - m;
            val chunk = compact (String.substring (s, 0, k) :: buffer);
            val s' = String.substring (s, k, l - k);
            val bytes' = Bytes {buffer = [], chunks = chunk :: chunks, m = 0, n = chunk_size + n};
          in add s' bytes' end
      end;

end;

fun build (f: T -> T) = f empty;

val string = build o add;

val buffer = build o fold add o Buffer.contents;

fun read_chunk stream =
  Byte.bytesToString (BinIO.inputN (stream, chunk_size));

val read = File.open_input (fn stream =>
  let
    fun read_bytes bytes =
      (case read_chunk stream of
        "" => bytes
      | s => read_bytes (add s bytes))
  in read_bytes empty end);

end;
