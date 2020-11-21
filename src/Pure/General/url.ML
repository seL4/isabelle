(*  Title:      Pure/General/url.ML
    Author:     Makarius

Basic URLs (see RFC 1738 and RFC 2396).
*)

signature URL =
sig
  datatype T =
    File of Path.T |
    Http of string * Path.T |
    Https of string * Path.T |
    Ftp of string * Path.T
  val explode: string -> T
end;

structure Url: URL =
struct

(* type url *)

datatype T =
  File of Path.T |
  Http of string * Path.T |
  Https of string * Path.T |
  Ftp of string * Path.T;


(* explode *)

local

val scan_host =
  (Scan.many1 (fn s => s <> "/" andalso Symbol.not_eof s) >> implode) --|
  Scan.ahead ($$ "/" || Scan.one Symbol.is_eof);

val scan_path = Scan.many Symbol.not_eof >> (Path.explode o implode);
val scan_path_root = Scan.many Symbol.not_eof >> (Path.explode o implode o cons "/");

val scan_url =
  Scan.unless
    (Scan.this_string "file:" || Scan.this_string "http:" ||
      Scan.this_string "https:" || Scan.this_string "ftp:") scan_path >> File ||
  Scan.this_string "file:///" |-- scan_path_root >> File ||
  Scan.this_string "file://localhost/" |-- scan_path_root >> File ||
  Scan.this_string "file://" |-- scan_host -- scan_path
    >> (fn (h, p) => File (Path.named_root h + p)) ||
  Scan.this_string "file:/" |-- scan_path_root >> File ||
  Scan.this_string "http://" |-- scan_host -- scan_path >> Http ||
  Scan.this_string "https://" |-- scan_host -- scan_path >> Https ||
  Scan.this_string "ftp://" |-- scan_host -- scan_path >> Ftp;

in

fun explode s = Symbol.scanner "Malformed URL" scan_url (Symbol.explode s);

end;

end;
