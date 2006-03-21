(*  Title:      Pure/General/url.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic URLs, see RFC 1738.
*)

signature URL =
sig
  datatype T =
    File of Path.T |
    RemoteFile of string * Path.T |
    Http of string * Path.T |
    Ftp of string * Path.T
  val append: T -> T -> T
  val pack: T -> string
  val unpack: string -> T
end;

structure Url: URL =
struct

(* type url *)

datatype T =
  File of Path.T |
  RemoteFile of string * Path.T |
  Http of string * Path.T |
  Ftp of string * Path.T;


(* append *)

fun append (File p)            (File p') = File (Path.append p p')
  | append (RemoteFile (h, p)) (File p') = RemoteFile (h, Path.append p p')
  | append (Http (h, p))       (File p') = Http (h, Path.append p p')
  | append (Ftp (h, p))        (File p') = Ftp (h, Path.append p p')
  | append _ url = url;


(* pack *)

fun pack_path p = if Path.is_current p then "" else Path.pack p;

fun pack (File p) = pack_path p
  | pack (RemoteFile (h, p)) = "file://" ^ h ^ pack_path p
  | pack (Http (h, p)) = "http://" ^ h ^ pack_path p
  | pack (Ftp (h, p)) = "ftp://" ^ h ^ pack_path p;


(* unpack *)

local

val scan_host =
  (Scan.any1 (fn s => s <> "/" andalso Symbol.not_eof s) >> implode) --|
  Scan.ahead ($$ "/" || Scan.one Symbol.is_eof);

val scan_path = Scan.any Symbol.not_eof >> (Path.unpack o implode);
val scan_path_root = Scan.any Symbol.not_eof >> (Path.unpack o implode o cons "/");

val scan_url =
  Scan.unless (Scan.this_string "file:" ||
    Scan.this_string "http:" || Scan.this_string "ftp:") scan_path >> File ||
  Scan.this_string "file:///" |-- scan_path_root >> File ||
  Scan.this_string "file://localhost/" |-- scan_path_root >> File ||
  Scan.this_string "file://" |-- scan_host -- scan_path >> RemoteFile ||
  Scan.this_string "http://" |-- scan_host -- scan_path >> Http ||
  Scan.this_string "ftp://" |-- scan_host -- scan_path >> Ftp;

in

fun unpack s = Symbol.scanner "Malformed URL" scan_url (Symbol.explode s);

end;

end;
