(*  Title:      Pure/General/url.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Basic URLs.
*)

signature URL =
sig
  type T
  val file: Path.T -> T
  val http: string * Path.T -> T
  val ftp: string * Path.T -> T
  val append: T -> T -> T
  val pack: T -> string
  val unpack: string -> T
end;

structure Url: URL =
struct


(* type url *)

datatype scheme = File | Http of string | Ftp of string;

datatype T = Url of scheme * Path.T;

fun file p = Url (File, p);
fun http (h, p) = Url (Http h, p);
fun ftp (h, p) = Url (Ftp h, p);


(* append *)

fun append (Url (s, p)) (Url (File, p')) = Url (s, Path.append p p')
  | append _ url = url;


(* pack *)

fun pack_scheme File = ""
  | pack_scheme (Http host) = "http://" ^ host
  | pack_scheme (Ftp host) = "ftp://" ^ host;

fun pack (Url (s, p)) = pack_scheme s ^ (if Path.is_current p then "" else Path.pack p);


(* unpack *)

fun scan_lits [] x = ("", x)
  | scan_lits (c :: cs) x = (($$ c -- scan_lits cs) >> op ^) x;

val scan_literal = scan_lits o Symbol.explode;

val scan_path = Scan.any Symbol.not_eof >> (Path.unpack o implode);
val scan_host = Scan.any1 (not_equal "/" andf Symbol.not_eof) >> implode;

val scan_url =
  scan_literal "http://" |-- scan_host -- scan_path >> http ||
  scan_literal "ftp://" |-- scan_host -- scan_path >> ftp ||
  Scan.unless (scan_literal "http:" || scan_literal "ftp:") scan_path >> file;

fun unpack s = Symbol.scanner "Malformed URL" scan_url (Symbol.explode s);


end;
