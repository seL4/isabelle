(*  Title:      Pure/General/symbol.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generalized characters with infinitely many named symbols.
*)

signature SYMBOL =
sig
  type symbol
  val space: symbol
  val spaces: int -> symbol
  val sync: symbol
  val is_sync: symbol -> bool
  val not_sync: symbol -> bool
  val malformed: symbol
  val eof: symbol
  val is_eof: symbol -> bool
  val not_eof: symbol -> bool
  val stopper: symbol * (symbol -> bool)
  val is_ascii: symbol -> bool
  val is_letter: symbol -> bool
  val is_digit: symbol -> bool
  val is_quasi: symbol -> bool
  val is_quasi_letter: symbol -> bool
  val is_letdig: symbol -> bool
  val is_blank: symbol -> bool
  val is_identifier: symbol -> bool
  val is_symbolic: symbol -> bool
  val is_printable: symbol -> bool
  val length: symbol list -> int
  val strip_blanks: string -> string
  val beginning: symbol list -> string
  val scan_id: string list -> string * string list
  val scan: string list -> symbol * string list
  val scanner: string -> (symbol list -> 'a * symbol list) -> symbol list -> 'a
  val source: bool -> (string, 'a) Source.source ->
    (symbol, (string, 'a) Source.source) Source.source
  val explode: string -> symbol list
  val bump_string: string -> string
  val default_indent: string * int -> string
  val add_mode: string -> (string -> string * real) * (string * int -> string) -> unit
  val symbolsN: string
  val xsymbolsN: string
  val plain_output: string -> string
  val output: string -> string
  val output_width: string -> string * real
  val indent: string * int -> string
end;

structure Symbol: SYMBOL =
struct


(** generalized characters **)

(*symbols, which are considered the smallest entities of any Isabelle
  string, may be of the following form:
    (a) ASCII symbols: a
    (b) printable symbols: \<ident>
    (c) control symbols: \<^ident>

  output is subject to the print_mode variable (default: verbatim),
  actual interpretation in display is up to front-end tools;
*)

type symbol = string;

val space = " ";
fun spaces k = Library.replicate_string k space;
val sync = "\\<^sync>";
val malformed = "\\<^malformed>";
val eof = "";


(* kinds *)

fun is_sync s = s = sync;
fun not_sync s = s <> sync;

fun is_eof s = s = eof;
fun not_eof s = s <> eof;
val stopper = (eof, is_eof);

fun is_ascii s = size s = 1 andalso ord s < 128;

local
    fun wrap s = "\\<" ^ s ^ ">"

    val cal_letters =
	["A","B","C","D","E","F","G","H","I","J","K","L","M",
	 "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]

    val small_letters =
	["a","b","c","d","e","f","g","h","i","j","k","l","m",
	 "n","o","p","q","r","s","t","u","v","w","x","y","z"]

    val goth_letters =
	["AA","BB","CC","DD","EE","FF","GG","HH","II","JJ","KK","LL","MM",
	 "NN","OO","PP","QQ","RR","SS","TT","UU","VV","WW","XX","YY","ZZ",
	 "aa","bb","cc","dd","ee","ff","gg","hh","ii","jj","kk","ll","mm",
	 "nn","oo","pp","qq","rr","ss","tt","uu","vv","ww","xx","yy","zz"]

    val greek_letters =
	["alpha","beta","gamma","delta","epsilon","zeta","eta","theta",
	 "iota","kappa",(*"lambda",*)"mu","nu","xi","pi","rho","sigma","tau",
	 "upsilon","phi","psi","omega","Gamma","Delta","Theta","Lambda",
	 "Xi","Pi","Sigma","Upsilon","Phi","Psi","Omega"]

    val bbb_letters = ["bool","complex","nat","rat","real","int"]

    val pre_letters =
	cal_letters   @
	small_letters @
	goth_letters  @
	greek_letters
in
val ext_letters = map wrap pre_letters

fun is_ext_letter s = String.isPrefix "\\<" s andalso s mem ext_letters
end
     
fun is_letter s =
    (size s = 1 andalso
     (ord "A" <= ord s andalso ord s <= ord "Z" orelse
      ord "a" <= ord s andalso ord s <= ord "z"))
    orelse is_ext_letter s

fun is_digit s =
    size s = 1 andalso ord "0" <= ord s andalso ord s <= ord "9"

fun is_quasi "_" = true
  | is_quasi "'" = true
  | is_quasi _ = false;

fun is_quasi_letter s = is_quasi s orelse is_letter s;

val is_blank =
  fn " " => true | "\t" => true | "\r" => true | "\n" => true | "\^L" => true
    | "\160" => true | "\\<spacespace>" => true
    | _ => false;

fun is_letdig s = is_quasi_letter s orelse is_digit s;

fun is_symbolic s =
  size s > 2 andalso nth_elem_string (2, s) <> "^"
  andalso not (is_ext_letter s);

fun is_printable s =
  size s = 1 andalso ord space <= ord s andalso ord s <= ord "~" orelse
  is_ext_letter s orelse
  is_symbolic s;

fun is_identifier s =
  case (explode s) of
      [] => false
    | c::cs => is_letter c andalso forall is_letdig cs;

fun sym_length ss = foldl (fn (n, s) =>
  (if not (is_printable s) then 0 else
    (case Library.try String.substring (s, 2, 4) of
      Some s' => if s' = "long" orelse s' = "Long" then 2 else 1
    | None => 1)) + n) (0, ss);

fun strip_blanks s =
  implode (#1 (Library.take_suffix is_blank (#2 (Library.take_prefix is_blank (explode s)))));


(* beginning *)

val smash_blanks = map (fn s => if is_blank s then space else s);

fun beginning raw_ss =
  let
    val (all_ss, _) = take_suffix is_blank raw_ss;
    val dots = if length all_ss > 10 then " ..." else "";
    val (ss, _) = take_suffix is_blank (take (10, all_ss));
  in implode (smash_blanks ss) ^ dots end;



(** scanning through symbols **)

fun scanner msg scan chs =
  let
    fun err_msg cs = msg ^ ": " ^ beginning cs;
    val fin_scan = Scan.error (Scan.finite stopper (!! (fn (cs, _) => err_msg cs) scan));
  in
    (case fin_scan chs of
      (result, []) => result
    | (_, rest) => error (err_msg rest))
  end;



(** symbol input **)

(* scan *)

val scan_id = Scan.one is_letter ^^ (Scan.any is_letdig >> implode);

val scan =
  ($$ "\\" --| Scan.optional ($$ "\\") "") ^^ $$ "<" ^^
    !! (fn (cs, _) => "Malformed symbolic character specification: \\" ^ "<" ^ beginning cs)
      (Scan.optional ($$ "^") "" ^^ scan_id ^^ $$ ">") ||
  Scan.one not_eof;


(* source *)

val recover = Scan.any ((not o is_blank) andf not_eof) >> K [malformed];

fun source do_recover src =
  Source.source stopper (Scan.bulk scan) (if do_recover then Some recover else None) src;


(* explode *)

fun no_syms [] = true
  | no_syms ("\\" :: "<" :: _) = false
  | no_syms (_ :: cs) = no_syms cs;

fun sym_explode str =
  let val chs = explode str in
    if no_syms chs then chs     (*tune trivial case*)
    else the (Scan.read stopper (Scan.repeat scan) chs)
  end;


(* bump_string -- increment suffix of lowercase letters like a base 26 number *)

fun bump_string str =
  let
    fun bump [] = ["a"]
      | bump ("z" :: ss) = "a" :: bump ss
      | bump (s :: ss) =
          if size s = 1 andalso ord "a" <= ord s andalso ord s < ord "z"
          then chr (ord s + 1) :: ss
          else "a" :: s :: ss;
    val (cs, qs) = Library.take_suffix is_quasi (sym_explode str);
  in implode (rev (bump (rev cs)) @ qs) end;


(** symbol output **)

(* default *)

fun string_size s = (s, real (size s));

val escape = Scan.repeat
  ((($$ "\\" >> K "\\\\") ^^ Scan.optional ($$ "\\" >> K "\\\\") "" ^^ $$ "<" ^^
      Scan.optional ($$ "^") "" ^^ scan_id ^^ $$ ">") ||
   Scan.one not_eof) >> implode;

fun default_output s =
  if not (exists_string (equal "\\") s) then string_size s
  else string_size (fst (Scan.finite stopper escape (explode s)));

fun default_indent (_: string, k) = spaces k;


(* maintain modes *)

val symbolsN = "symbols";
val xsymbolsN = "xsymbols";

val modes =
  ref (Symtab.empty: ((string -> string * real) * (string * int -> string)) Symtab.table);

fun lookup_mode name = Symtab.lookup (! modes, name);

fun add_mode name m =
 (if is_none (lookup_mode name) then ()
  else warning ("Redeclaration of symbol print mode " ^ quote name);
  modes := Symtab.update ((name, m), ! modes));

fun get_mode () =
  if_none (get_first lookup_mode (! print_mode)) (default_output, default_indent);


(* mode output *)

fun output_width x = #1 (get_mode ()) x;
val output = #1 o output_width;
val plain_output = #1 o default_output;

fun indent x = #2 (get_mode ()) x;


(*final declarations of this structure!*)
val length = sym_length;
val explode = sym_explode;


end;
