(*  Title:      Pure/General/symbol.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generalized characters with and infinite amount of named symbols.
*)

signature SYMBOL =
sig
  type symbol
  val space: symbol
  val spaces: int -> symbol
  val is_char: symbol -> bool
  val is_symbolic: symbol -> bool
  val is_printable: symbol -> bool
  val eof: symbol
  val is_eof: symbol -> bool
  val not_eof: symbol -> bool
  val stopper: symbol * (symbol -> bool)
  val sync: symbol
  val is_sync: symbol -> bool
  val not_sync: symbol -> bool
  val malformed: symbol
  val is_ascii: symbol -> bool
  val is_ascii_letter: symbol -> bool
  val is_ascii_digit: symbol -> bool
  val is_ascii_quasi: symbol -> bool
  val is_ascii_blank: symbol -> bool
  datatype kind = Letter | Digit | Quasi | Blank | Other
  val kind: symbol -> kind
  val is_letter: symbol -> bool
  val is_digit: symbol -> bool
  val is_quasi: symbol -> bool
  val is_blank: symbol -> bool
  val is_quasi_letter: symbol -> bool
  val is_letdig: symbol -> bool
  val beginning: int -> symbol list -> string
  val scanner: string -> (string list -> 'a * string list) -> symbol list -> 'a
  val scan_id: string list -> string * string list
  val scan: string list -> symbol * string list
  val source: bool -> (string, 'a) Source.source ->
    (symbol, (string, 'a) Source.source) Source.source
  val explode: string -> symbol list
  val strip_blanks: string -> string
  val bump_init: string -> string
  val bump_string: string -> string
  val length: symbol list -> int
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

(** type symbol **)

(*Symbols, which are considered the smallest entities of any Isabelle
  string, may be of the following form:

    (a) ASCII symbols: a
    (b) printable symbols: \<ident>
    (c) control symbols: \<^ident>
    (d) raw control symbols: \<^raw:...>, where "..." may be any printable
        character excluding ">"

  Output is subject to the print_mode variable (default: verbatim),
  actual interpretation in display is up to front-end tools.

  Symbols (b),(c) and (d) may optionally start with "\\" instead of
  just "\" for compatibility with ML string literals (e.g. used in
  old-style theory files and ML proof scripts).  To be on the safe
  side, the default output of these symbols will also start with the
  double "\\".
*)

type symbol = string;

val space = " ";
fun spaces k = Library.replicate_string k space;

fun is_char s = size s = 1;

fun is_symbolic s =
  String.isPrefix "\\<" s andalso not (String.isPrefix "\\<^" s);

fun is_printable s =
  if is_char s then ord space <= ord s andalso ord s <= ord "~"
  else not (String.isPrefix "\\<^" s);


(* input source control *)

val eof = "";
fun is_eof s = s = eof;
fun not_eof s = s <> eof;
val stopper = (eof, is_eof);

val sync = "\\<^sync>";
fun is_sync s = s = sync;
fun not_sync s = s <> sync;

val malformed = "\\<^malformed>";


(* ascii symbols *)

fun is_ascii s = is_char s andalso ord s < 128;

fun is_ascii_letter s =
  is_char s andalso
   (ord "A" <= ord s andalso ord s <= ord "Z" orelse
    ord "a" <= ord s andalso ord s <= ord "z");

fun is_ascii_digit s =
  is_char s andalso ord "0" <= ord s andalso ord s <= ord "9";

fun is_ascii_quasi "_" = true
  | is_ascii_quasi "'" = true
  | is_ascii_quasi _ = false;

val is_ascii_blank =
  fn " " => true | "\t" => true | "\r" => true | "\n" => true | "\^L" => true
    | _ => false;


(* standard symbol kinds *)

datatype kind = Letter | Digit | Quasi | Blank | Other;

local
  val symbol_kinds = Symtab.make
   [("\\<A>", Letter),
    ("\\<B>", Letter),
    ("\\<C>", Letter),
    ("\\<D>", Letter),
    ("\\<E>", Letter),
    ("\\<F>", Letter),
    ("\\<G>", Letter),
    ("\\<H>", Letter),
    ("\\<I>", Letter),
    ("\\<J>", Letter),
    ("\\<K>", Letter),
    ("\\<L>", Letter),
    ("\\<M>", Letter),
    ("\\<N>", Letter),
    ("\\<O>", Letter),
    ("\\<P>", Letter),
    ("\\<Q>", Letter),
    ("\\<R>", Letter),
    ("\\<S>", Letter),
    ("\\<T>", Letter),
    ("\\<U>", Letter),
    ("\\<V>", Letter),
    ("\\<W>", Letter),
    ("\\<X>", Letter),
    ("\\<Y>", Letter),
    ("\\<Z>", Letter),
    ("\\<a>", Letter),
    ("\\<b>", Letter),
    ("\\<c>", Letter),
    ("\\<d>", Letter),
    ("\\<e>", Letter),
    ("\\<f>", Letter),
    ("\\<g>", Letter),
    ("\\<h>", Letter),
    ("\\<i>", Letter),
    ("\\<j>", Letter),
    ("\\<k>", Letter),
    ("\\<l>", Letter),
    ("\\<m>", Letter),
    ("\\<n>", Letter),
    ("\\<o>", Letter),
    ("\\<p>", Letter),
    ("\\<q>", Letter),
    ("\\<r>", Letter),
    ("\\<s>", Letter),
    ("\\<t>", Letter),
    ("\\<u>", Letter),
    ("\\<v>", Letter),
    ("\\<w>", Letter),
    ("\\<x>", Letter),
    ("\\<y>", Letter),
    ("\\<z>", Letter),
    ("\\<AA>", Letter),
    ("\\<BB>", Letter),
    ("\\<CC>", Letter),
    ("\\<DD>", Letter),
    ("\\<EE>", Letter),
    ("\\<FF>", Letter),
    ("\\<GG>", Letter),
    ("\\<HH>", Letter),
    ("\\<II>", Letter),
    ("\\<JJ>", Letter),
    ("\\<KK>", Letter),
    ("\\<LL>", Letter),
    ("\\<MM>", Letter),
    ("\\<NN>", Letter),
    ("\\<OO>", Letter),
    ("\\<PP>", Letter),
    ("\\<QQ>", Letter),
    ("\\<RR>", Letter),
    ("\\<SS>", Letter),
    ("\\<TT>", Letter),
    ("\\<UU>", Letter),
    ("\\<VV>", Letter),
    ("\\<WW>", Letter),
    ("\\<XX>", Letter),
    ("\\<YY>", Letter),
    ("\\<ZZ>", Letter),
    ("\\<aa>", Letter),
    ("\\<bb>", Letter),
    ("\\<cc>", Letter),
    ("\\<dd>", Letter),
    ("\\<ee>", Letter),
    ("\\<ff>", Letter),
    ("\\<gg>", Letter),
    ("\\<hh>", Letter),
    ("\\<ii>", Letter),
    ("\\<jj>", Letter),
    ("\\<kk>", Letter),
    ("\\<ll>", Letter),
    ("\\<mm>", Letter),
    ("\\<nn>", Letter),
    ("\\<oo>", Letter),
    ("\\<pp>", Letter),
    ("\\<qq>", Letter),
    ("\\<rr>", Letter),
    ("\\<ss>", Letter),
    ("\\<tt>", Letter),
    ("\\<uu>", Letter),
    ("\\<vv>", Letter),
    ("\\<ww>", Letter),
    ("\\<xx>", Letter),
    ("\\<yy>", Letter),
    ("\\<zz>", Letter),
    ("\\<alpha>", Letter),
    ("\\<beta>", Letter),
    ("\\<gamma>", Letter),
    ("\\<delta>", Letter),
    ("\\<epsilon>", Letter),
    ("\\<zeta>", Letter),
    ("\\<eta>", Letter),
    ("\\<theta>", Letter),
    ("\\<iota>", Letter),
    ("\\<kappa>", Letter),
    ("\\<lambda>", Other),      (*sic!*)
    ("\\<mu>", Letter),
    ("\\<nu>", Letter),
    ("\\<xi>", Letter),
    ("\\<pi>", Letter),
    ("\\<rho>", Letter),
    ("\\<sigma>", Letter),
    ("\\<tau>", Letter),
    ("\\<upsilon>", Letter),
    ("\\<phi>", Letter),
    ("\\<psi>", Letter),
    ("\\<omega>", Letter),
    ("\\<Gamma>", Letter),
    ("\\<Delta>", Letter),
    ("\\<Theta>", Letter),
    ("\\<Lambda>", Letter),
    ("\\<Xi>", Letter),
    ("\\<Pi>", Letter),
    ("\\<Sigma>", Letter),
    ("\\<Upsilon>", Letter),
    ("\\<Phi>", Letter),
    ("\\<Psi>", Letter),
    ("\\<Omega>", Letter),
    ("\\<^isub>", Quasi),
    ("\\<^isup>", Quasi),
    ("\\<spacespace>", Blank)];
in
  fun kind s =
    if is_ascii_letter s then Letter
    else if is_ascii_digit s then Digit
    else if is_ascii_quasi s then Quasi
    else if is_ascii_blank s then Blank
    else if is_char s then Other
    else if_none (Symtab.lookup (symbol_kinds, s)) Other;
end;

fun is_letter s = kind s = Letter;
fun is_digit s = kind s = Digit;
fun is_quasi s = kind s = Quasi;
fun is_blank s = kind s = Blank;

fun is_quasi_letter s = let val k = kind s in k = Letter orelse k = Quasi end;
fun is_letdig s = let val k = kind s in k = Letter orelse k = Digit orelse k = Quasi end;



(** symbol input **)

(* scanning through symbols *)

fun beginning n raw_ss =
  let
    val (all_ss, _) = Library.take_suffix is_blank raw_ss;
    val dots = if length all_ss > n then " ..." else "";
    val (ss, _) = Library.take_suffix is_blank (Library.take (n, all_ss));
  in implode (map (fn s => if is_blank s then space else s) ss) ^ dots end;

fun scanner msg scan chs =
  let
    fun err_msg cs = msg ^ ": " ^ beginning 10 cs;
    val fin_scan = Scan.error (Scan.finite stopper (!! (fn (cs, _) => err_msg cs) scan));
  in
    (case fin_scan chs of
      (result, []) => result
    | (_, rest) => error (err_msg rest))
  end;


(* scan *)

val scan_id = Scan.one is_letter ^^ (Scan.any is_letdig >> implode);

local

val scan_encoded_newline =
  $$ "\r" -- $$ "\n" >> K "\n" ||
  $$ "\r" >> K "\n" ||
  Scan.optional ($$ "\\") "" -- Scan.list (explode "\\<^newline>") >> K "\n";

fun raw_body c = ord space <= ord c andalso ord c <= ord "~" andalso c <> ">";
val scan_raw = Scan.list (explode "raw:") -- Scan.any raw_body >> (implode o op @);

in

val scan =
  scan_encoded_newline ||
  ($$ "\\" --| Scan.optional ($$ "\\") "") ^^ $$ "<" ^^
    !! (fn (cs, _) => "Malformed symbolic character specification: \\" ^ "<" ^ beginning 10 cs)
       (($$ "^" ^^ (scan_raw || scan_id) || scan_id) ^^ $$ ">") ||
  Scan.one not_eof;

end;


(* source *)

val recover = Scan.any ((not o is_blank) andf not_eof) >> K [malformed];

fun source do_recover src =
  Source.source stopper (Scan.bulk scan) (if do_recover then Some recover else None) src;


(* explode *)

fun no_explode [] = true
  | no_explode ("\\" :: "<" :: _) = false
  | no_explode ("\r" :: _) = false
  | no_explode (_ :: cs) = no_explode cs;

fun sym_explode str =
  let val chs = explode str in
    if no_explode chs then chs
    else the (Scan.read stopper (Scan.repeat scan) chs)
  end;


(* blanks *)

fun strip_blanks s =
  sym_explode s
  |> Library.take_prefix is_blank |> #2
  |> Library.take_suffix is_blank |> #1
  |> implode;


(* bump string -- treat as base 26 or base 1 numbers *)

fun ends_symbolic (_ :: "\\<^isup>" :: _) = true
  | ends_symbolic (_ :: "\\<^isub>" :: _) = true
  | ends_symbolic (s :: _) = is_symbolic s
  | ends_symbolic [] = false;

fun bump_init str =
  if ends_symbolic (rev (sym_explode str)) then str ^ "'"
  else str ^ "a";

fun bump_string str =
  let
    fun bump [] = ["a"]
      | bump ("z" :: ss) = "a" :: bump ss
      | bump (s :: ss) =
          if is_char s andalso ord "a" <= ord s andalso ord s < ord "z"
          then chr (ord s + 1) :: ss
          else "a" :: s :: ss;

    val (ss, qs) = apfst rev (Library.take_suffix is_quasi (sym_explode str));
    val ss' = if ends_symbolic ss then "'" :: ss else bump ss;
  in implode (rev ss' @ qs) end;



(** symbol output **)

fun sym_len s =
  if not (is_printable s) then 0
  else if String.isPrefix "\\<long" s then 2
  else if String.isPrefix "\\<Long" s then 2
  else if s = "\\<spacespace>" then 2
  else 1;

fun sym_length ss = foldl (fn (n, s) => sym_len s + n) (0, ss);


(* default output *)

fun string_size s = (s, real (size s));

fun sym_escape s = if is_char s then s else "\\" ^ s;

fun default_output s =
  if not (exists_string (equal "\\") s) then string_size s
  else string_size (implode (map sym_escape (sym_explode s)));

fun default_indent (_: string, k) = spaces k;


(* print modes *)

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
