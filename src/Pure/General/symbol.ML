(*  Title:      Pure/General/symbol.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generalized characters, independent of encoding.
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
  val is_quasi_letter: symbol -> bool
  val is_letdig: symbol -> bool
  val is_blank: symbol -> bool
  val is_symbolic: symbol -> bool
  val is_printable: symbol -> bool
  val length: symbol list -> int
  val beginning: symbol list -> string
  val scan: string list -> symbol * string list
  val scanner: string -> (symbol list -> 'a * symbol list) -> symbol list -> 'a
  val source: bool -> (string, 'a) Source.source ->
    (symbol, (string, 'a) Source.source) Source.source
  val explode: string -> symbol list
  val input: string -> string
  val default_indent: string * int -> string
  val add_mode: string -> (string -> string * real) * (string * int -> string) -> unit
  val isabelle_fontN: string
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

  input may include non-ASCII characters according to isabelle-0 encoding;
  output is subject to the print_mode variable (default: verbatim);
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

fun is_letter s =
  size s = 1 andalso
   (ord "A" <= ord s andalso ord s <= ord "Z" orelse
    ord "a" <= ord s andalso ord s <= ord "z");

fun is_digit s =
  size s = 1 andalso ord "0" <= ord s andalso ord s <= ord "9";

fun is_quasi_letter "_" = true
  | is_quasi_letter "'" = true
  | is_quasi_letter s = is_letter s;

val is_blank =
  fn " " => true | "\t" => true | "\n" => true | "\^L" => true
    | "\160" => true | "\\<spacespace>" => true
    | _ => false;

val is_letdig = is_quasi_letter orf is_digit;

fun is_symbolic s =
  size s > 2 andalso nth_elem_string (2, s) <> "^";

fun is_printable s =
  size s = 1 andalso ord space <= ord s andalso ord s <= ord "~" orelse
  is_symbolic s;


fun sym_length ss = foldl (fn (n, s) =>
  (if not (is_printable s) then 0 else
    (case Library.try String.substring (s, 2, 4) of
      Some s' => if s' = "long" orelse s' = "Long" then 2 else 1
    | None => 1)) + n) (0, ss);


(* beginning *)

val smash_blanks = map (fn s => if is_blank s then space else s);

fun beginning raw_ss =
  let
    val (all_ss, _) = take_suffix is_blank raw_ss;
    val dots = if length all_ss > 10 then " ..." else "";
    val (ss, _) = take_suffix is_blank (take (10, all_ss));
  in implode (smash_blanks ss) ^ dots end;



(** isabelle-0 encoding table **)

val enc_start = 160;
val enc_end = 255;

val enc_vector =
[
(* GENERATED TEXT FOLLOWS - Do not edit! *)
  "\\<spacespace>",
  "\\<Gamma>",
  "\\<Delta>",
  "\\<Theta>",
  "\\<Lambda>",
  "\\<Pi>",
  "\\<Sigma>",
  "\\<Phi>",
  "\\<Psi>",
  "\\<Omega>",
  "\\<alpha>",
  "\\<beta>",
  "\\<gamma>",
  "\\<delta>",
  "\\<epsilon>",
  "\\<zeta>",
  "\\<eta>",
  "\\<theta>",
  "\\<kappa>",
  "\\<lambda>",
  "\\<mu>",
  "\\<nu>",
  "\\<xi>",
  "\\<pi>",
  "\\<rho>",
  "\\<sigma>",
  "\\<tau>",
  "\\<phi>",
  "\\<chi>",
  "\\<psi>",
  "\\<omega>",
  "\\<not>",
  "\\<and>",
  "\\<or>",
  "\\<forall>",
  "\\<exists>",
  "\\<And>",
  "\\<lceil>",
  "\\<rceil>",
  "\\<lfloor>",
  "\\<rfloor>",
  "\\<turnstile>",
  "\\<Turnstile>",
  "\\<lbrakk>",
  "\\<rbrakk>",
  "\\<cdot>",
  "\\<in>",
  "\\<subseteq>",
  "\\<inter>",
  "\\<union>",
  "\\<Inter>",
  "\\<Union>",
  "\\<sqinter>",
  "\\<squnion>",
  "\\<Sqinter>",
  "\\<Squnion>",
  "\\<bottom>",
  "\\<doteq>",
  "\\<equiv>",
  "\\<noteq>",
  "\\<sqsubset>",
  "\\<sqsubseteq>",
  "\\<prec>",
  "\\<preceq>",
  "\\<succ>",
  "\\<approx>",
  "\\<sim>",
  "\\<simeq>",
  "\\<le>",
  "\\<Colon>",
  "\\<leftarrow>",
  "\\<midarrow>",
  "\\<rightarrow>",
  "\\<Leftarrow>",
  "\\<Midarrow>",
  "\\<Rightarrow>",
  "\\<frown>",
  "\\<mapsto>",
  "\\<leadsto>",
  "\\<up>",
  "\\<down>",
  "\\<notin>",
  "\\<times>",
  "\\<oplus>",
  "\\<ominus>",
  "\\<otimes>",
  "\\<oslash>",
  "\\<subset>",
  "\\<infinity>",
  "\\<box>",
  "\\<diamond>",
  "\\<circ>",
  "\\<bullet>",
  "\\<parallel>",
  "\\<surd>",
  "\\<copyright>"
(* END OF GENERATED TEXT *)
];

val enc_rel = enc_vector ~~ map chr (enc_start upto enc_end);

val char_tab = Symtab.make enc_rel;
val symbol_tab = Symtab.make (map swap enc_rel);

fun lookup_symbol c =
  if ord c < enc_start then None
  else Symtab.lookup (symbol_tab, c);


(* encode / decode *)

fun char s = if_none (Symtab.lookup (char_tab, s)) s;
fun symbol c = if_none (lookup_symbol c) c;

fun symbol' c =
  (case lookup_symbol c of
    None => c
  | Some s => "\\" ^ s);



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
  | no_syms (c :: cs) = ord c < enc_start andalso no_syms cs;

fun sym_explode str =
  let val chs = explode str in
    if no_syms chs then chs     (*tune trivial case*)
    else map symbol (the (Scan.read stopper (Scan.repeat scan) chs))
  end;


(* input *)

fun input str =
  let val chs = explode str in
    if forall (fn c => ord c < enc_start) chs then str
    else implode (map symbol' chs)
  end;



(** symbol output **)

(* default *)

fun string_size s = (s, real (size s));

fun default_output s =
  if not (exists_string (equal "\\") s) then string_size s
  else string_size (implode (map (fn "\\" => "\\\\" | c => c) (explode s)));    (*sic!*)

fun default_indent (_: string, k) = spaces k;


(* isabelle_font *)

fun isabelle_font_output s =
  let val cs = sym_explode s
  in (implode (map char cs), real (sym_length cs)) end;

val isabelle_font_indent = default_indent;


(* maintain modes *)

val isabelle_fontN = "isabelle_font";
val symbolsN = "symbols";
val xsymbolsN = "xsymbols";

val modes = ref (Symtab.make [(isabelle_fontN, (isabelle_font_output, isabelle_font_indent))]);

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
