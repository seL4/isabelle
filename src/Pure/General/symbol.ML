(*  Title:      Pure/General/symbol.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generalized characters.
*)

signature SYMBOL =
sig
  type symbol
  val space: symbol
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
  val is_printable: symbol -> bool
  val beginning: symbol list -> string
  val scan: string list -> symbol * string list
  val explode: string -> symbol list
  val length: symbol list -> int
  val size: string -> int
  val input: string -> string
  val output: string -> string
  val source: bool -> (string, 'a) Source.source ->
    (symbol, (string, 'a) Source.source) Source.source
end;

structure Symbol: SYMBOL =
struct


(** encoding table (isabelle-0) **)

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
  "\\<bow>",
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



(** type symbol **)

type symbol = string;

val space = " ";
val eof = "";


(* kinds *)

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

fun is_printable s =
  size s = 1 andalso ord space <= ord s andalso ord s <= ord "~" orelse
  size s > 2 andalso nth_elem (2, explode s) <> "^";


(* beginning *)

val smash_blanks = map (fn s => if is_blank s then space else s);

fun beginning raw_ss =
  let
    val (all_ss, _) = take_suffix is_blank raw_ss;
    val dots = if length all_ss > 10 then " ..." else "";
    val (ss, _) = take_suffix is_blank (take (10, all_ss));
  in implode (smash_blanks ss) ^ dots end;


(* scan *)

val scan_id = Scan.one is_letter ^^ (Scan.any is_letdig >> implode);

val scan =
  ($$ "\\" --| Scan.optional ($$ "\\") "") ^^ $$ "<" ^^
    !! (fn (cs, _) => "Malformed symbolic character specification: \\" ^ "<" ^ beginning cs)
      (Scan.optional ($$ "^") "" ^^ scan_id ^^ $$ ">") ||
  Scan.one not_eof;


(* source *)

val recover = Scan.any1 ((not o is_blank) andf not_eof);

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


(* printable length *)

fun sym_length ss = foldl (fn (n, c) => if is_printable c then n + 1 else n) (0, ss);
val sym_size = sym_length o sym_explode;


(* input / output *)

fun input str =
  let val chs = explode str in
    if forall (fn c => ord c < enc_start) chs then str
    else implode (map symbol' chs)
  end;

fun char' s = if size s > 1 then "\\" ^ s else s;
fun output s = let val chr = (* if "isabelle_font" mem_string !print_mode *)
(* FIXME: does not work yet, because of static calls to output in printer.ML *)
			     (* then *) char (* else char'*)
		in (implode o map chr o sym_explode) s end;


(*final declarations of this structure!*)
val explode = sym_explode;
val length = sym_length;
val size = sym_size;


end;
