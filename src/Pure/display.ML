(*  Title:      Pure/display.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Printing of theories, theorems, etc.
*)

signature DISPLAY =
sig
  val show_hyps		: bool ref
  val show_tags		: bool ref
  val pretty_thm_no_quote: thm -> Pretty.T
  val pretty_thm	: thm -> Pretty.T
  val pretty_thms	: thm list -> Pretty.T
  val pretty_thm_sg     : Sign.sg -> thm -> Pretty.T
  val pretty_thms_sg    : Sign.sg -> thm list -> Pretty.T
  val string_of_thm	: thm -> string
  val pprint_thm	: thm -> pprint_args -> unit
  val print_thm		: thm -> unit
  val print_thms	: thm list -> unit
  val prth		: thm -> thm
  val prthq		: thm Seq.seq -> thm Seq.seq
  val prths		: thm list -> thm list
  val pretty_ctyp	: ctyp -> Pretty.T
  val pprint_ctyp	: ctyp -> pprint_args -> unit
  val string_of_ctyp	: ctyp -> string
  val print_ctyp	: ctyp -> unit
  val pretty_cterm	: cterm -> Pretty.T
  val pprint_cterm	: cterm -> pprint_args -> unit
  val string_of_cterm	: cterm -> string
  val print_cterm	: cterm -> unit
  val pretty_theory	: theory -> Pretty.T
  val pprint_theory	: theory -> pprint_args -> unit
  val print_syntax	: theory -> unit
  val pretty_full_theory: theory -> Pretty.T list
  val pretty_name_space : string * NameSpace.T -> Pretty.T
  val show_consts	: bool ref
end;

structure Display: DISPLAY =
struct

(** print thm **)

val show_hyps = ref true;	(*false: print meta-hypotheses as dots*)
val show_tags = ref false;	(*false: suppress tags*)

local

fun pretty_tag (name, args) = Pretty.strs (name :: map quote args);
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_thm_aux quote th =
  let
    val {sign, hyps, prop, der = (ora, _), ...} = rep_thm th;
    val xshyps = Thm.extra_shyps th;
    val (_, tags) = Thm.get_name_tags th;

    val prt_term = (if quote then Pretty.quote else I) o Sign.pretty_term sign;

    val hlen = length xshyps + length hyps;
    val hsymbs =
      if hlen = 0 andalso not ora then []
      else if ! show_hyps then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map prt_term hyps @ map (Sign.pretty_sort sign) xshyps @
            (if ora then [Pretty.str "!"] else []))]
      else [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^
        (if ora then "!" else "") ^ "]")];
    val tsymbs =
      if null tags orelse not (! show_tags) then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term prop :: (hsymbs @ tsymbs)) end;

in

val pretty_thm = pretty_thm_aux true;
val pretty_thm_no_quote = pretty_thm_aux false;

end;


val string_of_thm = Pretty.string_of o pretty_thm;
val pprint_thm = Pretty.pprint o pretty_thm;

fun pretty_thms [th] = pretty_thm th
  | pretty_thms ths = Pretty.block (Pretty.fbreaks (map pretty_thm ths));

val pretty_thm_sg = pretty_thm oo Thm.transfer_sg;
val pretty_thms_sg = pretty_thms oo (map o Thm.transfer_sg);


(* top-level commands for printing theorems *)

val print_thm = Pretty.writeln o pretty_thm;
val print_thms = Pretty.writeln o pretty_thms;

fun prth th = (print_thm th; th);

(*Print and return a sequence of theorems, separated by blank lines. *)
fun prthq thseq =
  (Seq.print (fn _ => print_thm) 100000 thseq; thseq);

(*Print and return a list of theorems, separated by blank lines. *)
fun prths ths = (seq (fn th => (print_thm th; writeln "")) ths; ths);


(* other printing commands *)

fun pretty_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pretty_typ sign T end;

fun pprint_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pprint_typ sign T end;

fun string_of_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.string_of_typ sign T end;

val print_ctyp = writeln o string_of_ctyp;

fun pretty_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pretty_term sign t end;

fun pprint_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pprint_term sign t end;

fun string_of_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.string_of_term sign t end;

val print_cterm = writeln o string_of_cterm;



(** print theory **)

val pretty_theory = Sign.pretty_sg o Theory.sign_of;
val pprint_theory = Sign.pprint_sg o Theory.sign_of;

val print_syntax = Syntax.print_syntax o Theory.syn_of;


(* pretty_name_space  *)

fun pretty_name_space (kind, space) =
  let
    fun prt_entry (name, accs) = Pretty.block
      (Pretty.str (quote name ^ " =") :: Pretty.brk 1 ::
        Pretty.commas (map (Pretty.str o quote) accs));
  in
    Pretty.fbreaks (Pretty.str (kind ^ ":") :: map prt_entry (NameSpace.dest space))
    |> Pretty.block
  end;



(* print theory *)

fun pretty_full_theory thy =
  let
    val sg = Theory.sign_of thy;

    fun prt_cls c = Sign.pretty_sort sg [c];
    fun prt_sort S = Sign.pretty_sort sg S;
    fun prt_arity t (c, Ss) = Sign.pretty_arity sg (t, Ss, [c]);
    fun prt_typ_no_tvars ty = Pretty.quote (Sign.pretty_typ sg (#1 (Type.freeze_thaw_type ty)));
    fun prt_term t = Pretty.quote (Sign.pretty_term sg t);

    fun pretty_classes cs = Pretty.block
      (Pretty.breaks (Pretty.str "classes:" :: map prt_cls cs));

    fun pretty_classrel (c, cs) = Pretty.block
      (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
        Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, prt_sort S];

    fun pretty_ty (t, n) = Pretty.block
      [Pretty.str t, Pretty.brk 1, Pretty.str (string_of_int n)];

    fun pretty_log_types ts = Pretty.block
      (Pretty.breaks (Pretty.str "logical types:" :: map Pretty.str ts));

    fun pretty_witness None = Pretty.str "universal non-emptiness witness: --"
      | pretty_witness (Some (T, S)) = Pretty.block
          [Pretty.str "universal non-emptiness witness:", Pretty.brk 1, prt_typ_no_tvars T,
            Pretty.brk 1, prt_sort S];

    fun pretty_abbr (t, (vs, rhs)) = Pretty.block
      [prt_typ_no_tvars (Type (t, map (fn v => TVar ((v, 0), [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ_no_tvars rhs];

    fun pretty_arities (t, ars) = map (prt_arity t) ars;

    fun pretty_const (c, ty) = Pretty.block
      [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];

    fun prt_axm (a, t) = Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term t];


    val {self = _, tsig, const_tab, syn = _, path, spaces, data} = Sign.rep_sg sg;
    val {axioms, oracles, ...} = Theory.rep_theory thy;
    val spaces' = Library.sort_wrt fst spaces;
    val {classes, classrel, default, tycons = type_tab, log_types, univ_witness, abbrs, arities} =
      Type.rep_tsig tsig;
    val tycons = Sign.cond_extern_table sg Sign.typeK type_tab;
    val consts = Sign.cond_extern_table sg Sign.constK const_tab;
    val axms = Sign.cond_extern_table sg Theory.axiomK axioms;
    val oras = Sign.cond_extern_table sg Theory.oracleK oracles;
  in
    [Pretty.strs ("stamps:" :: Sign.stamp_names_of sg),
      Pretty.strs ("data:" :: Sign.data_kinds data),
      Pretty.strs ["name prefix:", NameSpace.pack path],
      Pretty.big_list "name spaces:" (map pretty_name_space spaces'),
      pretty_classes classes,
      Pretty.big_list "class relation:" (map pretty_classrel (Symtab.dest classrel)),
      pretty_default default,
      pretty_log_types log_types,
      pretty_witness univ_witness,
      Pretty.big_list "type constructors:" (map pretty_ty tycons),
      Pretty.big_list "type abbreviations:" (map pretty_abbr (Symtab.dest abbrs)),
      Pretty.big_list "type arities:" (flat (map pretty_arities (Symtab.dest arities))),
      Pretty.big_list "consts:" (map pretty_const consts),
      Pretty.big_list "axioms:" (map prt_axm axms),
      Pretty.strs ("oracles:" :: (map #1 oras))]
  end;


(*show consts with types in proof state output?*)
val show_consts = ref false;


end;

open Display;
