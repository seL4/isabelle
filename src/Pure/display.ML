(*  Title:      Pure/display.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Printing of theorems, goals, results etc.
*)

signature BASIC_DISPLAY =
sig
  val goals_limit: int ref
  val show_hyps: bool ref
  val show_tags: bool ref
  val string_of_thm: thm -> string
  val print_thm: thm -> unit
  val print_thms: thm list -> unit
  val prth: thm -> thm
  val prthq: thm Seq.seq -> thm Seq.seq
  val prths: thm list -> thm list
  val string_of_ctyp: ctyp -> string
  val print_ctyp: ctyp -> unit
  val string_of_cterm: cterm -> string
  val print_cterm: cterm -> unit
  val print_syntax: theory -> unit
  val show_consts: bool ref
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val raw_string_of_sort: sort -> string
  val raw_string_of_typ: typ -> string
  val raw_string_of_term: term -> string
  val pretty_flexpair: Pretty.pp -> term * term -> Pretty.T
  val pretty_thm_aux: Pretty.pp -> bool -> bool -> term list -> thm -> Pretty.T
  val pretty_thm_no_quote: thm -> Pretty.T
  val pretty_thm: thm -> Pretty.T
  val pretty_thms: thm list -> Pretty.T
  val pretty_thm_sg: theory -> thm -> Pretty.T
  val pretty_thms_sg: theory -> thm list -> Pretty.T
  val pprint_thm: thm -> pprint_args -> unit
  val pretty_ctyp: ctyp -> Pretty.T
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val pretty_cterm: cterm -> Pretty.T
  val pprint_cterm: cterm -> pprint_args -> unit
  val pretty_full_theory: theory -> Pretty.T list
  val pretty_goals_aux: Pretty.pp -> string -> bool * bool -> int -> thm -> Pretty.T list
  val pretty_goals: int -> thm -> Pretty.T list
  val print_goals: int -> thm -> unit
  val current_goals_markers: (string * string * string) ref
  val pretty_current_goals: int -> int -> thm -> Pretty.T list
  val print_current_goals_default: int -> int -> thm -> unit
  val print_current_goals_fn: (int -> int -> thm -> unit) ref
end;

structure Display: DISPLAY =
struct

(** raw output **)

val raw_string_of_sort = Sign.string_of_sort ProtoPure.thy;
val raw_string_of_typ = Sign.string_of_typ ProtoPure.thy;
val raw_string_of_term = Sign.string_of_term ProtoPure.thy;



(** print thm **)

val goals_limit = ref 10;       (*max number of goals to print*)
val show_hyps = ref false;      (*false: print meta-hypotheses as dots*)
val show_tags = ref false;      (*false: suppress tags*)

fun pretty_tag (name, args) = Pretty.strs (name :: map Library.quote args);
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_flexpair pp (t, u) = Pretty.block
  [Pretty.term pp t, Pretty.str " =?=", Pretty.brk 1, Pretty.term pp u];

fun pretty_thm_aux pp quote show_hyps' asms raw_th =
  let
    val th = Thm.strip_shyps raw_th;
    val {hyps, tpairs, prop, der = (ora, _), ...} = Thm.rep_thm th;
    val xshyps = Thm.extra_shyps th;
    val (_, tags) = Thm.get_name_tags th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o (Pretty.term pp);

    val hyps' = if ! show_hyps then hyps else subtract (op aconv) asms hyps;
    val ora' = ora andalso (! show_hyps orelse not (! quick_and_dirty));
    val hlen = length xshyps + length hyps' + length tpairs;
    val hsymbs =
      if hlen = 0 andalso not ora' then []
      else if ! show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o pretty_flexpair pp) tpairs @ map prt_term hyps' @
           map (Pretty.sort pp) xshyps @
            (if ora' then [Pretty.str "!"] else []))]
      else [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^
        (if ora' then "!" else "") ^ "]")];
    val tsymbs =
      if null tags orelse not (! show_tags) then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term prop :: (hsymbs @ tsymbs)) end;

fun gen_pretty_thm quote th =
  pretty_thm_aux (Sign.pp (Thm.theory_of_thm th)) quote false [] th;

val pretty_thm = gen_pretty_thm true;
val pretty_thm_no_quote = gen_pretty_thm false;


val string_of_thm = Pretty.string_of o pretty_thm;
val pprint_thm = Pretty.pprint o pretty_thm;

fun pretty_thms [th] = pretty_thm th
  | pretty_thms ths = Pretty.block (Pretty.fbreaks (map pretty_thm ths));

val pretty_thm_sg = pretty_thm oo Thm.transfer;
val pretty_thms_sg = pretty_thms oo (map o Thm.transfer);


(* top-level commands for printing theorems *)

val print_thm = Pretty.writeln o pretty_thm;
val print_thms = Pretty.writeln o pretty_thms;

fun prth th = (print_thm th; th);
fun prthq thq = (Seq.print (K print_thm) 100000 thq; thq);
fun prths ths = (prthq (Seq.of_list ths); ths);


(* other printing commands *)

fun pretty_ctyp cT =
  let val {thy, T, ...} = rep_ctyp cT in Sign.pretty_typ thy T end;

fun pprint_ctyp cT =
  let val {thy, T, ...} = rep_ctyp cT in Sign.pprint_typ thy T end;

fun string_of_ctyp cT =
  let val {thy, T, ...} = rep_ctyp cT in Sign.string_of_typ thy T end;

val print_ctyp = writeln o string_of_ctyp;

fun pretty_cterm ct =
  let val {thy, t, ...} = rep_cterm ct in Sign.pretty_term thy t end;

fun pprint_cterm ct =
  let val {thy, t, ...} = rep_cterm ct in Sign.pprint_term thy t end;

fun string_of_cterm ct =
  let val {thy, t, ...} = rep_cterm ct in Sign.string_of_term thy t end;

val print_cterm = writeln o string_of_cterm;



(** print theory **)

val print_syntax = Syntax.print_syntax o Sign.syn_of;


(* pretty_full_theory *)

fun pretty_full_theory thy =
  let
    fun prt_cls c = Sign.pretty_sort thy [c];
    fun prt_sort S = Sign.pretty_sort thy S;
    fun prt_arity t (c, (_, Ss)) = Sign.pretty_arity thy (t, Ss, [c]);
    fun prt_typ ty = Pretty.quote (Sign.pretty_typ thy ty);
    val prt_typ_no_tvars = prt_typ o Type.freeze_type;
    fun prt_term t = Pretty.quote (Sign.pretty_term thy t);
    val prt_term_no_vars = prt_term o Logic.unvarify;
    fun prt_const (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];
    val prt_const' = Defs.pretty_const (Sign.pp thy);

    fun pretty_classrel (c, []) = prt_cls c
      | pretty_classrel (c, cs) = Pretty.block
          (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
            Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default sort:", Pretty.brk 1, prt_sort S];

    fun pretty_witness NONE = Pretty.str "universal non-emptiness witness: -"
      | pretty_witness (SOME (T, S)) = Pretty.block
          [Pretty.str "universal non-emptiness witness:", Pretty.brk 1,
            prt_typ_no_tvars T, Pretty.str " ::", Pretty.brk 1, prt_sort S];

    val tfrees = map (fn v => TFree (v, []));
    fun pretty_type syn (t, (Type.LogicalType n, _)) =
          if syn then NONE
          else SOME (prt_typ (Type (t, tfrees (Term.invent_names [] "'a" n))))
      | pretty_type syn (t, (Type.Abbreviation (vs, U, syn'), _)) =
          if syn <> syn' then NONE
          else SOME (Pretty.block
            [prt_typ (Type (t, tfrees vs)), Pretty.str " =", Pretty.brk 1, prt_typ U])
      | pretty_type syn (t, (Type.Nonterminal, _)) =
          if not syn then NONE
          else SOME (prt_typ (Type (t, [])));

    val pretty_arities = maps (fn (t, ars) => map (prt_arity t) ars);

    fun pretty_abbrev (c, (ty, t)) = Pretty.block
      (prt_const (c, ty) @ [Pretty.str " ==", Pretty.brk 1, prt_term_no_vars t]);

    fun pretty_axm (a, t) = Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term_no_vars t];

    fun pretty_finals reds = Pretty.block
      (Pretty.str "final:" :: Pretty.brk 1 :: Pretty.commas (map (prt_const' o fst) reds));

    fun pretty_reduct (lhs, rhs) = Pretty.block
      ([prt_const' lhs, Pretty.str "  ->", Pretty.brk 2] @
        Pretty.commas (map prt_const' (sort_wrt #1 rhs)));

    fun pretty_restrict (const, name) =
      Pretty.block ([prt_const' const, Pretty.brk 2, Pretty.str ("(from " ^ quote name ^ ")")]);

    val {axioms, defs, oracles} = Theory.rep_theory thy;
    val {restricts, reducts} = Defs.dest defs;
    val {naming, syn = _, tsig, consts} = Sign.rep_sg thy;
    val {constants, constraints} = Consts.dest consts;
    val extern_const = NameSpace.extern (#1 constants);
    val {classes, default, types, witness, ...} = Type.rep_tsig tsig;
    val (class_space, class_algebra) = classes;
    val {classes, arities} = Sorts.rep_algebra class_algebra;

    val clsses = NameSpace.dest_table (class_space, Symtab.make (Graph.dest classes));
    val tdecls = NameSpace.dest_table types;
    val arties = NameSpace.dest_table (Sign.type_space thy, arities);
    val cnsts = NameSpace.extern_table constants;
    val log_cnsts = map_filter (fn (c, (ty, NONE)) => SOME (c, ty) | _ => NONE) cnsts;
    val abbrevs = map_filter (fn (c, (ty, SOME t)) => SOME (c, (ty, t)) | _ => NONE) cnsts;
    val cnstrs = NameSpace.extern_table constraints;
    val axms = NameSpace.extern_table axioms;
    val oras = NameSpace.extern_table oracles;

    val (reds0, (reds1, reds2)) = reducts |> map (fn (lhs, rhs) =>
        (apfst extern_const lhs, map (apfst extern_const) rhs))
      |> sort_wrt (#1 o #1)
      |> List.partition (null o #2)
      ||> List.partition (Defs.plain_args o #2 o #1);
    val rests = restricts |> map (apfst (apfst extern_const)) |> sort_wrt (#1 o #1);
  in
    [Pretty.strs ("names:" :: Context.names_of thy),
      Pretty.strs ("theory data:" :: Context.theory_data_of thy),
      Pretty.strs ("proof data:" :: Context.proof_data_of thy),
      Pretty.strs ["name prefix:", NameSpace.path_of naming],
      Pretty.big_list "classes:" (map pretty_classrel clsses),
      pretty_default default,
      pretty_witness witness,
      Pretty.big_list "syntactic types:" (map_filter (pretty_type true) tdecls),
      Pretty.big_list "logical types:" (map_filter (pretty_type false) tdecls),
      Pretty.big_list "type arities:" (pretty_arities arties),
      Pretty.big_list "logical consts:" (map (Pretty.block o prt_const) log_cnsts),
      Pretty.big_list "abbreviations:" (map pretty_abbrev abbrevs),
      Pretty.big_list "constraints:" (map (Pretty.block o prt_const) cnstrs),
      Pretty.big_list "axioms:" (map pretty_axm axms),
      Pretty.strs ("oracles:" :: (map #1 oras)),
      Pretty.big_list "definitions:"
        [pretty_finals reds0,
         Pretty.big_list "non-overloaded:" (map pretty_reduct reds1),
         Pretty.big_list "overloaded:" (map pretty_reduct reds2),
         Pretty.big_list "pattern restrictions:" (map pretty_restrict rests)]]
  end;



(** print_goals **)

(* print_goals etc. *)

val show_consts = ref false;  (*true: show consts with types in proof state output*)


(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

local

fun ins_entry (x, y) =
  AList.default (op =) (x, []) #>
  AList.map_entry (op =) x (insert (op =) y);

val add_consts = Term.fold_aterms
  (fn Const (c, T) => ins_entry (T, (c, T))
    | _ => I);

val add_vars = Term.fold_aterms
  (fn Free (x, T) => ins_entry (T, (x, ~1))
    | Var (xi, T) => ins_entry (T, xi)
    | _ => I);

val add_varsT = Term.fold_atyps
  (fn TFree (x, S) => ins_entry (S, (x, ~1))
    | TVar (xi, S) => ins_entry (S, xi)
    | _ => I);

fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
fun sort_cnsts cs = map (apsnd (sort_wrt fst)) cs;

fun consts_of t = sort_cnsts (add_consts t []);
fun vars_of t = sort_idxs (add_vars t []);
fun varsT_of t = rev (sort_idxs (Term.fold_types add_varsT t []));

in

fun pretty_goals_aux pp begin_goal (msg, main) maxgoals state =
  let
    fun prt_atoms prt prtT (X, xs) = Pretty.block
      [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
        Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = Pretty.term pp (Syntax.free x)
      | prt_var xi = Pretty.term pp (Syntax.var xi);

    fun prt_varT (x, ~1) = Pretty.typ pp (TFree (x, []))
      | prt_varT xi = Pretty.typ pp (TVar (xi, []));

    val prt_consts = prt_atoms (Pretty.term pp o Const) (Pretty.typ pp);
    val prt_vars = prt_atoms prt_var (Pretty.typ pp);
    val prt_varsT = prt_atoms prt_varT (Pretty.sort pp);


    fun pretty_list _ _ [] = []
      | pretty_list name prt lst = [Pretty.big_list name (map prt lst)];

    fun pretty_subgoal (n, A) = Pretty.blk (0,
     [Pretty.str (begin_goal ^ " " ^ string_of_int n ^ ". "), Pretty.term pp A]);
    fun pretty_subgoals As = map pretty_subgoal (1 upto length As ~~ As);

    val pretty_ffpairs = pretty_list "flex-flex pairs:" (pretty_flexpair pp);

    val pretty_consts = pretty_list "constants:" prt_consts o consts_of;
    val pretty_vars = pretty_list "variables:" prt_vars o vars_of;
    val pretty_varsT = pretty_list "type variables:" prt_varsT o varsT_of;


    val {prop, tpairs, ...} = Thm.rep_thm state;
    val (As, B) = Logic.strip_horn prop;
    val ngoals = length As;

    fun pretty_gs (types, sorts) =
      (if main then [Pretty.term pp B] else []) @
       (if ngoals = 0 then [Pretty.str "No subgoals!"]
        else if ngoals > maxgoals then
          pretty_subgoals (Library.take (maxgoals, As)) @
          (if msg then [Pretty.str ("A total of " ^ string_of_int ngoals ^ " subgoals...")]
           else [])
        else pretty_subgoals As) @
      pretty_ffpairs tpairs @
      (if ! show_consts then pretty_consts prop else []) @
      (if types then pretty_vars prop else []) @
      (if sorts then pretty_varsT prop else []);
  in
    setmp show_no_free_types true
      (setmp show_types (! show_types orelse ! show_sorts orelse ! show_all_types)
        (setmp show_sorts false pretty_gs))
   (! show_types orelse ! show_sorts orelse ! show_all_types, ! show_sorts)
  end;

fun pretty_goals_marker bg n th =
  pretty_goals_aux (Sign.pp (Thm.theory_of_thm th)) bg (true, true) n th;

val pretty_goals = pretty_goals_marker "";
val print_goals = (Pretty.writeln o Pretty.chunks) oo pretty_goals_marker "";

end;


(* print_current_goals *)

val current_goals_markers = ref ("", "", "");

fun pretty_current_goals n m th =
  let
    val ref (begin_state, end_state, begin_goal) = current_goals_markers;
    val ngoals = nprems_of th;
  in
    (if begin_state = "" then [] else [Pretty.str begin_state]) @
    [Pretty.str ("Level " ^ string_of_int n ^
      (if ngoals > 0 then " (" ^ string_of_int ngoals ^ " subgoal" ^
        (if ngoals <> 1 then "s" else "") ^ ")"
      else ""))] @
    pretty_goals_marker begin_goal m th @
    (if end_state = "" then [] else [Pretty.str end_state])
  end;

fun print_current_goals_default n m th =
  Pretty.writeln (Pretty.chunks (pretty_current_goals n m th));

val print_current_goals_fn = ref print_current_goals_default;

end;

structure BasicDisplay: BASIC_DISPLAY = Display;
open BasicDisplay;
