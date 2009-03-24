(*  Title:      Pure/display.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Printing of theorems, goals, results etc.
*)

signature BASIC_DISPLAY =
sig
  val goals_limit: int ref
  val show_hyps: bool ref
  val show_tags: bool ref
  val show_consts: bool ref
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val pretty_flexpair: Pretty.pp -> term * term -> Pretty.T
  val pretty_thm_aux: Pretty.pp -> bool -> bool -> term list -> thm -> Pretty.T
  val pretty_thm: thm -> Pretty.T
  val string_of_thm: thm -> string
  val pretty_thms: thm list -> Pretty.T
  val pretty_thm_sg: theory -> thm -> Pretty.T
  val pretty_thms_sg: theory -> thm list -> Pretty.T
  val print_thm: thm -> unit
  val print_thms: thm list -> unit
  val prth: thm -> thm
  val prthq: thm Seq.seq -> thm Seq.seq
  val prths: thm list -> thm list
  val pretty_ctyp: ctyp -> Pretty.T
  val string_of_ctyp: ctyp -> string
  val print_ctyp: ctyp -> unit
  val pretty_cterm: cterm -> Pretty.T
  val string_of_cterm: cterm -> string
  val print_cterm: cterm -> unit
  val print_syntax: theory -> unit
  val pretty_full_theory: bool -> theory -> Pretty.T list
  val pretty_goals_aux: Pretty.pp -> Markup.T -> bool * bool -> int -> thm -> Pretty.T list
  val pretty_goals: int -> thm -> Pretty.T list
  val print_goals: int -> thm -> unit
end;

structure Display: DISPLAY =
struct


(** print thm **)

val goals_limit = ref 10;       (*max number of goals to print*)
val show_hyps = ref false;      (*false: print meta-hypotheses as dots*)
val show_tags = ref false;      (*false: suppress tags*)

fun pretty_tag (name, arg) = Pretty.strs [name, quote arg];
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_flexpair pp (t, u) = Pretty.block
  [Pretty.term pp t, Pretty.str " =?=", Pretty.brk 1, Pretty.term pp u];

fun display_status th =
  let
    val {oracle = oracle0, unfinished, failed} = Thm.status_of th;
    val oracle = oracle0 andalso (not (! quick_and_dirty) orelse ! show_hyps);
  in
    if failed then "!!"
    else if oracle andalso unfinished then "!?"
    else if oracle then "!"
    else if unfinished then "?"
    else ""
  end;

fun pretty_thm_aux pp quote show_hyps' asms raw_th =
  let
    val th = Thm.strip_shyps raw_th;
    val {hyps, tpairs, prop, ...} = Thm.rep_thm th;
    val xshyps = Thm.extra_shyps th;
    val tags = Thm.get_tags th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o Pretty.term pp;

    val hyps' = if ! show_hyps then hyps else subtract (op aconv) asms hyps;
    val status = display_status th;

    val hlen = length xshyps + length hyps' + length tpairs;
    val hsymbs =
      if hlen = 0 andalso status = "" then []
      else if ! show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o pretty_flexpair pp) tpairs @ map prt_term hyps' @
           map (Pretty.sort pp) xshyps @
            (if status = "" then [] else [Pretty.str status]))]
      else [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^ status ^ "]")];
    val tsymbs =
      if null tags orelse not (! show_tags) then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term prop :: (hsymbs @ tsymbs)) end;

fun pretty_thm th =
  pretty_thm_aux (Syntax.pp_global (Thm.theory_of_thm th)) true false [] th;

val string_of_thm = Pretty.string_of o pretty_thm;

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

fun pretty_ctyp cT = Syntax.pretty_typ_global (Thm.theory_of_ctyp cT) (Thm.typ_of cT);
fun string_of_ctyp cT = Syntax.string_of_typ_global (Thm.theory_of_ctyp cT) (Thm.typ_of cT);
val print_ctyp = writeln o string_of_ctyp;

fun pretty_cterm ct = Syntax.pretty_term_global (Thm.theory_of_cterm ct) (Thm.term_of ct);
fun string_of_cterm ct = Syntax.string_of_term_global (Thm.theory_of_cterm ct) (Thm.term_of ct);
val print_cterm = writeln o string_of_cterm;



(** print theory **)

val print_syntax = Syntax.print_syntax o Sign.syn_of;


(* pretty_full_theory *)

fun pretty_full_theory verbose thy =
  let
    val ctxt = ProofContext.init thy;

    fun prt_cls c = Syntax.pretty_sort ctxt [c];
    fun prt_sort S = Syntax.pretty_sort ctxt S;
    fun prt_arity t (c, (_, Ss)) = Syntax.pretty_arity ctxt (t, Ss, [c]);
    fun prt_typ ty = Pretty.quote (Syntax.pretty_typ ctxt ty);
    val prt_typ_no_tvars = prt_typ o Logic.unvarifyT;
    fun prt_term t = Pretty.quote (Syntax.pretty_term ctxt t);
    val prt_term_no_vars = prt_term o Logic.unvarify;
    fun prt_const (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];
    val prt_const' = Defs.pretty_const (Syntax.pp ctxt);

    fun pretty_classrel (c, []) = prt_cls c
      | pretty_classrel (c, cs) = Pretty.block
          (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
            Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default sort:", Pretty.brk 1, prt_sort S];

    val tfrees = map (fn v => TFree (v, []));
    fun pretty_type syn (t, ((Type.LogicalType n, _), _)) =
          if syn then NONE
          else SOME (prt_typ (Type (t, tfrees (Name.invents Name.context Name.aT n))))
      | pretty_type syn (t, ((Type.Abbreviation (vs, U, syn'), _), _)) =
          if syn <> syn' then NONE
          else SOME (Pretty.block
            [prt_typ (Type (t, tfrees vs)), Pretty.str " =", Pretty.brk 1, prt_typ U])
      | pretty_type syn (t, ((Type.Nonterminal, _), _)) =
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

    val axioms = (Theory.axiom_space thy, Theory.axiom_table thy);
    val defs = Theory.defs_of thy;
    val {restricts, reducts} = Defs.dest defs;
    val {naming, syn = _, tsig, consts} = Sign.rep_sg thy;
    val {constants, constraints} = Consts.dest consts;
    val extern_const = NameSpace.extern (#1 constants);
    val {classes, default, types, ...} = Type.rep_tsig tsig;
    val (class_space, class_algebra) = classes;
    val {classes, arities} = Sorts.rep_algebra class_algebra;

    val clsses = NameSpace.dest_table (class_space, Symtab.make (Graph.dest classes));
    val tdecls = NameSpace.dest_table types;
    val arties = NameSpace.dest_table (Sign.type_space thy, arities);

    fun prune_const c = not verbose andalso
      member (op =) (Consts.the_tags consts c) Markup.property_internal;
    val cnsts = NameSpace.extern_table (#1 constants,
      Symtab.make (filter_out (prune_const o fst) (Symtab.dest (#2 constants))));

    val log_cnsts = map_filter (fn (c, (ty, NONE)) => SOME (c, ty) | _ => NONE) cnsts;
    val abbrevs = map_filter (fn (c, (ty, SOME t)) => SOME (c, (ty, t)) | _ => NONE) cnsts;
    val cnstrs = NameSpace.extern_table constraints;

    val axms = NameSpace.extern_table axioms;

    val (reds0, (reds1, reds2)) = filter_out (prune_const o fst o fst) reducts
      |> map (fn (lhs, rhs) =>
        (apfst extern_const lhs, map (apfst extern_const) (filter_out (prune_const o fst) rhs)))
      |> sort_wrt (#1 o #1)
      |> List.partition (null o #2)
      ||> List.partition (Defs.plain_args o #2 o #1);
    val rests = restricts |> map (apfst (apfst extern_const)) |> sort_wrt (#1 o #1);
  in
    [Pretty.strs ("names:" :: Context.display_names thy)] @
    [Pretty.big_list "classes:" (map pretty_classrel clsses),
      pretty_default default,
      Pretty.big_list "syntactic types:" (map_filter (pretty_type true) tdecls),
      Pretty.big_list "logical types:" (map_filter (pretty_type false) tdecls),
      Pretty.big_list "type arities:" (pretty_arities arties),
      Pretty.big_list "logical consts:" (map (Pretty.block o prt_const) log_cnsts),
      Pretty.big_list "abbreviations:" (map pretty_abbrev abbrevs),
      Pretty.big_list "constraints:" (map (Pretty.block o prt_const) cnstrs),
      Pretty.big_list "axioms:" (map pretty_axm axms),
      Pretty.strs ("oracles:" :: Thm.extern_oracles thy),
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

fun pretty_goals_aux pp markup (msg, main) maxgoals state =
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

    fun pretty_subgoal (n, A) = Pretty.markup markup
      [Pretty.str (" " ^ string_of_int n ^ ". "), Pretty.term pp A];
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

fun pretty_goals n th =
  pretty_goals_aux (Syntax.pp_global (Thm.theory_of_thm th)) Markup.none (true, true) n th;

val print_goals = (Pretty.writeln o Pretty.chunks) oo pretty_goals;

end;


end;

structure BasicDisplay: BASIC_DISPLAY = Display;
open BasicDisplay;
