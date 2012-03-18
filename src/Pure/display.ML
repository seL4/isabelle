(*  Title:      Pure/display.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Printing of theorems, results etc.
*)

signature BASIC_DISPLAY =
sig
  val show_consts_default: bool Unsynchronized.ref
  val show_consts: bool Config.T
  val show_hyps_raw: Config.raw
  val show_hyps: bool Config.T
  val show_tags_raw: Config.raw
  val show_tags: bool Config.T
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val pretty_thm_raw: Proof.context -> {quote: bool, show_hyps: bool, show_status: bool} ->
    thm -> Pretty.T
  val pretty_thm_aux: Proof.context -> bool -> thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thm_global: theory -> thm -> Pretty.T
  val pretty_thm_without_context: thm -> Pretty.T
  val string_of_thm: Proof.context -> thm -> string
  val string_of_thm_global: theory -> thm -> string
  val string_of_thm_without_context: thm -> string
  val pretty_thms_aux: Proof.context -> bool -> thm list -> Pretty.T
  val pretty_thms: Proof.context -> thm list -> Pretty.T
  val print_syntax: theory -> unit
  val pretty_full_theory: bool -> theory -> Pretty.T list
end;

structure Display: DISPLAY =
struct

(** options **)

val show_consts_default = Goal_Display.show_consts_default;
val show_consts = Goal_Display.show_consts;

val show_hyps_raw = Config.declare "show_hyps" (fn _ => Config.Bool false);
val show_hyps = Config.bool show_hyps_raw;

val show_tags_raw = Config.declare "show_tags" (fn _ => Config.Bool false);
val show_tags = Config.bool show_tags_raw;



(** print thm **)

fun pretty_tag (name, arg) = Pretty.strs [name, quote arg];
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun display_status _ false _ = ""
  | display_status show_hyps true th =
      let
        val {oracle = oracle0, unfinished, failed} = Thm.status_of th;
        val oracle = oracle0 andalso (not (! quick_and_dirty) orelse show_hyps);
      in
        if failed then "!!"
        else if oracle andalso unfinished then "!?"
        else if oracle then "!"
        else if unfinished then "?"
        else ""
      end;

fun pretty_thm_raw ctxt {quote, show_hyps = show_hyps', show_status} raw_th =
  let
    val show_tags = Config.get ctxt show_tags;
    val show_hyps = Config.get ctxt show_hyps;

    val th = Thm.strip_shyps raw_th;
    val {hyps, tpairs, prop, ...} = Thm.rep_thm th;
    val xshyps = Thm.extra_shyps th;
    val tags = Thm.get_tags th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o Syntax.pretty_term ctxt;

    val asms = map Thm.term_of (Assumption.all_assms_of ctxt);
    val hyps' = if show_hyps then hyps else subtract (op aconv) asms hyps;
    val status = display_status show_hyps show_status th;

    val hlen = length xshyps + length hyps' + length tpairs;
    val hsymbs =
      if hlen = 0 andalso status = "" then []
      else if show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o Goal_Display.pretty_flexpair ctxt) tpairs @ map prt_term hyps' @
           map (Syntax.pretty_sort ctxt) xshyps @
            (if status = "" then [] else [Pretty.str status]))]
      else [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^ status ^ "]")];
    val tsymbs =
      if null tags orelse not show_tags then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term prop :: (hsymbs @ tsymbs)) end;

fun pretty_thm_aux ctxt show_status =
  pretty_thm_raw ctxt {quote = false, show_hyps = true, show_status = show_status};

fun pretty_thm ctxt = pretty_thm_aux ctxt true;

fun pretty_thm_global thy =
  pretty_thm_raw (Syntax.init_pretty_global thy)
    {quote = false, show_hyps = false, show_status = true};

fun pretty_thm_without_context th = pretty_thm_global (Thm.theory_of_thm th) th;

val string_of_thm = Pretty.string_of oo pretty_thm;
val string_of_thm_global = Pretty.string_of oo pretty_thm_global;
val string_of_thm_without_context = Pretty.string_of o pretty_thm_without_context;


(* multiple theorems *)

fun pretty_thms_aux ctxt flag [th] = pretty_thm_aux ctxt flag th
  | pretty_thms_aux ctxt flag ths =
      Pretty.blk (0, Pretty.fbreaks (map (pretty_thm_aux ctxt flag) ths));

fun pretty_thms ctxt = pretty_thms_aux ctxt true;



(** print theory **)

val print_syntax = Syntax.print_syntax o Sign.syn_of;


(* pretty_full_theory *)

fun pretty_full_theory verbose thy =
  let
    val ctxt = Syntax.init_pretty_global thy;

    fun prt_cls c = Syntax.pretty_sort ctxt [c];
    fun prt_sort S = Syntax.pretty_sort ctxt S;
    fun prt_arity t (c, Ss) = Syntax.pretty_arity ctxt (t, Ss, [c]);
    fun prt_typ ty = Pretty.quote (Syntax.pretty_typ ctxt ty);
    val prt_typ_no_tvars = prt_typ o Logic.unvarifyT_global;
    fun prt_term t = Pretty.quote (Syntax.pretty_term ctxt t);
    val prt_term_no_vars = prt_term o Logic.unvarify_global;
    fun prt_const (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];
    val prt_const' = Defs.pretty_const ctxt;

    fun pretty_classrel (c, []) = prt_cls c
      | pretty_classrel (c, cs) = Pretty.block
          (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
            Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default sort:", Pretty.brk 1, prt_sort S];

    val tfrees = map (fn v => TFree (v, []));
    fun pretty_type syn (t, (Type.LogicalType n)) =
          if syn then NONE
          else SOME (prt_typ (Type (t, tfrees (Name.invent Name.context Name.aT n))))
      | pretty_type syn (t, (Type.Abbreviation (vs, U, syn'))) =
          if syn <> syn' then NONE
          else SOME (Pretty.block
            [prt_typ (Type (t, tfrees vs)), Pretty.str " =", Pretty.brk 1, prt_typ U])
      | pretty_type syn (t, Type.Nonterminal) =
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
    val tsig = Sign.tsig_of thy;
    val consts = Sign.consts_of thy;
    val {constants, constraints} = Consts.dest consts;
    val extern_const = Name_Space.extern ctxt (#1 constants);
    val {classes, default, types, ...} = Type.rep_tsig tsig;
    val (class_space, class_algebra) = classes;
    val classes = Sorts.classes_of class_algebra;
    val arities = Sorts.arities_of class_algebra;

    val clsses = Name_Space.dest_table ctxt (class_space, Symtab.make (Graph.dest classes));
    val tdecls = Name_Space.dest_table ctxt types;
    val arties = Name_Space.dest_table ctxt (Type.type_space tsig, arities);

    fun prune_const c = not verbose andalso Consts.is_concealed consts c;
    val cnsts = Name_Space.extern_table ctxt (#1 constants,
      Symtab.make (filter_out (prune_const o fst) (Symtab.dest (#2 constants))));

    val log_cnsts = map_filter (fn (c, (ty, NONE)) => SOME (c, ty) | _ => NONE) cnsts;
    val abbrevs = map_filter (fn (c, (ty, SOME t)) => SOME (c, (ty, t)) | _ => NONE) cnsts;
    val cnstrs = Name_Space.extern_table ctxt constraints;

    val axms = Name_Space.extern_table ctxt axioms;

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
      Pretty.strs ("oracles:" :: Thm.extern_oracles ctxt),
      Pretty.big_list "definitions:"
        [pretty_finals reds0,
         Pretty.big_list "non-overloaded:" (map pretty_reduct reds1),
         Pretty.big_list "overloaded:" (map pretty_reduct reds2),
         Pretty.big_list "pattern restrictions:" (map pretty_restrict rests)]]
  end;

end;

structure Basic_Display: BASIC_DISPLAY = Display;
open Basic_Display;
