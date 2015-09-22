(*  Title:      Pure/display.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Printing of theorems, results etc.
*)

signature BASIC_DISPLAY =
sig
  val show_consts: bool Config.T
  val show_hyps_raw: Config.raw
  val show_hyps: bool Config.T
  val show_tags_raw: Config.raw
  val show_tags: bool Config.T
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val pretty_thm_raw: Proof.context -> {quote: bool, show_hyps: bool} -> thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thm_item: Proof.context -> thm -> Pretty.T
  val pretty_thm_global: theory -> thm -> Pretty.T
  val string_of_thm: Proof.context -> thm -> string
  val string_of_thm_global: theory -> thm -> string
  val pretty_full_theory: bool -> theory -> Pretty.T list
end;

structure Display: DISPLAY =
struct

(** options **)

val show_consts = Goal_Display.show_consts;

val show_hyps_raw = Config.declare ("show_hyps", @{here}) (fn _ => Config.Bool false);
val show_hyps = Config.bool show_hyps_raw;

val show_tags_raw = Config.declare ("show_tags", @{here}) (fn _ => Config.Bool false);
val show_tags = Config.bool show_tags_raw;



(** print thm **)

fun pretty_tag (name, arg) = Pretty.strs [name, quote arg];
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_thm_raw ctxt {quote, show_hyps = show_hyps'} raw_th =
  let
    val show_tags = Config.get ctxt show_tags;
    val show_hyps = Config.get ctxt show_hyps;

    val th = raw_th
      |> perhaps (try (Thm.transfer (Proof_Context.theory_of ctxt)))
      |> perhaps (try Thm.strip_shyps);

    val hyps = if show_hyps then Thm.hyps_of th else Thm.undeclared_hyps (Context.Proof ctxt) th;
    val extra_shyps = Thm.extra_shyps th;
    val tags = Thm.get_tags th;
    val tpairs = Thm.tpairs_of th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o Syntax.pretty_term ctxt;


    val hlen = length extra_shyps + length hyps + length tpairs;
    val hsymbs =
      if hlen = 0 then []
      else if show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o Goal_Display.pretty_flexpair ctxt) tpairs @ map prt_term hyps @
           map (Syntax.pretty_sort ctxt) extra_shyps)]
      else [Pretty.brk 2, Pretty.str ("[" ^ replicate_string hlen "." ^ "]")];
    val tsymbs =
      if null tags orelse not show_tags then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term (Thm.prop_of th) :: (hsymbs @ tsymbs)) end;

fun pretty_thm ctxt = pretty_thm_raw ctxt {quote = false, show_hyps = true};
fun pretty_thm_item ctxt th = Pretty.item [pretty_thm ctxt th];

fun pretty_thm_global thy =
  pretty_thm_raw (Syntax.init_pretty_global thy) {quote = false, show_hyps = false};

val string_of_thm = Pretty.string_of oo pretty_thm;
val string_of_thm_global = Pretty.string_of oo pretty_thm_global;



(** print theory **)

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
    fun prt_const (c, ty) = [Pretty.mark_str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];
    val prt_node = Defs.pretty_node ctxt;
    fun sort_node_wrt f = sort (Defs.fast_node_ord o apply2 f)

    fun pretty_classrel (c, []) = prt_cls c
      | pretty_classrel (c, cs) = Pretty.block
          (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 :: Pretty.commas (map prt_cls cs));

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

    fun pretty_axm (a, t) =
      Pretty.block [Pretty.mark_str a, Pretty.str ":", Pretty.brk 1, prt_term_no_vars t];

    fun pretty_finals reds = Pretty.block
      (Pretty.str "final:" :: Pretty.brk 1 :: Pretty.commas (map (prt_node o fst) reds));

    fun pretty_reduct (lhs, rhs) = Pretty.block
      ([prt_node lhs, Pretty.str "  ->", Pretty.brk 2] @
        Pretty.commas (map prt_node ((sort_node_wrt #1) rhs)));

    fun pretty_restrict (const, name) =
      Pretty.block ([prt_node const, Pretty.brk 2, Pretty.str ("(from " ^ quote name ^ ")")]);

    val defs = Theory.defs_of thy;
    val {restricts, reducts} = Defs.dest defs;
    val tsig = Sign.tsig_of thy;
    val consts = Sign.consts_of thy;
    val {const_space, constants, constraints} = Consts.dest consts;
    val {classes, default, types, ...} = Type.rep_tsig tsig;
    val type_space = Type.type_space tsig;
    val (class_space, class_algebra) = classes;
    val classes = Sorts.classes_of class_algebra;
    val arities = Sorts.arities_of class_algebra;

    fun extern_node (Defs.NConst c) = Defs.NConst (Name_Space.extern ctxt const_space c)
      | extern_node (Defs.NType t) = Defs.NType (Name_Space.extern ctxt type_space t);

    val clsses =
      Name_Space.extern_entries verbose ctxt class_space
        (map (fn ((c, _), cs) => (c, Sign.minimize_sort thy cs)) (Graph.dest classes))
      |> map (apfst #1);
    val tdecls = Name_Space.extern_table verbose ctxt types |> map (apfst #1);
    val arties =
      Name_Space.extern_entries verbose ctxt (Type.type_space tsig) (Symtab.dest arities)
      |> map (apfst #1);

    fun prune_const c = not verbose andalso Consts.is_concealed consts c;

    fun prune_node (Defs.NConst c) = prune_const c
      | prune_node (Defs.NType t) = not verbose andalso Name_Space.is_concealed type_space t;

    val cnsts = Name_Space.markup_entries verbose ctxt const_space constants;
    val log_cnsts = map_filter (fn (c, (ty, NONE)) => SOME (c, ty) | _ => NONE) cnsts;
    val abbrevs = map_filter (fn (c, (ty, SOME t)) => SOME (c, (ty, t)) | _ => NONE) cnsts;
    val cnstrs = Name_Space.markup_entries verbose ctxt const_space constraints;

    val axms = Name_Space.markup_table verbose ctxt (Theory.axiom_table thy);

    val (reds0, (reds1, reds2)) = filter_out (prune_node o fst o fst) reducts
      |> map (fn (lhs, rhs) =>
        (apfst extern_node lhs, map (apfst extern_node) (filter_out (prune_node o fst) rhs)))
      |> sort_node_wrt (#1 o #1)
      |> List.partition (null o #2)
      ||> List.partition (Defs.plain_args o #2 o #1);
    val rests = restricts |> map (apfst (apfst extern_node)) |> sort_node_wrt (#1 o #1);
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
      Pretty.block
        (Pretty.breaks (Pretty.str "oracles:" ::
          map Pretty.mark_str (Thm.extern_oracles verbose ctxt))),
      Pretty.big_list "definitions:"
        [pretty_finals reds0,
         Pretty.big_list "non-overloaded:" (map pretty_reduct reds1),
         Pretty.big_list "overloaded:" (map pretty_reduct reds2),
         Pretty.big_list "pattern restrictions:" (map pretty_restrict rests)]]
  end;

end;

structure Basic_Display: BASIC_DISPLAY = Display;
open Basic_Display;
