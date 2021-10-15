(*   Title:   HOL/ex/Sketch_and_Explore.thy
     Author:  Florian Haftmann, TU Muenchen
*)

chapter \<open>Experimental commands \<^text>\<open>sketch\<close> and \<^text>\<open>explore\<close>\<close>

theory Sketch_and_Explore
  imports Main \<comment> \<open>TODO: generalize existing sledgehammer functions to Pure\<close>
  keywords "sketch" "explore" :: diag
begin

ML \<open>
fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val concl = Logic.strip_imp_concl horn;
  in (fixes, assms, concl) end;

fun maybe_quote ctxt =
  ATP_Util.maybe_quote (Thy_Header.get_keywords' ctxt);

fun print_typ ctxt T =
  T
  |> Syntax.string_of_typ ctxt
  |> maybe_quote ctxt;

fun print_term ctxt t =
  t
  |> singleton (Syntax.uncheck_terms ctxt)
  |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt
      \<comment> \<open>TODO pointless to annotate explicit fixes in term\<close>
  |> Print_Mode.setmp [] (Syntax.unparse_term ctxt #> Pretty.string_of)
  |> Sledgehammer_Util.simplify_spaces
  |> maybe_quote ctxt;

fun eigen_context_for_statement (fixes, assms, concl) ctxt =
  let
    val (fixes', ctxt') = Variable.add_fixes (map fst fixes) ctxt;
    val subst_free = AList.lookup (op =) (map fst fixes ~~ fixes')
    val subst = map_aterms (fn Free (v, T) => Free (the_default v (subst_free v), T)
      | t => t)
    val assms' = map subst assms;
    val concl' = subst concl;
  in ((fixes, assms', concl'), ctxt') end;

fun print_isar_skeleton ctxt indent keyword stmt =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (print_term ctxt') assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));
    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [prefix ^ "  " ^ (if is_none if_s then "" else "using that ") ^ "sorry"]);
  in
    s
  end;

fun print_sketch ctxt method_text clauses =
  "proof" ^ method_text :: map (print_isar_skeleton ctxt 2 "show") clauses @ ["qed"];

fun print_exploration ctxt method_text [clause] =
    ["proof -", print_isar_skeleton ctxt 2 "have" clause,
      "  then show ?thesis", "    by" ^ method_text, "qed"]
  | print_exploration ctxt method_text (clause :: clauses) =
    "proof -" :: print_isar_skeleton ctxt 2 "have" clause
      :: map (print_isar_skeleton ctxt 2 "moreover have") clauses
      @ ["  ultimately show ?thesis", "    by" ^ method_text, "qed"];

fun coalesce_method_txt [] = ""
  | coalesce_method_txt [s] = s
  | coalesce_method_txt (s1 :: s2 :: ss) =
      if s1 = "(" orelse s1 = "["
        orelse s2 = ")" orelse s2 = "]" orelse s2= ":"
      then s1 ^ coalesce_method_txt (s2 :: ss)
      else s1 ^ " " ^ coalesce_method_txt (s2 :: ss);

fun print_proof_text_from_state print (some_method_ref : ((Method.text * Position.range) * Token.T list) option) state =
  let
    val state' = state
      |> Proof.proof (Option.map fst some_method_ref)
      |> Seq.the_result ""

    val { context = ctxt, facts = _, goal } = Proof.goal state';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text = case some_method_ref of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val lines = if null clauses then
      if is_none some_method_ref then ["  .."]
      else ["  by" ^ method_text]
      else print ctxt_print method_text clauses;
    val message = Active.sendback_markup_properties [] (cat_lines lines);
  in
    (state |> tap (fn _ => Output.information message))
  end

val sketch = print_proof_text_from_state print_sketch;

fun explore method_ref = print_proof_text_from_state print_exploration (SOME method_ref);

fun sketch_cmd some_method_text =
  Toplevel.keep_proof (K () o sketch some_method_text o Toplevel.proof_of)

fun explore_cmd method_text =
  Toplevel.keep_proof (K () o explore method_text o Toplevel.proof_of)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch\<close>
    "print sketch of Isar proof text after method application"
    (Scan.option (Scan.trace Method.parse) >> sketch_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>explore\<close>
    "explore proof obligations after method application as Isar proof text"
    (Scan.trace Method.parse >> explore_cmd);
\<close>

end
