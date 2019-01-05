(*  Title:      HOL/Types_To_Sets/local_typedef.ML
    Author:     Ondřej Kunčar, TU München

The Local Typedef Rule (extension of the logic).
*)

signature LOCAL_TYPEDEF =
sig
  val cancel_type_definition: thm -> thm
  val cancel_type_definition_attr: attribute
end;

structure Local_Typedef : LOCAL_TYPEDEF =
struct

(*
Local Typedef Rule (LT)

  \<Gamma> \<turnstile> (\<exists>(Rep::\<beta> \<Rightarrow> \<tau>) Abs. type_definition Rep Abs A) \<Longrightarrow> \<phi>
------------------------------------------------------------- [\<beta> not in \<phi>, \<Gamma>, A;
                       \<Gamma> \<turnstile> A \<noteq> \<emptyset> \<Longrightarrow> \<phi>                        sort(\<beta>)=HOL.type]
*)

(** BEGINNING OF THE CRITICAL CODE **)

fun dest_typedef (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _,
      (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, Abs_type,
      (Const (\<^const_name>\<open>type_definition\<close>, _)) $ Bound 1 $ Bound 0 $ set)))) =
    (Abs_type, set)
   | dest_typedef t = raise TERM ("dest_typedef", [t]);

fun cancel_type_definition_cterm thm =
  let
    fun err msg = raise THM ("cancel_type_definition: " ^ msg, 0, [thm]);

    val thy = Thm.theory_of_thm thm;
    val prop = Thm.prop_of thm;
    val hyps = Thm.hyps_of thm;

    val _ = null (Thm.tpairs_of thm) orelse err "the theorem contains unsolved flex-flex pairs";

    val (typedef_assm, phi) = Logic.dest_implies prop
      handle TERM _ => err "the theorem is not an implication";
    val (abs_type, set) = typedef_assm |> HOLogic.dest_Trueprop |> dest_typedef
      handle TERM _ => err ("the assumption is not of the form "
        ^ quote "\<exists>Rep Abs. type_definition Rep Abs A");

    val (repT, absT) = Term.dest_funT abs_type;
    val _ = Term.is_TVar absT orelse err "the abstract type is not a schematic type variable";
    val (absT_name, sorts) = Term.dest_TVar absT;

    val typeS = Sign.defaultS thy;
    val _ = sorts = typeS orelse err ("the type " ^ quote (fst absT_name) ^ " is not of the sort "
      ^ quote (Syntax.string_of_sort_global thy typeS));

    fun contains_absT tm = member (op=) (Term.add_tvars tm []) (absT_name, sorts);
    fun err_contains_absT_in msg = err (msg ^ " contains the forbidden type "
      ^ quote (fst absT_name));
    val _ = not (contains_absT phi) orelse err_contains_absT_in "the conclusion";
    val _ = not (contains_absT set) orelse err_contains_absT_in "the set term";
    (* the following test is superfluous; the meta hypotheses cannot currently contain TVars *)
    val _ = not (exists contains_absT hyps) orelse err_contains_absT_in "one of the hypotheses";

    val not_empty_assm = HOLogic.mk_Trueprop
      (HOLogic.mk_not (HOLogic.mk_eq (set, HOLogic.mk_set repT [])));
    val prop = Logic.list_implies (hyps @ [not_empty_assm], phi);
  in
    Thm.global_cterm_of thy prop |> Thm.weaken_sorts (Thm.shyps_of thm)
  end;

(** END OF THE CRITICAL CODE **)

val (_, cancel_type_definition_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>cancel_type_definition\<close>, cancel_type_definition_cterm)));

fun cancel_type_definition thm =
  Drule.implies_elim_list (cancel_type_definition_oracle thm) (map Thm.assume (Thm.chyps_of thm));

val cancel_type_definition_attr = Thm.rule_attribute [] (K cancel_type_definition);

val _ = Context.>> (Context.map_theory (Attrib.setup \<^binding>\<open>cancel_type_definition\<close>
  (Scan.succeed cancel_type_definition_attr) "cancel a local type definition"));

end;
