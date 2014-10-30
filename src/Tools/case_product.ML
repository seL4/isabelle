(*  Title:      Tools/case_product.ML
    Author:     Lars Noschinski, TU Muenchen

Combine two case rules into a single one.

Assumes that the theorems are of the form
  "[| C1; ...; Cm; A1 ==> P; ...; An ==> P |] ==> P"
where m is given by the "consumes" attribute of the theorem.
*)

signature CASE_PRODUCT =
sig
  val combine: Proof.context -> thm -> thm -> thm
  val combine_annotated: Proof.context -> thm -> thm -> thm
  val annotation: thm -> thm -> attribute
end

structure Case_Product: CASE_PRODUCT =
struct

(*instantiate the conclusion of thm2 to the one of thm1*)
fun inst_concl thm1 thm2 =
  let
    val cconcl_of = Drule.strip_imp_concl o Thm.cprop_of
  in Thm.instantiate (Thm.match (cconcl_of thm2, cconcl_of thm1)) thm2 end

fun inst_thms thm1 thm2 ctxt =
  let
    val import = yield_singleton (apfst snd oo Variable.import true)
    val (i_thm1, ctxt') = import thm1 ctxt
    val (i_thm2, ctxt'') = import (inst_concl i_thm1 thm2) ctxt'
  in ((i_thm1, i_thm2), ctxt'') end

(*
Return list of prems, where loose bounds have been replaced by frees.
FIXME: Focus
*)
fun free_prems t ctxt =
  let
    val bs = Term.strip_all_vars t
    val (names, ctxt') = Variable.variant_fixes (map fst bs) ctxt
    val subst = map Free (names ~~ map snd bs)
    val t' = map (Term.subst_bounds o pair (rev subst)) (Logic.strip_assums_hyp t)
  in ((t', subst), ctxt') end

fun build_concl_prems thm1 thm2 ctxt =
  let
    val concl = Thm.concl_of thm1

    fun is_consumes t = not (Logic.strip_assums_concl t aconv concl)
    val (p_cons1, p_cases1) = take_prefix is_consumes (Thm.prems_of thm1)
    val (p_cons2, p_cases2) = take_prefix is_consumes (Thm.prems_of thm2)

    val p_cases_prod = map (fn p1 => map (fn p2 =>
      let
        val (((t1, subst1), (t2, subst2)), _) = ctxt
          |> free_prems p1 ||>> free_prems p2
      in
        Logic.list_implies (t1 @ t2, concl)
        |> fold_rev Logic.all (subst1 @ subst2)
      end) p_cases2) p_cases1

    val prems = p_cons1 :: p_cons2 :: p_cases_prod
  in
    (concl, prems)
  end

fun case_product_tac ctxt prems struc thm1 thm2 =
  let
    val (p_cons1 :: p_cons2 :: premss) = unflat struc prems
    val thm2' = thm2 OF p_cons2
  in
    resolve_tac [thm1 OF p_cons1]
     THEN' EVERY' (map (fn p =>
       resolve_tac [thm2'] THEN' EVERY' (map (Proof_Context.fact_tac ctxt o single) p)) premss)
  end

fun combine ctxt thm1 thm2 =
  let
    val ((i_thm1, i_thm2), ctxt') = inst_thms thm1 thm2 ctxt
    val (concl, prems_rich) = build_concl_prems i_thm1 i_thm2 ctxt'
  in
    Goal.prove ctxt' [] (flat prems_rich) concl
      (fn {context = ctxt'', prems} =>
        case_product_tac ctxt'' prems prems_rich i_thm1 i_thm2 1)
    |> singleton (Variable.export ctxt' ctxt)
  end

fun annotation_rule thm1 thm2 =
  let
    val (cases1, cons1) = apfst (map fst) (Rule_Cases.get thm1)
    val (cases2, cons2) = apfst (map fst) (Rule_Cases.get thm2)
    val names = map_product (fn (x, _) => fn (y, _) => x ^ "_" ^ y) cases1 cases2
  in
    Rule_Cases.name names o Rule_Cases.put_consumes (SOME (cons1 + cons2))
  end

fun annotation thm1 thm2 = Thm.rule_attribute (K (annotation_rule thm1 thm2))

fun combine_annotated ctxt thm1 thm2 =
  combine ctxt thm1 thm2
  |> annotation_rule thm1 thm2


(* attribute setup *)

val _ =
  Theory.setup
   (Attrib.setup @{binding case_product}
      let
        fun combine_list ctxt = fold (fn x => fn y => combine_annotated ctxt y x)
      in
        Attrib.thms >> (fn thms => Thm.rule_attribute (fn ctxt => fn thm =>
          combine_list (Context.proof_of ctxt) thms thm))
      end
    "product with other case rules")

end
