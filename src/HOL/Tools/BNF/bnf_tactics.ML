(*  Title:      HOL/Tools/BNF/bnf_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

General tactics for bounded natural functors.
*)

signature BNF_TACTICS =
sig
  include CTR_SUGAR_GENERAL_TACTICS

  val fo_rtac: thm -> Proof.context -> int -> tactic
  val subst_tac: Proof.context -> int list option -> thm list -> int -> tactic
  val subst_asm_tac: Proof.context -> int list option -> thm list -> int -> tactic

  val mk_rotate_eq_tac: (int -> tactic) -> thm -> thm -> thm -> thm -> ''a list -> ''a list ->
    int -> tactic

  val mk_pointfree: Proof.context -> thm -> thm

  val mk_Abs_bij_thm: Proof.context -> thm -> thm -> thm
  val mk_Abs_inj_thm: thm -> thm

  val mk_map_comp_id_tac: Proof.context -> thm -> tactic
  val mk_map_cong0_tac: Proof.context -> int -> thm -> tactic
  val mk_map_cong0L_tac: int -> thm -> thm -> tactic
end;

structure BNF_Tactics : BNF_TACTICS =
struct

open Ctr_Sugar_General_Tactics
open BNF_Util

(*stolen from Christian Urban's Cookbook (and adapted slightly)*)
fun fo_rtac thm = Subgoal.FOCUS (fn {concl, ...} =>
  let
    val concl_pat = Drule.strip_imp_concl (cprop_of thm)
    val insts = Thm.first_order_match (concl_pat, concl)
  in
    rtac (Drule.instantiate_normalize insts thm) 1
  end
  handle Pattern.MATCH => no_tac);

(*unlike "unfold_thms_tac", it succeed when the RHS contains schematic variables not in the LHS*)
fun subst_tac ctxt = EqSubst.eqsubst_tac ctxt o the_default [0];
fun subst_asm_tac ctxt = EqSubst.eqsubst_asm_tac ctxt o the_default [0];


(*transforms f (g x) = h (k x) into f o g = h o k using first order matches for f, g, h, and k*)
fun mk_pointfree ctxt thm = thm
  |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  |> apply2 (dest_comb #> apsnd (dest_comb #> fst) #> HOLogic.mk_comp)
  |> mk_Trueprop_eq
  |> (fn goal => Goal.prove_sorry ctxt [] [] goal
    (K (rtac @{thm ext} 1 THEN
        unfold_thms_tac ctxt ([o_apply, unfold_thms ctxt [o_apply] (mk_sym thm)]) THEN
        rtac refl 1)))
  |> Thm.close_derivation;


(* Theorems for open typedefs with UNIV as representing set *)

fun mk_Abs_inj_thm inj = inj OF (replicate 2 UNIV_I);
fun mk_Abs_bij_thm ctxt Abs_inj_thm surj = rule_by_tactic ctxt ((rtac surj THEN' etac exI) 1)
  (Abs_inj_thm RS @{thm bijI'});



(* General tactic generators *)

(*applies assoc rule to the lhs of an equation as long as possible*)
fun mk_flatten_assoc_tac refl_tac trans assoc cong = rtac trans 1 THEN
  REPEAT_DETERM (CHANGED ((FIRST' [rtac trans THEN' rtac assoc, rtac cong THEN' refl_tac]) 1)) THEN
  refl_tac 1;

(*proves two sides of an equation to be equal assuming both are flattened and rhs can be obtained
from lhs by the given permutation of monoms*)
fun mk_rotate_eq_tac refl_tac trans assoc com cong =
  let
    fun gen_tac [] [] = K all_tac
      | gen_tac [x] [y] = if x = y then refl_tac else error "mk_rotate_eq_tac: different lists"
      | gen_tac (x :: xs) (y :: ys) = if x = y
        then rtac cong THEN' refl_tac THEN' gen_tac xs ys
        else rtac trans THEN' rtac com THEN'
          K (mk_flatten_assoc_tac refl_tac trans assoc cong) THEN'
          gen_tac (xs @ [x]) (y :: ys)
      | gen_tac _ _ = error "mk_rotate_eq_tac: different lists";
  in
    gen_tac
  end;

fun mk_map_comp_id_tac ctxt map_comp0 =
  (rtac trans THEN' rtac map_comp0 THEN' K (unfold_thms_tac ctxt @{thms comp_id}) THEN' rtac refl) 1;

fun mk_map_cong0_tac ctxt m map_cong0 =
  EVERY' [rtac mp, rtac map_cong0,
    CONJ_WRAP' (K (rtac ballI THEN' Goal.assume_rule_tac ctxt)) (1 upto m)] 1;

fun mk_map_cong0L_tac passive map_cong0 map_id =
  (rtac trans THEN' rtac map_cong0 THEN' EVERY' (replicate passive (rtac refl))) 1 THEN
  REPEAT_DETERM (EVERY' [rtac trans, etac bspec, atac, rtac sym, rtac @{thm id_apply}] 1) THEN
  rtac map_id 1;

end;
