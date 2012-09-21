(*  Title:      HOL/BNF/Tools/bnf_lfp_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Library for the datatype construction.
*)

signature BNF_LFP_UTIL =
sig
  val HOL_arg_cong: cterm -> thm

  val mk_bij_betw: term -> term -> term -> term
  val mk_cardSuc: term -> term
  val mk_convol: term * term -> term
  val mk_cpow: term -> term
  val mk_inver: term -> term -> term -> term
  val mk_not_empty: term -> term
  val mk_not_eq: term -> term -> term
  val mk_rapp: term -> typ -> term
  val mk_relChain: term -> term -> term
  val mk_underS: term -> term
  val mk_worec: term -> term -> term
end;

structure BNF_LFP_Util : BNF_LFP_UTIL =
struct

open BNF_Util

fun HOL_arg_cong ct = Drule.instantiate'
  (map SOME (Thm.dest_ctyp (Thm.ctyp_of_term ct))) [NONE, NONE, SOME ct] arg_cong;

(*reverse application*)
fun mk_rapp arg T = Term.absdummy (fastype_of arg --> T) (Bound 0 $ arg);

fun mk_underS r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (@{const_name rel.underS}, mk_relT (T, T) --> T --> HOLogic.mk_setT T) $ r end;

fun mk_worec r f =
  let val (A, AB) = apfst domain_type (dest_funT (fastype_of f));
  in Const (@{const_name wo_rel.worec}, mk_relT (A, A) --> (AB --> AB) --> AB) $ r $ f end;

fun mk_relChain r f =
  let val (A, AB) = `domain_type (fastype_of f);
  in Const (@{const_name relChain}, mk_relT (A, A) --> AB --> HOLogic.boolT) $ r $ f end;

fun mk_cardSuc r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (@{const_name cardSuc}, mk_relT (T, T) --> mk_relT (`I (HOLogic.mk_setT T))) $ r end;

fun mk_cpow r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (@{const_name cpow}, mk_relT (T, T) --> mk_relT (`I (HOLogic.mk_setT T))) $ r end;

fun mk_bij_betw f A B =
 Const (@{const_name bij_betw},
   fastype_of f --> fastype_of A --> fastype_of B --> HOLogic.boolT) $ f $ A $ B;

fun mk_inver f g A =
 Const (@{const_name inver}, fastype_of f --> fastype_of g --> fastype_of A --> HOLogic.boolT) $
   f $ g $ A;

fun mk_not_eq x y = HOLogic.mk_not (HOLogic.mk_eq (x, y));

fun mk_not_empty B = mk_not_eq B (HOLogic.mk_set (HOLogic.dest_setT (fastype_of B)) []);

fun mk_convol (f, g) =
  let
    val (fU, fTU) = `range_type (fastype_of f);
    val ((gT, gU), gTU) = `dest_funT (fastype_of g);
    val convolT = fTU --> gTU --> gT --> HOLogic.mk_prodT (fU, gU);
  in Const (@{const_name convol}, convolT) $ f $ g end;

end;
