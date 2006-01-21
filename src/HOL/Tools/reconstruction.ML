(*  Title:      HOL/Reconstruction.thy
    ID: $Id$
    Author:     Lawrence C Paulson and Claire Quigley
    Copyright   2004  University of Cambridge
*)

(*Attributes for reconstructing external resolution proofs*)

structure Reconstruction =
struct

(**************************************************************)
(* extra functions necessary for factoring and paramodulation *)
(**************************************************************)

fun mksubstlist [] sublist = sublist
  | mksubstlist ((a, (_, b)) :: rest) sublist =
      let val vartype = type_of b
          val avar = Var(a,vartype)
          val newlist = ((avar,b)::sublist)
      in mksubstlist rest newlist end;


(**** attributes ****)

(** Binary resolution **)

fun binary_rule ((cl1, lit1), (cl2 , lit2)) =
     select_literal (lit1 + 1) cl1
     RSN ((lit2 + 1), cl2);

val binary = Attrib.syntax
  (Scan.lift Args.nat -- Attrib.thm -- Scan.lift Args.nat
    >> (fn ((i, B), j) => Thm.rule_attribute (fn _ => fn A => binary_rule ((A, i), (B, j)))));


fun inst_single sign t1 t2 cl =
    let val ct1 = cterm_of sign t1 and ct2 = cterm_of sign t2
    in  hd (Seq.list_of(distinct_subgoals_tac
                            (cterm_instantiate [(ct1,ct2)] cl)))
    end;

fun inst_subst sign substs cl =
    if (is_Var (fst(hd(substs))))
    then inst_single sign (fst (hd substs)) (snd (hd substs)) cl
    else if (is_Var (snd(hd(substs))))
    then inst_single sign (snd (hd substs)) (fst (hd substs)) cl
    else raise THM ("inst_subst", 0, [cl]);


(** Factoring **)

fun factor_rule (cl, lit1, lit2) =
    let
       val prems = prems_of cl
       val fac1 = List.nth (prems,lit1)
       val fac2 = List.nth (prems,lit2)
       val sign = sign_of_thm cl
       val unif_env = Unify.unifiers (sign, Envir.empty 0, [(fac1, fac2)])
       val newenv = ReconTranslateProof.getnewenv unif_env
       val envlist = Envir.alist_of newenv
     in
       inst_subst sign (mksubstlist envlist []) cl
    end;

val factor = Attrib.syntax (Scan.lift (Args.nat -- Args.nat)
  >> (fn (i, j) => Thm.rule_attribute (fn _ => fn A => factor_rule (A, i, j))));


(** Paramodulation **)

(*subst with premises exchanged: that way, side literals of the equality will appear
  as the second to last premises of the result.*)
val rev_subst = rotate_prems 1 subst;

fun paramod_rule ((cl1, lit1), (cl2, lit2)) =
    let  val eq_lit_th = select_literal (lit1+1) cl1
         val mod_lit_th = select_literal (lit2+1) cl2
         val eqsubst = eq_lit_th RSN (2,rev_subst)
         val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 eqsubst)
         val newth' = Seq.hd (flexflex_rule newth)
    in Meson.negated_asm_of_head newth' end;


val paramod = Attrib.syntax (Scan.lift Args.nat -- Attrib.thm -- Scan.lift Args.nat
  >> (fn ((i, B), j) => Thm.rule_attribute (fn _ => fn A => paramod_rule ((A, i), (B, j)))));


(** Demodulation: rewriting of a single literal (Non-Unit Rewriting, SPASS) **)

fun demod_rule ((cl1, lit1), (cl2 , lit2)) =
    let  val eq_lit_th = select_literal (lit1+1) cl1
         val mod_lit_th = select_literal (lit2+1) cl2
         val (fmod_th,thaw) = Drule.freeze_thaw_robust mod_lit_th
         val eqsubst = eq_lit_th RSN (2,rev_subst)
         val newth = Seq.hd(biresolution false [(false, fmod_th)] 1 eqsubst)
         val offset = #maxidx(rep_thm newth) + 1
                          (*ensures "renaming apart" even when Vars are frozen*)
    in Meson.negated_asm_of_head (thaw offset newth) end;

val demod = Attrib.syntax (Scan.lift Args.nat -- Attrib.thm -- Scan.lift Args.nat
  >> (fn ((i, B), j) => Thm.rule_attribute (fn _ => fn A => demod_rule ((A, i), (B, j)))));


(** Conversion of a theorem into clauses **)

(*For efficiency, we rely upon memo-izing in ResAxioms.*)
fun clausify_rule (th,i) = List.nth (ResAxioms.meta_cnf_axiom th, i)

val clausify = Attrib.syntax (Scan.lift Args.nat
  >> (fn i => Thm.rule_attribute (fn _ => fn th => clausify_rule (th, i))));


(** theory setup **)

val setup =
  Attrib.add_attributes
    [("binary", binary, "binary resolution"),
     ("paramod", paramod, "paramodulation"),
     ("demod", demod, "demodulation"),
     ("factor", factor, "factoring"),
     ("clausify", clausify, "conversion to clauses")];

end
