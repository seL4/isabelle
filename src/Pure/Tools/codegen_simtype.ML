(*  Title:      Pure/Tools/codegen_simtype.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Axiomatic extension of code generator: implement ("simulate") types
by other type expressions. Requires user proof but does not use
the proven theorems!
*)

signature CODEGEN_SIMTYPE =
sig
end;

structure CodegenSimtype: CODEGEN_SIMTYPE =
struct

local

fun gen_simtype prep_term do_proof (raw_repm, raw_absm) (raw_repi, raw_absi) raw_repe thy =
  let
    val repm = prep_term thy raw_repm;
    val absm = prep_term thy raw_absm;
    val repi = prep_term thy raw_repi;
    val absi = prep_term thy raw_absi;
    val (repe, repe_ty) = (dest_Const o prep_term thy) raw_repe;
    val repe_ty' = (snd o strip_type) repe_ty;
    fun dest_fun (ty as Type (_, [ty1, ty2])) =
          if is_funtype ty then (ty1, ty2)
          else raise TYPE ("dest_fun", [ty], [])
      | dest_fun ty = raise TYPE ("dest_fun", [ty], []);
    val PROP = ObjectLogic.ensure_propT thy
    val (ty_abs, ty_rep) = (dest_fun o type_of) repm;
    val (tyco_abs, ty_parms) = dest_Type ty_abs;
    val _ = if exists (fn TFree _ => false | _ => true) ty_parms then raise TYPE ("no TFree", ty_parms, []) else ();
    val repv = Free ("x", ty_rep);
    val absv = Free ("x", ty_abs);
    val rep_mor = Logic.mk_implies
      (PROP (absi $ absv), Logic.mk_equals (absm $ (repm $ absv), absv));
    val abs_mor = Logic.mk_implies
      (PROP (repi $ repv), PROP (Const (repe, ty_rep --> ty_rep --> repe_ty') $ (repm $ (absm $ repv)) $ repv));
    val rep_inv = Logic.mk_implies
      (PROP (absi $ absv), PROP (repi $ (repm $ absv)));
    val abs_inv = Logic.mk_implies
      (PROP (repi $ repv), PROP (absi $ (absm $ repv)));
  in
    thy
    |> do_proof (K I) [rep_mor, abs_mor, rep_inv, abs_inv]
  end;

fun gen_e_simtype do_proof = gen_simtype Sign.read_term do_proof;
fun gen_i_simtype do_proof = gen_simtype Sign.cert_term do_proof;

fun setup_proof after_qed props thy =
  thy
  |> ProofContext.init
  |> Proof.theorem_i PureThy.internalK NONE after_qed NONE ("", [])
       (map (fn t => (("", []), [(t, [])])) props);

fun tactic_proof tac after_qed props thy =
  let
    val thms = Goal.prove_multi thy [] [] props (K tac);
  in
    thy
    |> after_qed thms
  end;

in

val simtype = gen_e_simtype setup_proof;
val simtype_i = gen_i_simtype setup_proof;
val prove_simtype = gen_i_simtype o tactic_proof;

end; (*local*)

local

structure P = OuterParse
and K = OuterKeyword

in

val simtypeK = "code_simtype"

val simtypeP =
  OuterSyntax.command simtypeK "simulate type in executable code" K.thy_goal (
    (P.term -- P.term -- P.term -- P.term -- P.term)
    >> (fn ((((raw_repm, raw_absm), raw_repi), raw_absi), raw_repe) =>
          (Toplevel.print oo Toplevel.theory_to_proof)
            (simtype (raw_repm, raw_absm) (raw_repi, raw_absi) raw_repe))
  );

val _ = OuterSyntax.add_parsers [simtypeP];

end; (*local*)

end; (*struct*)
