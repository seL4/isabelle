(*  Title:      Pure/Isar/subclass.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Prove subclass relations between type classes
*)

signature SUBCLASS =
sig
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
  (*FIXME val prove_subclass: tactic -> class * class -> theory -> theory*)
end;

structure Subclass : SUBCLASS =
struct

(** auxiliary **)

fun prove_interpretation_in tac after_qed (name, expr) =
  Locale.interpretation_in_locale
      (ProofContext.theory after_qed) (name, expr)
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun OF_LAST thm1 thm2 =
  let
    val n = (length o Logic.strip_imp_prems o prop_of) thm2;
  in (thm1 RSN (n, thm2)) end;

fun strip_all_ofclass thy sort =
  let
    val typ = TVar ((Name.aT, 0), sort);
    fun prem_inclass t =
      case Logic.strip_imp_prems t
       of ofcls :: _ => try Logic.dest_inclass ofcls
        | [] => NONE;
    fun strip_ofclass class thm =
      thm OF (fst o AxClass.of_sort thy (typ, [class])) AxClass.cache;
    fun strip thm = case (prem_inclass o Thm.prop_of) thm
     of SOME (_, class) => thm |> strip_ofclass class |> strip
      | NONE => thm;
  in strip end;


(** subclassing **)

local

fun mk_subclass_rule lthy sup =
  let
    (*FIXME check for proper parameter inclusion (consts_of) (?)*)
    val ctxt = LocalTheory.target_of lthy;
    val thy = ProofContext.theory_of ctxt;
    val locale = Class.locale_of_class thy sup;
  in
    Locale.global_asms_of thy locale
    |> maps snd
    |> map (ObjectLogic.ensure_propT thy)
  end;

fun gen_subclass prep_class raw_sup lthy =
  let
    (*FIXME cleanup, provide tactical interface*)
    val ctxt = LocalTheory.target_of lthy;
    val thy = ProofContext.theory_of ctxt;
    val ctxt_thy = ProofContext.init thy;
    val sup = prep_class thy raw_sup;
    val sub = case Option.mapPartial (Class.class_of_locale thy)
       (TheoryTarget.peek lthy)
     of NONE => error "not in class context"
      | SOME sub => sub;
    val export =
      Assumption.export false ctxt ctxt_thy
      #> singleton (Variable.export ctxt ctxt_thy);
    val loc_name = Class.locale_of_class thy sub;
    val loc_expr = Locale.Locale (Class.locale_of_class thy sup);
    fun prove_classrel interp thy =
      let
        val classes = Sign.complete_sort thy [sup]
          |> filter_out (fn class' => Sign.subsort thy ([sub], [class']));
        fun instance_subclass (class1, class2) thy  =
          let
            val ax = #axioms (AxClass.get_info thy class1);
            val intro = #intro (AxClass.get_info thy class2)
              |> Drule.instantiate' [SOME (Thm.ctyp_of thy
                  (TVar ((Name.aT, 0), [class1])))] [];
            val thm =
              intro
              |> OF_LAST (interp OF ax)
              |> strip_all_ofclass thy (Sign.super_classes thy class2);
          in
            thy |> AxClass.add_classrel thm
          end;
      in
        thy |> fold_rev (curry instance_subclass sub) classes
      end;
    fun after_qed [thms] =
      let
        val thm = Conjunction.intr_balanced thms;
        val interp = export thm;
      in
        LocalTheory.theory (prove_classrel interp
          #> prove_interpretation_in (ProofContext.fact_tac [thm] 1)
             I (loc_name, loc_expr))
        (*#> (fn lthy => LocalTheory.reinit lthy thy) FIXME does not work as expected*)
      end;

  in Proof.theorem_i NONE after_qed [map (rpair []) (mk_subclass_rule lthy sup)] lthy end;

in

val subclass = gen_subclass (K I);
val subclass_cmd = gen_subclass Sign.read_class;

end; (*local*)

end;
