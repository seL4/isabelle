(*  Title:      HOL/Tools/ATP/atp_waldmeister.ML
    Author:     Albert Steckermeier, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature ATP_WALDMEISTER =
sig
  type 'a atp_problem = 'a ATP_Problem.atp_problem
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature

  val generate_waldmeister_problem: Proof.context -> term list -> term ->
    ((string * stature) * term) list ->
    string atp_problem * string Symtab.table * (string * term) list * int Symtab.table
  val termify_waldmeister_proof : Proof.context -> string Symtab.table -> string atp_proof ->
    (term, string) atp_step list
end;

structure ATP_Waldmeister : ATP_WALDMEISTER =
struct

open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct

type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
type atp_connective = ATP_Problem.atp_connective
type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
type atp_format = ATP_Problem.atp_format
type atp_formula_role = ATP_Problem.atp_formula_role
type 'a atp_problem = 'a ATP_Problem.atp_problem

val const_prefix = #"c"
val var_prefix = #"V"
val free_prefix = #"f"
val conjecture_condition_name = "condition"

val factsN = "Relevant facts"
val helpersN = "Helper facts"
val conjN = "Conjecture"

exception Failure
exception FailureMessage of string

(*
Some utilitary functions for translation.
*)

fun is_eq (Const (@{const_name "HOL.eq"}, _) $ _ $ _) = true
  | is_eq _ = false

fun gen_ascii_tuple str = (str, ascii_of str)

(*
Translation from Isabelle theorms and terms to ATP terms.
*)

fun trm_to_atp'' (Const (x, _)) args = [ATerm ((gen_ascii_tuple (String.str const_prefix ^ x), []), args)]
  | trm_to_atp'' (Free (x, _)) args = ATerm ((gen_ascii_tuple (String.str free_prefix ^ x), []), [])::args
  | trm_to_atp'' (Var ((x, _), _)) args = ATerm ((gen_ascii_tuple (String.str var_prefix ^ x), []), [])::args
  | trm_to_atp'' (trm1 $ trm2) args = trm_to_atp'' trm1 (trm_to_atp'' trm2 [] @ args)
  | trm_to_atp'' _ args = args

fun trm_to_atp' trm = trm_to_atp'' trm [] |> hd

fun eq_trm_to_atp (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) =
    ATerm ((("equal", "equal"), []), [trm_to_atp' lhs, trm_to_atp' rhs])
  | eq_trm_to_atp _ = raise Failure

fun trm_to_atp trm =
  if is_eq trm then eq_trm_to_atp trm
  else HOLogic.mk_eq (trm, @{term True}) |> eq_trm_to_atp

fun thm_to_atps split_conj prop_term =
  if split_conj then map trm_to_atp (prop_term |> HOLogic.dest_conj)
  else [prop_term |> trm_to_atp]

fun prepare_conjecture conj_term =
  let
    fun split_conj_trm (Const (@{const_name Pure.imp}, _) $ condition $ consequence) =
        (SOME condition, consequence)
      | split_conj_trm conj = (NONE, conj)
    val (condition, consequence) = split_conj_trm conj_term
  in
    (case condition of SOME x => HOLogic.dest_conj x |> map trm_to_atp | NONE => []
    , trm_to_atp consequence)
  end

(* Translation from ATP terms to Isabelle terms. *)

fun construct_term (ATerm ((name, _), _)) =
  let
    val prefix = String.sub (name, 0)
  in
    if prefix = const_prefix then
      Const (String.extract (name, 1, NONE), Type ("", []))
    else if prefix = free_prefix then
      Free (String.extract (name, 1, NONE), TFree ("", []))
    else if Char.isUpper prefix then
      Var ((name, 0), TVar (("", 0), []))
    else
      raise Failure
  end
  | construct_term _ = raise Failure

fun atp_to_trm' (ATerm (descr, args)) =
    (case args of
      [] => construct_term (ATerm (descr, args))
     | _ => Term.list_comb (construct_term (ATerm (descr, args)), map atp_to_trm' args))
     | atp_to_trm' _ = raise Failure

fun atp_to_trm (ATerm (("equal", _), [lhs, rhs])) =
    Const (@{const_name HOL.eq}, Type ("", [])) $ atp_to_trm' lhs $ atp_to_trm' rhs
  | atp_to_trm (ATerm (("$true", _), _)) = Const ("HOL.True", Type ("", []))
  | atp_to_trm _ = raise Failure

fun formula_to_trm (AAtom aterm) = atp_to_trm aterm
  | formula_to_trm (AConn (ANot, [aterm])) =
    Const (@{const_name HOL.Not}, @{typ "bool \<Rightarrow> bool"}) $ formula_to_trm aterm
  | formula_to_trm _ = raise Failure

(* Abstract translation *)

fun mk_formula prefix_name name atype aterm =
  Formula ((prefix_name ^ ascii_of name, name), atype, AAtom aterm, NONE, [])

fun problem_lines_of_fact prefix ((s, _), t) =
  map (mk_formula prefix s Axiom) (thm_to_atps false t)

fun make_nice problem = nice_atp_problem true CNF problem

fun mk_conjecture aterm =
  let
    val formula = mk_anot (AAtom aterm)
  in
    Formula ((conjecture_prefix ^ "0", ""), Hypothesis, formula, NONE, [])
  end

fun atp_proof_step_to_term (name, role, formula, formula_name, step_names) =
  (name, role, formula_to_trm formula, formula_name, step_names)

fun generate_waldmeister_problem ctxt hyp_ts0 concl_t0 facts0 =
  let
    val thy = Proof_Context.theory_of ctxt

    val preproc = Object_Logic.atomize_term thy

    val hyp_ts = map preproc hyp_ts0
    val concl_t = preproc concl_t0
    val facts = map (apsnd preproc) facts0

    val (conditions, consequence) = prepare_conjecture concl_t
    val fact_lines = maps (problem_lines_of_fact (fact_prefix ^ "0_" (* FIXME *))) facts
    val condition_lines =
      map (mk_formula fact_prefix conjecture_condition_name Hypothesis) conditions
    val axiom_lines = fact_lines @ condition_lines
    val conj_line = mk_conjecture consequence

    val helper_lines =
      if List.exists (is_eq o snd) facts orelse not (is_eq concl_t) then
        [(helpersN,
          @{thms waldmeister_fol}
          |> map (fn th => (("", (Global, General)), preproc (prop_of th)))
          |> maps (problem_lines_of_fact helper_prefix))]
      else
        []
    val problem = (factsN, axiom_lines) :: helper_lines @ [(conjN, [conj_line])]

    val (nice_problem, symtabs) = make_nice problem
  in
    (nice_problem, Symtab.empty, [], Symtab.empty)
  end

fun termify_line ctxt (name, role, AAtom u, rule, deps) =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = u
      |> atp_to_trm
      |> singleton (infer_formula_types ctxt)
      |> HOLogic.mk_Trueprop
  in
    (name, role, t, rule, deps)
  end

fun termify_waldmeister_proof ctxt pool =
  nasty_atp_proof pool
  #> map (termify_line ctxt)
  #> repair_waldmeister_endgame

end;
