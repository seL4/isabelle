(* Author: Lukas Bulwahn, TU Muenchen

Preprocessing definitions of predicates to introduction rules
*)

signature PREDICATE_COMPILE_PRED =
sig
  (* preprocesses an equation to a set of intro rules; defines new constants *)
  (*
  val preprocess_pred_equation : thm -> theory -> thm list * theory
  *)
  val preprocess : string -> theory -> (thm list list * theory) 
  (* output is the term list of clauses of an unknown predicate *)
  val preprocess_term : term -> theory -> (term list * theory)
  
  (*val rewrite : thm -> thm*)
  
end;
(* : PREDICATE_COMPILE_PREPROC_PRED *)
structure Predicate_Compile_Pred =
struct

open Predicate_Compile_Aux

fun is_compound ((Const ("Not", _)) $ t) =
    error "is_compound: Negation should not occur; preprocessing is defect"
  | is_compound ((Const ("Ex", _)) $ _) = true
  | is_compound ((Const (@{const_name "op |"}, _)) $ _ $ _) = true
  | is_compound ((Const ("op &", _)) $ _ $ _) =
    error "is_compound: Conjunction should not occur; preprocessing is defect"
  | is_compound _ = false

fun flatten constname atom (defs, thy) =
  if is_compound atom then
    let
      val constname = Name.variant (map (Long_Name.base_name o fst) defs)
        ((Long_Name.base_name constname) ^ "_aux")
      val full_constname = Sign.full_bname thy constname
      val (params, args) = List.partition (is_predT o fastype_of)
        (map Free (Term.add_frees atom []))
      val constT = map fastype_of (params @ args) ---> HOLogic.boolT
      val lhs = list_comb (Const (full_constname, constT), params @ args)
      val def = Logic.mk_equals (lhs, atom)
      val ([definition], thy') = thy
        |> Sign.add_consts_i [(Binding.name constname, constT, NoSyn)]
        |> PureThy.add_defs false [((Binding.name (constname ^ "_def"), def), [])]
    in
      (lhs, ((full_constname, [definition]) :: defs, thy'))
    end
  else
    (atom, (defs, thy))

fun flatten_intros constname intros thy =
  let
    val ctxt = ProofContext.init thy
    val ((_, intros), ctxt') = Variable.import true intros ctxt
    val (intros', (local_defs, thy')) = (fold_map o fold_map_atoms)
      (flatten constname) (map prop_of intros) ([], thy)
    val tac = fn {...} => SkipProof.cheat_tac thy'
    val intros'' = map (fn t => Goal.prove ctxt' [] [] t tac) intros'
      |> Variable.export ctxt' ctxt
  in
    (intros'', (local_defs, thy'))
  end

(* TODO: same function occurs in inductive package *)
fun select_disj 1 1 = []
  | select_disj _ 1 = [rtac @{thm disjI1}]
  | select_disj n i = (rtac @{thm disjI2})::(select_disj (n - 1) (i - 1));

fun introrulify thy th = 
  let
    val ctxt = (ProofContext.init thy)
    val ((_, [th']), ctxt') = Variable.import true [th] ctxt
    val (lhs, rhs) = Logic.dest_equals (prop_of th')
    val frees = Term.add_free_names rhs []
    val disjuncts = HOLogic.dest_disj rhs
    val nctxt = Name.make_context frees
    fun mk_introrule t =
      let
        val ((ps, t'), nctxt') = focus_ex t nctxt
        val prems = map HOLogic.mk_Trueprop (HOLogic.dest_conj t')
      in
        (ps, Logic.list_implies (prems, HOLogic.mk_Trueprop lhs))
      end
    val x = ((cterm_of thy) o the_single o snd o strip_comb o HOLogic.dest_Trueprop o fst o
      Logic.dest_implies o prop_of) @{thm exI}
    fun prove_introrule (index, (ps, introrule)) =
      let
        val tac = Simplifier.simp_tac (HOL_basic_ss addsimps [th]) 1
          THEN EVERY1 (select_disj (length disjuncts) (index + 1)) 
          THEN (EVERY (map (fn y =>
            rtac (Drule.cterm_instantiate [(x, cterm_of thy (Free y))] @{thm exI}) 1) ps))
          THEN REPEAT_DETERM (rtac @{thm conjI} 1 THEN atac 1)
          THEN TRY (atac 1)
      in
        Goal.prove ctxt' (map fst ps) [] introrule (fn {...} => tac)
        |> singleton (Variable.export ctxt' ctxt)
      end
  in
    map_index prove_introrule (map mk_introrule disjuncts) 
  end;

val rewrite =
  Simplifier.simplify (HOL_basic_ss addsimps [@{thm Ball_def}, @{thm Bex_def}])
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm all_not_ex}]) 
  #> Conv.fconv_rule nnf_conv 
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm ex_disj_distrib}])
  
fun preprocess (constname, specs) thy =
  let
    val ctxt = ProofContext.init thy
      val intros =
      if forall is_pred_equation specs then 
        maps (introrulify thy o rewrite) specs
      else if forall (is_intro constname) specs then
        specs
      else
        error ("unexpected specification for constant " ^ quote constname ^ ":\n"
          ^ commas (map (quote o Display.string_of_thm_global thy) specs))
    val _ = priority "Defining local predicates and their intro rules..."
    val (intros', (local_defs, thy')) = flatten_intros constname intros thy
    val (intross, thy'') = fold_map preprocess local_defs thy'
  in
    (intros' :: flat intross,thy'')
  end;

fun preprocess_term t thy = error "preprocess_pred_term: to implement" 
  
  
end;
