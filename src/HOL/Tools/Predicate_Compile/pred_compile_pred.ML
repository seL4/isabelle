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
    val tac = fn {...} => setmp quick_and_dirty true (SkipProof.cheat_tac thy')
    val intros'' = map (fn t => Goal.prove ctxt' [] [] t tac) intros'
      |> Variable.export ctxt' ctxt
  in
    (intros'', (local_defs, thy'))
  end

(* TODO: same function occurs in inductive package *)
fun select_disj 1 1 = []
  | select_disj _ 1 = [rtac @{thm disjI1}]
  | select_disj n i = (rtac @{thm disjI2})::(select_disj (n - 1) (i - 1));

fun introrulify thy ths = 
  let
    val ctxt = ProofContext.init thy
    val ((_, ths'), ctxt') = Variable.import true ths ctxt
    fun introrulify' th =
      let
        val (lhs, rhs) = Logic.dest_equals (prop_of th)
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
          end
      in
        map_index prove_introrule (map mk_introrule disjuncts)
      end
  in maps introrulify' ths' |> Variable.export ctxt' ctxt end

val rewrite =
  Simplifier.simplify (HOL_basic_ss addsimps [@{thm Ball_def}, @{thm Bex_def}])
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm all_not_ex}]) 
  #> Conv.fconv_rule nnf_conv 
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm ex_disj_distrib}])

val rewrite_intros =
  Simplifier.simplify (HOL_basic_ss addsimps @{thms HOL.simp_thms(9)})

fun preprocess (constname, specs) thy =
  let
    val ctxt = ProofContext.init thy
      val intros =
      if forall is_pred_equation specs then 
        introrulify thy (map rewrite specs)
      else if forall (is_intro constname) specs then
        map rewrite_intros specs
      else
        error ("unexpected specification for constant " ^ quote constname ^ ":\n"
          ^ commas (map (quote o Display.string_of_thm_global thy) specs))
    val (intros', (local_defs, thy')) = flatten_intros constname intros thy
    val (intross, thy'') = fold_map preprocess local_defs thy'
  in
    (intros' :: flat intross,thy'')
  end;

fun preprocess_term t thy = error "preprocess_pred_term: to implement" 

fun is_Abs (Abs _) = true
  | is_Abs _       = false

fun flat_higher_order_arguments (intross, thy) =
  let
    fun process constname atom (new_defs, thy) =
      let
        val (pred, args) = strip_comb atom
        val abs_args = filter is_Abs args
        fun replace_abs_arg (abs_arg as Abs _ ) (new_defs, thy) =
          let
            val _ = tracing ("Introduce new constant for " ^
              Syntax.string_of_term_global thy abs_arg)
            val vars = map Var (Term.add_vars abs_arg [])
            val abs_arg' = Logic.unvarify abs_arg
            val frees = map Free (Term.add_frees abs_arg' [])
            val constname = Name.variant []
              ((Long_Name.base_name constname) ^ "_hoaux")
            val full_constname = Sign.full_bname thy constname
            val constT = map fastype_of frees ---> (fastype_of abs_arg')
            val const = Const (full_constname, constT)
            val lhs = list_comb (const, frees)
            val def = Logic.mk_equals (lhs, abs_arg')
            val _ = tracing (Syntax.string_of_term_global thy def)
            val ([definition], thy') = thy
              |> Sign.add_consts_i [(Binding.name constname, constT, NoSyn)]
              |> PureThy.add_defs false [((Binding.name (constname ^ "_def"), def), [])]
            
          in
            (list_comb (Logic.varify const, vars), ((full_constname, [definition])::new_defs, thy'))
          end
        | replace_abs_arg arg (new_defs, thy) = (arg, (new_defs, thy))

      val (args', (new_defs', thy')) = fold_map replace_abs_arg args (new_defs, thy)
            (*        val _ = if not (null abs_args) then error "Found some abs argument" else ()*)
      in
        (list_comb (pred, args'), (new_defs', thy'))
      end
    fun flat_intro intro (new_defs, thy) =
      let
        val constname = "dummy"
        val (intro_ts, (new_defs, thy)) = fold_map_atoms (process constname) (prop_of intro) (new_defs, thy)
        val th = setmp quick_and_dirty true (SkipProof.make_thm thy) intro_ts
      in
        (th, (new_defs, thy))
      end
    val (intross', (new_defs, thy')) = fold_map (fold_map flat_intro) intross ([], thy)
  in
    (intross', (new_defs, thy'))
  end

end;
