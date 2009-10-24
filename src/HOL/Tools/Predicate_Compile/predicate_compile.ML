(* Author: Lukas Bulwahn, TU Muenchen

*)
signature PREDICATE_COMPILE =
sig
  val setup : theory -> theory
  val preprocess : string -> theory -> theory
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

(* options *)
val fail_safe_mode = false

open Predicate_Compile_Aux;

val priority = tracing;

(* tuple processing *)

fun expand_tuples thy intro =
  let
    fun rewrite_args [] (pats, intro_t, ctxt) = (pats, intro_t, ctxt)
      | rewrite_args (arg::args) (pats, intro_t, ctxt) = 
      (case HOLogic.strip_tupleT (fastype_of arg) of
        (Ts as _ :: _ :: _) =>
        let
          fun rewrite_arg' (Const ("Pair", _) $ _ $ t2, Type ("*", [_, T2]))
            (args, (pats, intro_t, ctxt)) = rewrite_arg' (t2, T2) (args, (pats, intro_t, ctxt))
            | rewrite_arg' (t, Type ("*", [T1, T2])) (args, (pats, intro_t, ctxt)) =
              let
                val ([x, y], ctxt') = Variable.variant_fixes ["x", "y"] ctxt
                val pat = (t, HOLogic.mk_prod (Free (x, T1), Free (y, T2)))
                  (*val _ = tracing ("Rewriting term " ^
                    (Syntax.string_of_term_global thy (fst pat)) ^ " to " ^
                    (Syntax.string_of_term_global thy (snd pat)) ^ " in " ^
                  (Syntax.string_of_term_global thy intro_t))*)
                val intro_t' = Pattern.rewrite_term thy [pat] [] intro_t
                val args' = map (Pattern.rewrite_term thy [pat] []) args
              in
                rewrite_arg' (Free (y, T2), T2) (args', (pat::pats, intro_t', ctxt'))
              end
            | rewrite_arg' _ (args, (pats, intro_t, ctxt)) = (args, (pats, intro_t, ctxt))
          val (args', (pats, intro_t', ctxt')) = rewrite_arg' (arg, fastype_of arg)
            (args, (pats, intro_t, ctxt))
        in
          rewrite_args args' (pats, intro_t', ctxt')
        end
      | _ => rewrite_args args (pats, intro_t, ctxt))
    fun rewrite_prem atom =
      let
        val (_, args) = strip_comb atom
      in rewrite_args args end
    val ctxt = ProofContext.init thy
    val (((T_insts, t_insts), [intro']), ctxt1) = Variable.import false [intro] ctxt
    val intro_t = prop_of intro'
    val concl = Logic.strip_imp_concl intro_t
    val (p, args) = strip_comb (HOLogic.dest_Trueprop concl)
    val (pats', intro_t', ctxt2) = rewrite_args args ([], intro_t, ctxt1)
    val (pats', intro_t', ctxt3) = 
      fold_atoms rewrite_prem intro_t' (pats', intro_t', ctxt2)
    (*val _ = Output.tracing ("intro_t': " ^ (Syntax.string_of_term_global thy intro_t'))
    val _ = Output.tracing ("pats : " ^ (commas (map
      (fn (t1, t2) => (Syntax.string_of_term_global thy t1) ^ " -> " ^
      Syntax.string_of_term_global thy t2) pats'))*)
    fun rewrite_pat (ct1, ct2) =
      (ct1, cterm_of thy (Pattern.rewrite_term thy pats' [] (term_of ct2)))
    val t_insts' = map rewrite_pat t_insts
      (*val _ = Output.tracing ("t_insts':" ^ (commas (map
      (fn (ct1, ct2) => (Syntax.string_of_term_global thy (term_of ct1) ^ " -> " ^
    Syntax.string_of_term_global thy (term_of ct2))) t_insts')))*)
    val intro'' = Thm.instantiate (T_insts, t_insts') intro
      (*val _ = Output.tracing ("intro'':" ^ (Display.string_of_thm_global thy intro''))*)
    val [intro'''] = Variable.export ctxt3 ctxt [intro'']
    (*val _ = Output.tracing ("intro''':" ^ (Display.string_of_thm_global thy intro'''))*)
  in
    intro'''
  end 

  (* eliminating fst/snd functions *)
val simplify_fst_snd = Simplifier.full_simplify
  (HOL_basic_ss addsimps [@{thm fst_conv}, @{thm snd_conv}, @{thm Pair_eq}])

(* Some last processing *)

fun remove_pointless_clauses intro =
  if Logic.strip_imp_prems (prop_of intro) = [@{prop "False"}] then
    []
  else [intro]

fun print_intross thy msg intross =
  tracing (msg ^ 
    (space_implode "; " (map 
      (fn intros => commas (map (Display.string_of_thm_global thy) intros)) intross)))

fun print_specs thy specs =
  map (fn (c, thms) => "Constant " ^ c ^ " has specification:\n"
    ^ (space_implode "\n" (map (Display.string_of_thm_global thy) thms)) ^ "\n") specs

fun process_specification specs thy' =
  let
  val specs = map (apsnd (map
  (fn th => if is_equationlike th then Pred_Compile_Data.normalize_equation thy' th else th))) specs
    val (intross1, thy'') = apfst flat (fold_map Predicate_Compile_Pred.preprocess specs thy')
    val _ = print_intross thy'' "Flattened introduction rules: " intross1
    val _ = priority "Replacing functions in introrules..."
    val intross2 =
      if fail_safe_mode then
        case try (burrow (maps (Predicate_Compile_Fun.rewrite_intro thy''))) intross1 of
          SOME intross => intross
        | NONE => let val _ = warning "Function replacement failed!" in intross1 end
      else burrow (maps (Predicate_Compile_Fun.rewrite_intro thy'')) intross1
    val _ = print_intross thy'' "Introduction rules with replaced functions: " intross2
    val _ = priority "Introducing new constants for abstractions at higher-order argument positions..."
    val (intross3, (new_defs, thy''')) = Predicate_Compile_Pred.flat_higher_order_arguments (intross2, thy'')
    val _ = tracing ("Now derive introduction rules for new_defs: "
        ^ space_implode "\n" 
        (map (fn (c, ths) => c ^ ": " ^ 
    commas (map (Display.string_of_thm_global thy''') ths)) new_defs))
  val (new_intross, thy'''')  = if not (null new_defs) then
    process_specification new_defs thy'''
    else ([], thy''')
  in
    (intross3 @ new_intross, thy'''')
  end


fun preprocess_strong_conn_constnames gr constnames thy =
  let
    val get_specs = map (fn k => (k, Graph.get_node gr k))
    val _ = priority ("Preprocessing scc of " ^ commas constnames)
    val (prednames, funnames) = List.partition (is_pred thy) constnames
    (* untangle recursion by defining predicates for all functions *)
    val _ = priority "Compiling functions to predicates..."
    val _ = Output.tracing ("funnames: " ^ commas funnames)
    val (fun_pred_specs, thy') =
      if not (null funnames) then Predicate_Compile_Fun.define_predicates
      (get_specs funnames) thy else ([], thy)
    val _ = print_specs thy' fun_pred_specs
    val _ = priority "Compiling predicates to flat introrules..."
    val specs = (get_specs prednames) @ fun_pred_specs
    val (intross3, thy''') = process_specification specs thy'
    val _ = print_intross thy''' "Introduction rules with new constants: " intross3
    val intross4 = map (maps remove_pointless_clauses) intross3
    val _ = print_intross thy''' "After removing pointless clauses: " intross4
    val intross5 = burrow (map (AxClass.overload thy''')) intross4
    val intross6 = burrow (map (simplify_fst_snd o expand_tuples thy''')) intross5
    val _ = print_intross thy''' "introduction rules before registering: " intross6
    val _ = priority "Registering intro rules..."
    val thy'''' = fold Predicate_Compile_Core.register_intros intross6 thy'''
  in
    thy''''
  end;

fun preprocess const thy =
  let
    val _ = Output.tracing ("Fetching definitions from theory...")
    val table = Pred_Compile_Data.make_const_spec_table thy
    val gr = Pred_Compile_Data.obtain_specification_graph thy table const
    val _ = Output.tracing (commas (Graph.all_succs gr [const]))
    val gr = Graph.subgraph (member (op =) (Graph.all_succs gr [const])) gr
  in fold_rev (preprocess_strong_conn_constnames gr)
    (Graph.strong_conn gr) thy
  end

fun code_pred_cmd (((modes, inductify_all), rpred), raw_const) lthy =
  if inductify_all then
    let
      val thy = ProofContext.theory_of lthy
      val const = Code.read_const thy raw_const
      val lthy' = LocalTheory.theory (preprocess const) lthy
        |> LocalTheory.checkpoint
        
      val const = case Predicate_Compile_Fun.pred_of_function (ProofContext.theory_of lthy') const of
          SOME c => c
        | NONE => const
      val _ = tracing "Starting Predicate Compile Core..."
    in Predicate_Compile_Core.code_pred modes rpred const lthy' end
  else
    Predicate_Compile_Core.code_pred_cmd modes rpred raw_const lthy

val setup = Predicate_Compile_Fun.setup_oracle #> Predicate_Compile_Core.setup

val _ = List.app OuterKeyword.keyword ["inductify_all", "rpred", "mode"]

local structure P = OuterParse
in

val opt_modes =
  Scan.optional (P.$$$ "(" |-- P.$$$ "mode" |-- P.$$$ ":" |--
   P.enum1 "," (P.$$$ "[" |-- P.enum "," P.nat --| P.$$$ "]")
  --| P.$$$ ")" >> SOME) NONE

val _ = OuterSyntax.local_theory_to_proof "code_pred"
  "prove equations for predicate specified by intro/elim rules"
  OuterKeyword.thy_goal (opt_modes --
    P.opt_keyword "inductify_all" -- P.opt_keyword "rpred" -- P.term_group >> code_pred_cmd)

end

end
