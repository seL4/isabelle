(*  Title:      HOL/Tools/Function/fundef_datatype.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
A tactic to prove completeness of datatype patterns.
*)

signature FUNDEF_DATATYPE =
sig
    val add_fun : FundefCommon.fundef_config ->
      (binding * typ option * mixfix) list -> (Attrib.binding * term) list ->
      bool -> local_theory -> Proof.context
    val add_fun_cmd : FundefCommon.fundef_config ->
      (binding * string option * mixfix) list -> (Attrib.binding * string) list ->
      bool -> local_theory -> Proof.context

    val setup : theory -> theory
end

structure FundefDatatype : FUNDEF_DATATYPE =
struct

open FundefLib
open FundefCommon


fun check_pats ctxt geq =
    let 
      fun err str = error (cat_lines ["Malformed definition:",
                                      str ^ " not allowed in sequential mode.",
                                      Syntax.string_of_term ctxt geq])
      val thy = ProofContext.theory_of ctxt
                
      fun check_constr_pattern (Bound _) = ()
        | check_constr_pattern t =
          let
            val (hd, args) = strip_comb t
          in
            (((case Datatype.info_of_constr thy (dest_Const hd) of
                 SOME _ => ()
               | NONE => err "Non-constructor pattern")
              handle TERM ("dest_Const", _) => err "Non-constructor patterns");
             map check_constr_pattern args; 
             ())
          end
          
      val (fname, qs, gs, args, rhs) = split_def ctxt geq 
                                       
      val _ = if not (null gs) then err "Conditional equations" else ()
      val _ = map check_constr_pattern args
                  
                  (* just count occurrences to check linearity *)
      val _ = if fold (fold_aterms (fn Bound _ => Integer.add 1 | _ => I)) args 0 > length qs
              then err "Nonlinear patterns" else ()
    in
      ()
    end
    
val by_pat_completeness_auto =
    Proof.global_future_terminal_proof
      (Method.Basic Pat_Completeness.pat_completeness,
       SOME (Method.Source_i (Args.src (("HOL.auto", []), Position.none))))

fun termination_by method int =
    Fundef.termination_proof NONE
    #> Proof.global_future_terminal_proof (Method.Basic method, NONE) int

fun mk_catchall fixes arity_of =
    let
      fun mk_eqn ((fname, fT), _) =
          let 
            val n = arity_of fname
            val (argTs, rT) = chop n (binder_types fT)
                                   |> apsnd (fn Ts => Ts ---> body_type fT) 
                              
            val qs = map Free (Name.invent_list [] "a" n ~~ argTs)
          in
            HOLogic.mk_eq(list_comb (Free (fname, fT), qs),
                          Const ("HOL.undefined", rT))
              |> HOLogic.mk_Trueprop
              |> fold_rev Logic.all qs
          end
    in
      map mk_eqn fixes
    end

fun add_catchall ctxt fixes spec =
  let val fqgars = map (split_def ctxt) spec
      val arity_of = map (fn (fname,_,_,args,_) => (fname, length args)) fqgars
                     |> AList.lookup (op =) #> the
  in
    spec @ mk_catchall fixes arity_of
  end

fun warn_if_redundant ctxt origs tss =
    let
        fun msg t = "Ignoring redundant equation: " ^ quote (Syntax.string_of_term ctxt t)
                    
        val (tss', _) = chop (length origs) tss
        fun check (t, []) = (warning (msg t); [])
          | check (t, s) = s
    in
        (map check (origs ~~ tss'); tss)
    end


fun sequential_preproc (config as FundefConfig {sequential, ...}) ctxt fixes spec =
      if sequential then
        let
          val (bnds, eqss) = split_list spec
                            
          val eqs = map the_single eqss
                    
          val feqs = eqs
                      |> tap (check_defs ctxt fixes) (* Standard checks *)
                      |> tap (map (check_pats ctxt))    (* More checks for sequential mode *)

          val compleqs = add_catchall ctxt fixes feqs   (* Completion *)

          val spliteqs = warn_if_redundant ctxt feqs
                           (FundefSplit.split_all_equations ctxt compleqs)

          fun restore_spec thms =
              bnds ~~ Library.take (length bnds, Library.unflat spliteqs thms)
              
          val spliteqs' = flat (Library.take (length bnds, spliteqs))
          val fnames = map (fst o fst) fixes
          val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) spliteqs'

          fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) (indices ~~ xs)
                                       |> map (map snd)


          val bnds' = bnds @ replicate (length spliteqs - length bnds) Attrib.empty_binding

          (* using theorem names for case name currently disabled *)
          val case_names = map_index (fn (i, (_, es)) => mk_case_names i "" (length es)) 
                                     (bnds' ~~ spliteqs)
                           |> flat
        in
          (flat spliteqs, restore_spec, sort, case_names)
        end
      else
        FundefCommon.empty_preproc check_defs config ctxt fixes spec

val setup =
  Context.theory_map (FundefCommon.set_preproc sequential_preproc)


val fun_config = FundefConfig { sequential=true, default="%x. undefined" (*FIXME dynamic scoping*), 
                                domintros=false, tailrec=false }

fun gen_fun add config fixes statements int lthy =
  let val group = serial_string () in
    lthy
      |> LocalTheory.set_group group
      |> add fixes statements config
      |> by_pat_completeness_auto int
      |> LocalTheory.restore
      |> LocalTheory.set_group group
      |> termination_by (FundefCommon.get_termination_prover lthy) int
  end;

val add_fun = gen_fun Fundef.add_fundef
val add_fun_cmd = gen_fun Fundef.add_fundef_cmd



local structure P = OuterParse and K = OuterKeyword in

val _ =
  OuterSyntax.local_theory' "fun" "define general recursive functions (short version)" K.thy_decl
  (fundef_parser fun_config
     >> (fn ((config, fixes), statements) => add_fun_cmd config fixes statements));

end

end
