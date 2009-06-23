(*  Title:      HOL/Tools/Function/fundef_datatype.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
A tactic to prove completeness of datatype patterns.
*)

signature FUNDEF_DATATYPE =
sig
    val pat_completeness_tac: Proof.context -> int -> tactic
    val pat_completeness: Proof.context -> Proof.method
    val prove_completeness : theory -> term list -> term -> term list list -> term list list -> thm

    val setup : theory -> theory

    val add_fun : FundefCommon.fundef_config ->
      (binding * typ option * mixfix) list -> (Attrib.binding * term) list ->
      bool -> local_theory -> Proof.context
    val add_fun_cmd : FundefCommon.fundef_config ->
      (binding * string option * mixfix) list -> (Attrib.binding * string) list ->
      bool -> local_theory -> Proof.context
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
            (((case Datatype.info_of_constr thy (fst (dest_Const hd)) of
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
      val _ = if fold (fold_aterms (fn Bound _ => curry (op +) 1 | _ => I)) args 0 > length qs
              then err "Nonlinear patterns" else ()
    in
      ()
    end
    

fun mk_argvar i T = Free ("_av" ^ (string_of_int i), T)
fun mk_patvar i T = Free ("_pv" ^ (string_of_int i), T)

fun inst_free var inst thm =
    forall_elim inst (forall_intr var thm)


fun inst_case_thm thy x P thm =
    let
        val [Pv, xv] = Term.add_vars (prop_of thm) []
    in
        cterm_instantiate [(cterm_of thy (Var xv), cterm_of thy x), 
                           (cterm_of thy (Var Pv), cterm_of thy P)] thm
    end


fun invent_vars constr i =
    let
        val Ts = binder_types (fastype_of constr)
        val j = i + length Ts
        val is = i upto (j - 1)
        val avs = map2 mk_argvar is Ts
        val pvs = map2 mk_patvar is Ts
    in
        (avs, pvs, j)
    end


fun filter_pats thy cons pvars [] = []
  | filter_pats thy cons pvars (([], thm) :: pts) = raise Match
  | filter_pats thy cons pvars ((pat :: pats, thm) :: pts) =
    case pat of
        Free _ => let val inst = list_comb (cons, pvars)
                 in (inst :: pats, inst_free (cterm_of thy pat) (cterm_of thy inst) thm)
                    :: (filter_pats thy cons pvars pts) end
      | _ => if fst (strip_comb pat) = cons
             then (pat :: pats, thm) :: (filter_pats thy cons pvars pts)
             else filter_pats thy cons pvars pts


fun inst_constrs_of thy (T as Type (name, _)) =
        map (fn (Cn,CT) => Envir.subst_TVars (Sign.typ_match thy (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
            (the (Datatype.get_constrs thy name))
  | inst_constrs_of thy _ = raise Match


fun transform_pat thy avars c_assum ([] , thm) = raise Match
  | transform_pat thy avars c_assum (pat :: pats, thm) =
    let
        val (_, subps) = strip_comb pat
        val eqs = map (cterm_of thy o HOLogic.mk_Trueprop o HOLogic.mk_eq) (avars ~~ subps)
        val a_eqs = map assume eqs
        val c_eq_pat = simplify (HOL_basic_ss addsimps a_eqs) c_assum
    in
        (subps @ pats, fold_rev implies_intr eqs
                                (implies_elim thm c_eq_pat))
    end


exception COMPLETENESS

fun constr_case thy P idx (v :: vs) pats cons =
    let
        val (avars, pvars, newidx) = invent_vars cons idx
        val c_hyp = cterm_of thy (HOLogic.mk_Trueprop (HOLogic.mk_eq (v, list_comb (cons, avars))))
        val c_assum = assume c_hyp
        val newpats = map (transform_pat thy avars c_assum) (filter_pats thy cons pvars pats)
    in
        o_alg thy P newidx (avars @ vs) newpats
              |> implies_intr c_hyp
              |> fold_rev (forall_intr o cterm_of thy) avars
    end
  | constr_case _ _ _ _ _ _ = raise Match
and o_alg thy P idx [] (([], Pthm) :: _)  = Pthm
  | o_alg thy P idx (v :: vs) [] = raise COMPLETENESS
  | o_alg thy P idx (v :: vs) pts =
    if forall (is_Free o hd o fst) pts (* Var case *)
    then o_alg thy P idx vs (map (fn (pv :: pats, thm) =>
                               (pats, refl RS (inst_free (cterm_of thy pv) (cterm_of thy v) thm))) pts)
    else (* Cons case *)
         let
             val T = fastype_of v
             val (tname, _) = dest_Type T
             val {exhaustion=case_thm, ...} = Datatype.the_info thy tname
             val constrs = inst_constrs_of thy T
             val c_cases = map (constr_case thy P idx (v :: vs) pts) constrs
         in
             inst_case_thm thy v P case_thm
                           |> fold (curry op COMP) c_cases
         end
  | o_alg _ _ _ _ _ = raise Match


fun prove_completeness thy xs P qss patss =
    let
        fun mk_assum qs pats = 
            HOLogic.mk_Trueprop P
            |> fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop o HOLogic.mk_eq) (xs ~~ pats)
            |> fold_rev Logic.all qs
            |> cterm_of thy

        val hyps = map2 mk_assum qss patss

        fun inst_hyps hyp qs = fold (forall_elim o cterm_of thy) qs (assume hyp)

        val assums = map2 inst_hyps hyps qss
    in
        o_alg thy P 2 xs (patss ~~ assums)
              |> fold_rev implies_intr hyps
    end



fun pat_completeness_tac ctxt = SUBGOAL (fn (subgoal, i) =>
    let
      val thy = ProofContext.theory_of ctxt
      val (vs, subgf) = dest_all_all subgoal
      val (cases, _ $ thesis) = Logic.strip_horn subgf
          handle Bind => raise COMPLETENESS

      fun pat_of assum =
            let
                val (qs, imp) = dest_all_all assum
                val prems = Logic.strip_imp_prems imp
            in
              (qs, map (HOLogic.dest_eq o HOLogic.dest_Trueprop) prems)
            end

        val (qss, x_pats) = split_list (map pat_of cases)
        val xs = map fst (hd x_pats)
                 handle Empty => raise COMPLETENESS
                 
        val patss = map (map snd) x_pats 

        val complete_thm = prove_completeness thy xs thesis qss patss
             |> fold_rev (forall_intr o cterm_of thy) vs
    in
      PRIMITIVE (fn st => Drule.compose_single(complete_thm, i, st))
    end
    handle COMPLETENESS => no_tac)


fun pat_completeness ctxt = SIMPLE_METHOD' (pat_completeness_tac ctxt)

val by_pat_completeness_auto =
    Proof.global_future_terminal_proof
      (Method.Basic (pat_completeness, Position.none),
       SOME (Method.Source_i (Args.src (("HOL.auto", []), Position.none))))

fun termination_by method int =
    Fundef.termination_proof NONE
    #> Proof.global_future_terminal_proof
      (Method.Basic (method, Position.none), NONE) int

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
        fun check (t, []) = (Output.warning (msg t); [])
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
    Method.setup @{binding pat_completeness} (Scan.succeed pat_completeness)
        "Completeness prover for datatype patterns"
    #> Context.theory_map (FundefCommon.set_preproc sequential_preproc)


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
