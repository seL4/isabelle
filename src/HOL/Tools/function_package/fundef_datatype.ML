(*  Title:      HOL/Tools/function_package/fundef_datatype.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
A tactic to prove completeness of datatype patterns.
*)

signature FUNDEF_DATATYPE =
sig
    val pat_complete_tac: int -> tactic

    val pat_completeness : method
    val setup : theory -> theory
end

structure FundefDatatype: FUNDEF_DATATYPE =
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
            (((case DatatypePackage.datatype_of_constr thy (fst (dest_Const hd)) of
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
        val [Pv, xv] = term_vars (prop_of thm)
    in
        cterm_instantiate [(cterm_of thy xv, cterm_of thy x), (cterm_of thy Pv, cterm_of thy P)] thm
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
            (the (DatatypePackage.get_datatype_constrs thy name))
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
             val {exhaustion=case_thm, ...} = DatatypePackage.the_datatype thy tname
             val constrs = inst_constrs_of thy T
             val c_cases = map (constr_case thy P idx (v :: vs) pts) constrs
         in
             inst_case_thm thy v P case_thm
                           |> fold (curry op COMP) c_cases
         end
  | o_alg _ _ _ _ _ = raise Match


fun prove_completeness thy x P qss pats =
    let
        fun mk_assum qs pat = Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (x,pat)),
                                                HOLogic.mk_Trueprop P)
                                               |> fold_rev mk_forall qs
                                               |> cterm_of thy

        val hyps = map2 mk_assum qss pats

        fun inst_hyps hyp qs = fold (forall_elim o cterm_of thy) qs (assume hyp)

        val assums = map2 inst_hyps hyps qss
    in
        o_alg thy P 2 [x] (map2 (pair o single) pats assums)
              |> fold_rev implies_intr hyps
    end



fun pat_complete_tac i thm =
    let
      val thy = theory_of_thm thm

        val subgoal = nth (prems_of thm) (i - 1)   (* FIXME SUBGOAL tactical *)

        val ([P, x], subgf) = dest_all_all subgoal

        val assums = Logic.strip_imp_prems subgf

        fun pat_of assum =
            let
                val (qs, imp) = dest_all_all assum
            in
                case Logic.dest_implies imp of
                    (_ $ (_ $ _ $ pat), _) => (qs, pat)
                  | _ => raise COMPLETENESS
            end

        val (qss, pats) = split_list (map pat_of assums)

        val complete_thm = prove_completeness thy x P qss pats
                                              |> forall_intr (cterm_of thy x)
                                              |> forall_intr (cterm_of thy P)
    in
        Seq.single (Drule.compose_single(complete_thm, i, thm))
    end
    handle COMPLETENESS => Seq.empty


val pat_completeness = Method.SIMPLE_METHOD' pat_complete_tac

val by_pat_completeness_simp =
    Proof.global_terminal_proof
      (Method.Basic (K pat_completeness, Position.none),
       SOME (Method.Source_i (Args.src (("HOL.auto", []), Position.none))))

val termination_by_lexicographic_order =
    FundefPackage.setup_termination_proof NONE
    #> Proof.global_terminal_proof
      (Method.Basic (LexicographicOrder.lexicographic_order [], Position.none), NONE)

fun mk_catchall fixes arities =
    let
      fun mk_eqn ((fname, fT), _) =
          let 
            val n = the (Symtab.lookup arities fname)
            val (argTs, rT) = chop n (binder_types fT)
                                   |> apsnd (fn Ts => Ts ---> body_type fT) 
                              
            val qs = map Free (Name.invent_list [] "a" n ~~ argTs)
          in
            HOLogic.mk_eq(list_comb (Free (fname, fT), qs),
                          Const ("HOL.undefined", rT))
              |> HOLogic.mk_Trueprop
              |> fold_rev mk_forall qs
          end
    in
      map mk_eqn fixes
    end

fun add_catchall ctxt fixes spec =
    let 
      val catchalls = mk_catchall fixes (mk_arities (map (split_def ctxt) (map snd spec)))
    in
      spec @ map (pair true) catchalls
    end

fun warn_if_redundant ctxt origs tss =
    let
        fun msg t = "Ignoring redundant equation: " ^ quote (Syntax.string_of_term ctxt t)
                    
        val (tss', _) = chop (length origs) tss
        fun check ((_, t), []) = (Output.warning (msg t); [])
          | check ((_, t), s) = s
    in
        (map check (origs ~~ tss'); tss)
    end


fun sequential_preproc (config as FundefConfig {sequential, ...}) flags ctxt fixes spec =
    let
      val enabled = sequential orelse exists I flags
    in 
      if enabled then
        let
          val flags' = if sequential then map (K true) flags else flags

          val (nas, eqss) = split_list spec
                            
          val eqs = map the_single eqss
                    
          val feqs = eqs
                           |> tap (check_defs ctxt fixes) (* Standard checks *)
                           |> tap (map (check_pats ctxt))    (* More checks for sequential mode *)
                           |> curry op ~~ flags'

    val compleqs = add_catchall ctxt fixes feqs   (* Completion *)

    val spliteqs = warn_if_redundant ctxt feqs
             (FundefSplit.split_some_equations ctxt compleqs)

          fun restore_spec thms =
              nas ~~ Library.take (length nas, Library.unflat spliteqs thms)
              
          val spliteqs' = flat (Library.take (length nas, spliteqs))
          val fnames = map (fst o fst) fixes
          val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) spliteqs'

          fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) (indices ~~ xs)
                                       |> map (map snd)

        in
          (flat spliteqs, restore_spec, sort)
        end
      else
        FundefCommon.empty_preproc check_defs config flags ctxt fixes spec
    end

val setup =
    Method.add_methods [("pat_completeness", Method.no_args pat_completeness, 
                         "Completeness prover for datatype patterns")]
    #> Context.theory_map (FundefCommon.set_preproc sequential_preproc)


val fun_config = FundefConfig { sequential=true, default="%x. arbitrary", 
                                target=NONE, domintros=false, tailrec=false }


local structure P = OuterParse and K = OuterKeyword in

fun fun_cmd config fixes statements flags lthy =
    lthy
      |> FundefPackage.add_fundef fixes statements config flags
      |> by_pat_completeness_simp
      |> (fn lthy => LocalTheory.reinit lthy (ProofContext.theory_of lthy))
      |> termination_by_lexicographic_order

val _ =
  OuterSyntax.command "fun" "define general recursive functions (short version)" K.thy_decl
  (fundef_parser fun_config
     >> (fn ((config, fixes), (flags, statements)) =>
            (Toplevel.local_theory (target_of config) (fun_cmd config fixes statements flags))));

end

end
