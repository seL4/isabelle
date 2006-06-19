(*  Title:      HOL/Tools/function_package/fundef_datatype.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
A tactic to prove completeness of datatype patterns.
*)

signature FUNDEF_DATATYPE = 
sig
    val pat_complete_tac: int -> tactic

    val setup : theory -> theory
end



structure FundefDatatype : FUNDEF_DATATYPE =
struct


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
	map (fn (Cn,CT) => Envir.subst_TVars (Type.typ_match (Sign.tsig_of thy) (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
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

	val subgoal = nth (prems_of thm) (i - 1)

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



val setup = 
    Method.add_methods [("pat_completeness", Method.no_args (Method.SIMPLE_METHOD (pat_complete_tac 1)), "Completeness prover for datatype patterns")]

end