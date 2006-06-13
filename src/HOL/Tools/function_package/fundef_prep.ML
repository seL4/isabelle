(*  Title:      HOL/Tools/function_package/fundef_prep.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Preparation step: makes auxiliary definitions and generates
proof obligations.
*)

signature FUNDEF_PREP =
sig
    val prepare_fundef : theory -> thm list -> string -> term -> FundefCommon.glrs -> string list
			 -> FundefCommon.prep_result * theory

end





structure FundefPrep : FUNDEF_PREP =
struct


open FundefCommon
open FundefAbbrev 




fun split_list3 [] = ([],[],[])
  | split_list3 ((x,y,z)::xyzs) = 
    let
	val (xs, ys, zs) = split_list3 xyzs
    in
	(x::xs,y::ys,z::zs)
    end


fun build_tree thy f congs (qs, gs, lhs, rhs) =
    let
	(* FIXME: Save precomputed dependencies in a theory data slot *)
	val congs_deps = map (fn c => (c, FundefCtxTree.cong_deps c)) (congs @ FundefCtxTree.add_congs)
    in
	FundefCtxTree.mk_tree thy congs_deps f rhs
    end


(* maps (qs,gs,lhs,ths) to (qs',gs',lhs',rhs') with primed variables *)
fun mk_primed_vars thy glrs =
    let
	val used = fold (fn (qs,_,_,_) => fold ((insert op =) o fst o dest_Free) qs) glrs []

	fun rename_vars (qs,gs,lhs,rhs) =
	    let
		val qs' = map (fn Free (v,T) => Free (variant used (v ^ "'"),T)) qs
		val rename_vars = Pattern.rewrite_term thy (qs ~~ qs') []
	    in
		(qs', map rename_vars gs, rename_vars lhs, rename_vars rhs)
	    end
    in
	map rename_vars glrs
    end


fun mk_clause_info thy (names:naming_context) (no, (qs,gs,lhs,rhs)) (GI,tree) RIs =
    let
	val Names {domT, G, R, h, f, fvar, used, x, ...} = names
				 
	val zv = Var (("z",0), domT) (* for generating h_assums *)
	val xv = Var (("x",0), domT)
	val rw_RI_to_h_assum = (mk_mem (mk_prod (zv, xv), R),
				mk_mem (mk_prod (zv, h $ zv), G))
	val rw_f_to_h = (f, h)
			
	val cqs = map (cterm_of thy) qs
		  
	val vqs = map free_to_var qs
	val cvqs = map (cterm_of thy) vqs

	val ags = map (assume o cterm_of thy) gs
		  
	val qs' = map (fn Free (v,T) => Free (variant used (v ^ "'"),T)) qs
	val cqs' = map (cterm_of thy) qs'

	val rename_vars = Pattern.rewrite_term thy (qs ~~ qs') []
	val ags' = map (assume o cterm_of thy o rename_vars) gs
	val lhs' = rename_vars lhs
	val rhs' = rename_vars rhs

	val localize = instantiate ([], cvqs ~~ cqs) 
					   #> fold implies_elim_swp ags

	val GI = Thm.freezeT GI
	val lGI = localize GI

	val ordcqs' = map (cterm_of thy o Pattern.rewrite_term thy ((fvar,h)::(qs ~~ qs')) [] o var_to_free) (term_vars (prop_of GI))
			  
	fun mk_call_info (RIvs, RI) =
	    let
		fun mk_var0 (v,T) = Var ((v,0),T)

		val RI = Thm.freezeT RI
		val lRI = localize RI
		val lRIq = fold_rev (forall_intr o cterm_of thy o mk_var0) RIvs lRI
		val plRI = prop_of lRI
		val GmAs = Logic.strip_imp_prems plRI
		val rcarg = case Logic.strip_imp_concl plRI of
				trueprop $ (memb $ (pair $ rcarg $ _) $ R) => rcarg
			      | _ => raise Match
			  
		val Gh_term = Pattern.rewrite_term thy [rw_RI_to_h_assum, rw_f_to_h] [] (prop_of lRIq)
		val Gh = assume (cterm_of thy Gh_term)
		val Gh' = assume (cterm_of thy (rename_vars Gh_term))
	    in
		RCInfo {RI=RI, RIvs=RIvs, lRI=lRI, lRIq=lRIq, Gh=Gh, Gh'=Gh', GmAs=GmAs, rcarg=rcarg}
	    end

	val case_hyp = assume (cterm_of thy (Trueprop (mk_eq (x, lhs))))
    in
	ClauseInfo
	    {
	     no=no,
	     qs=qs, gs=gs, lhs=lhs, rhs=rhs,		 
	     cqs=cqs, cvqs=cvqs, ags=ags,		 
	     cqs'=cqs', ags'=ags', lhs'=lhs', rhs'=rhs', ordcqs' = ordcqs',
	     GI=GI, lGI=lGI, RCs=map mk_call_info RIs,
	     tree=tree, case_hyp = case_hyp
	    }
    end




(* Chooses fresh free names, declares G and R, defines f and returns a record
   with all the information *)  
fun setup_context (f, glrs, used) defname congs thy =
    let
	val trees = map (build_tree thy f congs) glrs
	val allused = fold FundefCtxTree.add_context_varnames trees used

	val Const (f_fullname, fT) = f
	val fname = Sign.base_name f_fullname

	val domT = domain_type fT 
	val ranT = range_type fT

	val h = Free (variant allused "h", domT --> ranT)
	val y = Free (variant allused "y", ranT)
	val x = Free (variant allused "x", domT)
	val z = Free (variant allused "z", domT)
	val a = Free (variant allused "a", domT)
	val D = Free (variant allused "D", HOLogic.mk_setT domT)
	val P = Free (variant allused "P", domT --> boolT)
	val Pbool = Free (variant allused "P", boolT)
	val fvarname = variant allused "f"
	val fvar = Free (fvarname, domT --> ranT)

	val GT = mk_relT (domT, ranT)
	val RT = mk_relT (domT, domT)
	val G_name = defname ^ "_graph"
	val R_name = defname ^ "_rel"

	val glrs' = mk_primed_vars thy glrs

	val thy = Sign.add_consts_i [(G_name, GT, NoSyn), (R_name, RT, NoSyn)] thy

	val G = Const (Sign.full_name thy G_name, GT)
	val R = Const (Sign.full_name thy R_name, RT)
	val acc_R = Const (acc_const_name, (fastype_of R) --> HOLogic.mk_setT domT) $ R

	val f_eq = Logic.mk_equals (f $ x, 
				    Const ("The", (ranT --> boolT) --> ranT) $
					  Abs ("y", ranT, mk_relmemT domT ranT (x, Bound 0) G))

	val ([f_def], thy) = PureThy.add_defs_i false [((fname ^ "_def", f_eq), [])] thy
    in
	(Names {f=f, glrs=glrs, glrs'=glrs', fvar=fvar, fvarname=fvarname, domT=domT, ranT=ranT, G=G, R=R, acc_R=acc_R, h=h, x=x, y=y, z=z, a=a, D=D, P=P, Pbool=Pbool, f_def=f_def, used=allused, trees=trees}, thy)
    end


(* Gs ==> Gs' ==> lhs = lhs' ==> rhs = rhs' *)
fun mk_compat_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
    (implies $ Trueprop (mk_eq (lhs, lhs'))
	     $ Trueprop (mk_eq (rhs, rhs')))
	|> fold_rev (curry Logic.mk_implies) (gs @ gs')


(* all proof obligations *)
fun mk_compat_proof_obligations glrs glrs' =
    map (fn ((x,_), (_,y')) => mk_compat_impl (x,y')) (upairs (glrs ~~ glrs'))


fun extract_Ris thy congs f R tree (qs, gs, lhs, rhs) =
    let
	fun add_Ri2 (fixes,assumes) (_ $ arg) _ (_, x) = ([], (FundefCtxTree.export_term (fixes, map prop_of assumes) (mk_relmem (arg, lhs) R)) :: x)
	  | add_Ri2 _ _ _ _ = raise Match

	val preRis = rev (FundefCtxTree.traverse_tree add_Ri2 tree [])
	val (vRis, preRis_unq) = split_list (map dest_all_all preRis)

	val Ris = map (fold_rev (curry Logic.mk_implies) gs) preRis_unq
    in
	(map (map dest_Free) vRis, preRis, Ris)
    end

fun mk_GIntro thy names (qs, gs, lhs, rhs) Ris =
    let
	val Names { domT, R, G, f, fvar, h, y, Pbool, ... } = names

	val z = Var (("z",0), domT)
	val x = Var (("x",0), domT)

	val rew1 = (mk_mem (mk_prod (z, x), R),
		    mk_mem (mk_prod (z, fvar $ z), G))
	val rew2 = (f, fvar)

	val prems = map (Pattern.rewrite_term thy [rew1, rew2] []) Ris
	val rhs' = Pattern.rewrite_term thy [rew2] [] rhs 
    in
	mk_relmem (lhs, rhs') G
		  |> fold_rev (curry Logic.mk_implies) prems
		  |> fold_rev (curry Logic.mk_implies) gs
    end

fun mk_completeness names glrs =
    let
	val Names {domT, x, Pbool, ...} = names

	fun mk_case (qs, gs, lhs, _) = Trueprop Pbool
						|> curry Logic.mk_implies (Trueprop (mk_eq (x, lhs)))
						|> fold_rev (curry Logic.mk_implies) gs
						|> fold_rev mk_forall qs
    in
	Trueprop Pbool
		 |> fold_rev (curry Logic.mk_implies o mk_case) glrs
    end


fun extract_conditions thy names trees congs =
    let
	val Names {f, R, glrs, glrs', ...} = names

	val (vRiss, preRiss, Riss) = split_list3 (map2 (extract_Ris thy congs f R) trees glrs)
	val Gis = map2 (mk_GIntro thy names) glrs preRiss
	val complete = mk_completeness names glrs
	val compat = mk_compat_proof_obligations glrs glrs'
    in
	{G_intros = Gis, vRiss = vRiss, R_intross = Riss, complete = complete, compat = compat}
    end


fun inductive_def defs (thy, const) =
    let
 	val (thy, {intrs, elims = [elim], ...}) = 
	    InductivePackage.add_inductive_i true (*verbose*)
					     false (*add_consts*)
					     "" (* no altname *)
					     false (* no coind *)
					     false (* elims, please *)
					     false (* induction thm please *)
					     [const] (* the constant *)
					     (map (fn t=>(("", t),[])) defs) (* the intros *)
					     [] (* no special monos *)
					     thy
    in
	(intrs, (thy, elim))
    end



(*
 * This is the first step in a function definition.
 *
 * Defines the function, the graph and the termination relation, synthesizes completeness
 * and comatibility conditions and returns everything.
 *)
fun prepare_fundef thy congs defname f glrs used =
    let
	val (names, thy) = setup_context (f, glrs, used) defname congs thy
	val Names {G, R, glrs, trees, ...} = names

	val {G_intros, vRiss, R_intross, complete, compat} = extract_conditions thy names trees congs

	val (G_intro_thms, (thy, _)) = inductive_def G_intros (thy, G)
	val (R_intro_thmss, (thy, _)) = fold_burrow inductive_def R_intross (thy, R)

	val n = length glrs
	val clauses = map3 (mk_clause_info thy names) ((1 upto n) ~~ glrs) (G_intro_thms ~~ trees) (map2 (curry op ~~) vRiss R_intro_thmss)
    in
	(Prep {names = names, complete=complete, compat=compat, clauses = clauses},
	 thy) 
    end




end
