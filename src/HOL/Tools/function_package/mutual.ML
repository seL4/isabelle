(*  Title:      HOL/Tools/function_package/mutual.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Tools for mutual recursive definitions.

*)

signature FUNDEF_MUTUAL = 
sig
  
  val prepare_fundef_mutual : thm list -> term list list -> theory ->
                              (FundefCommon.mutual_info * string * (FundefCommon.prep_result * theory))


  val mk_partial_rules_mutual : theory -> thm list -> FundefCommon.mutual_info -> FundefCommon.prep_result -> thm -> thm list ->
                                FundefCommon.fundef_mresult
end


structure FundefMutual: FUNDEF_MUTUAL = 
struct

open FundefCommon



fun check_const (Const C) = C
  | check_const _ = raise ERROR "Head symbol of every left hand side must be a constant." (* FIXME: Output the equation here *)





fun split_def geq =
    let
	val gs = Logic.strip_imp_prems geq
	val eq = Logic.strip_imp_concl geq
	val (f_args, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
	val (fc, args) = strip_comb f_args
	val f = check_const fc
		    
	val qs = fold_rev Term.add_frees args []
		 
	val rhs_new_vars = (Term.add_frees rhs []) \\ qs
	val _ = if null rhs_new_vars then () 
		else raise ERROR "Variables occur on right hand side only: " (* FIXME: Output vars here *)
    in
	((f, length args), (qs, gs, args, rhs))
    end


fun analyze_eqs thy eqss =
    let
	fun all_equal ((x as ((n:string,T), k:int))::xs) = if forall (fn ((n',_),k') => n = n' andalso k = k') xs then x
							   else raise ERROR ("All equations in a block must describe the same "
									     ^ "constant and have the same number of arguments.")
								      
	val def_infoss = map (split_list o map split_def) eqss
	val (consts, qgarss) = split_list (map (fn (Cis, eqs) => (all_equal Cis, eqs)) def_infoss)

	val cnames = map (fst o fst) consts
	val check_rcs = exists_Const (fn (n,_) => if n mem cnames 
						  then raise ERROR "Recursive Calls not allowed in premises." else false)
	val _ = forall (forall (fn (_, gs, _, _) => forall check_rcs gs)) qgarss

	fun curried_types ((_,T), k) =
	    let
		val (caTs, uaTs) = chop k (binder_types T)
	    in 
		(caTs, uaTs ---> body_type T)
	    end

	val (caTss, resultTs) = split_list (map curried_types consts)
	val argTs = map (foldr1 HOLogic.mk_prodT) caTss

	val (RST,streeR, pthsR) = SumTools.mk_tree resultTs
	val (ST, streeA, pthsA) = SumTools.mk_tree argTs

	val def_name = foldr1 (fn (a,b) => a ^ "_" ^ b) (map Sign.base_name cnames)
	val sfun_xname = def_name ^ "_sum"
	val sfun_type = ST --> RST

    	val thy = Sign.add_consts_i [(sfun_xname, sfun_type, NoSyn)] thy (* Add the sum function *)
	val sfun = Const (Sign.full_name thy sfun_xname, sfun_type)

	fun define (((((n, T), _), caTs), (pthA, pthR)), qgars) (thy, rews) = 
	    let 
		val fxname = Sign.base_name n
		val f = Const (n, T)
		val vars = map_index (fn (i,T) => Free ("x" ^ string_of_int i, T)) caTs

		val f_exp = SumTools.mk_proj streeR pthR (sfun $ SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod vars))
		val def = Logic.mk_equals (list_comb (f, vars), f_exp)

		val ([f_def], thy) = PureThy.add_defs_i false [((fxname ^ "_def", def), [])] thy
		val rews' = (f, fold_rev lambda vars f_exp) :: rews
	    in
		(MutualPart {f_name=fxname, const=(n, T),cargTs=caTs,pthA=pthA,pthR=pthR,qgars=qgars,f_def=f_def}, (thy, rews'))
	    end

	val (parts, (thy, rews)) = fold_map define (((consts ~~ caTss)~~ (pthsA ~~ pthsR)) ~~ qgarss) (thy, [])

	fun mk_qglrss (MutualPart {qgars, pthA, pthR, ...}) =
	    let
		fun convert_eqs (qs, gs, args, rhs) =
		    (map Free qs, gs, SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod args), 
		     SumTools.mk_inj streeR pthR (Pattern.rewrite_term thy rews [] rhs))
	    in
		map convert_eqs qgars
	    end
	    
	val qglrss = map mk_qglrss parts
    in
	(Mutual {name=def_name,sum_const=dest_Const sfun, ST=ST, RST=RST, streeA=streeA, streeR=streeR, parts=parts, qglrss=qglrss}, thy)
    end




fun prepare_fundef_mutual congs eqss thy =
    let 
	val (mutual, thy) = analyze_eqs thy eqss
	val Mutual {name, sum_const, qglrss, ...} = mutual
	val global_glrs = flat qglrss
	val used = fold (fn (qs, _, _, _) => fold (curry op ins_string o fst o dest_Free) qs) global_glrs []
    in
	(mutual, name, FundefPrep.prepare_fundef thy congs name (Const sum_const) global_glrs used)
    end


(* Beta-reduce both sides of a meta-equality *)
fun beta_norm_eq thm = 
    let
	val (lhs, rhs) = dest_equals (cprop_of thm)
	val lhs_conv = beta_conversion false lhs 
	val rhs_conv = beta_conversion false rhs 
    in
	transitive (symmetric lhs_conv) (transitive thm rhs_conv)
    end




fun map_mutual2 f (Mutual {parts, ...}) =
    map2 (fn (p as MutualPart {qgars, ...}) => map2 (f p) qgars) parts



fun recover_mutual_psimp thy RST streeR all_f_defs (MutualPart {f_def, pthR, ...}) (_,_,args,_) sum_psimp =
    let
	val conds = cprems_of sum_psimp (* dom-condition and guards *)
	val plain_eq = sum_psimp
                         |> fold (implies_elim_swp o assume) conds

	val x = Free ("x", RST)

	val f_def_inst = instantiate' [] (map (SOME o cterm_of thy) args) (freezeT f_def) (* FIXME: freezeT *)
    in
	reflexive (cterm_of thy (lambda x (SumTools.mk_proj streeR pthR x)))  (*  PR(x) == PR(x) *)
		  |> (fn it => combination it (plain_eq RS eq_reflection))
		  |> beta_norm_eq (*  PR(S(I(as))) == PR(IR(...)) *)
		  |> transitive f_def_inst (*  f ... == PR(IR(...)) *)
		  |> simplify (HOL_basic_ss addsimps [SumTools.projl_inl, SumTools.projr_inr]) (*  f ... == ... *)
		  |> simplify (HOL_basic_ss addsimps all_f_defs) (*  f ... == ... *)
		  |> (fn it => it RS meta_eq_to_obj_eq)
		  |> fold_rev implies_intr conds
    end





fun mutual_induct_Pnames n = 
    if n < 5 then fst (chop n ["P","Q","R","S"])
    else map (fn i => "P" ^ string_of_int i) (1 upto n)
	 
	 
val sum_case_rules = thms "Datatype.sum.cases"
val split_apply = thm "Product_Type.split"
		     
		     
fun mutual_induct_rules thy induct all_f_defs (Mutual {qglrss, RST, parts, streeA, ...}) =
    let
	fun mk_P (MutualPart {cargTs, ...}) Pname =
	    let
		val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
		val atup = foldr1 HOLogic.mk_prod avars
	    in
		tupled_lambda atup (list_comb (Free (Pname, cargTs ---> HOLogic.boolT), avars))
	    end
	    
	val Ps = map2 mk_P parts (mutual_induct_Pnames (length parts))
	val case_exp = SumTools.mk_sumcases streeA HOLogic.boolT Ps
		       
	val induct_inst = 
	    forall_elim (cterm_of thy case_exp) induct
			|> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
		        |> full_simplify (HOL_basic_ss addsimps all_f_defs) 

	fun mk_proj rule (MutualPart {cargTs, pthA, ...}) =
	    let
		val afs = map_index (fn (i,T) => Free ("a" ^ string_of_int i, T)) cargTs
		val inj = SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod afs)
	    in
		rule 
		    |> forall_elim (cterm_of thy inj)
		    |> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
	    end

    in
	map (mk_proj induct_inst) parts
    end
    
    



fun mk_partial_rules_mutual thy congs (m as Mutual {qglrss, RST, parts, streeR, ...}) data complete_thm compat_thms =
    let
	val result = FundefProof.mk_partial_rules thy congs data complete_thm compat_thms 
	val FundefResult {f, G, R, compatibility, completeness, psimps, subset_pinduct,simple_pinduct,total_intro,dom_intros} = result

	val sum_psimps = Library.unflat qglrss psimps

	val all_f_defs = map (fn MutualPart {f_def, ...} => symmetric f_def) parts
	val mpsimps = map_mutual2 (recover_mutual_psimp thy RST streeR all_f_defs) m sum_psimps
	val minducts = mutual_induct_rules thy simple_pinduct all_f_defs m
        val termination = full_simplify (HOL_basic_ss addsimps all_f_defs) total_intro
    in
	FundefMResult { f=f, G=G, R=R,
			psimps=mpsimps, subset_pinducts=[subset_pinduct], simple_pinducts=minducts,
			cases=completeness, termination=termination, domintros=dom_intros}
    end
    

end

























