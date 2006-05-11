(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Isar commands.

*)

signature FUNDEF_PACKAGE = 
sig
    val add_fundef : ((bstring * Attrib.src list) * string) list -> theory -> Proof.state (* Need an _i variant *)

    val cong_add: attribute
    val cong_del: attribute
							 
    val setup : theory -> theory
end


structure FundefPackage : FUNDEF_PACKAGE =
struct

open FundefCommon

val True_implies = thm "True_implies"


fun fundef_afterqed congs curry_info name data names atts thmss thy =
    let
	val (complete_thm :: compat_thms) = map hd thmss
	val fundef_data = FundefProof.mk_partial_rules_curried thy congs curry_info data (freezeT complete_thm) (map freezeT compat_thms)
	val FundefResult {psimps, subset_pinduct, simple_pinduct, total_intro, dom_intros, ...} = fundef_data


	val Prep {names = Names {acc_R=accR, ...}, ...} = data
	val dom_abbrev = Logic.mk_equals (Free (name ^ "_dom", fastype_of accR), accR)
	val (_, thy) = LocalTheory.mapping NONE (Specification.abbreviation_i ("", false) [(NONE, dom_abbrev)]) thy

	val thy = thy |> Theory.add_path name 

	val thy = thy |> Theory.add_path "psimps"
	val (_, thy) = PureThy.add_thms ((names ~~ psimps) ~~ atts) thy;
	val thy = thy |> Theory.parent_path

	val (_, thy) = PureThy.add_thms [(("cases", complete_thm), [RuleCases.case_names names])] thy
	val (_, thy) = PureThy.add_thmss [(("domintros", dom_intros), [])] thy
	val (_, thy) = PureThy.add_thms [(("termination", total_intro), [])] thy
	val (_,thy) = PureThy.add_thms [(("pinduct", simple_pinduct), [RuleCases.case_names names, InductAttrib.induct_set ""])] thy
	val (_, thy) = PureThy.add_thmss [(("psimps", psimps), [Simplifier.simp_add])] thy
	val thy = thy |> Theory.parent_path
    in
	add_fundef_data name fundef_data thy
    end

fun gen_add_fundef prep_att eqns_atts thy =
    let
	val (natts, eqns) = split_list eqns_atts
	val (names, raw_atts) = split_list natts

	val atts = map (map (prep_att thy)) raw_atts

	val congs = get_fundef_congs (Context.Theory thy)

	val t_eqns = map (Sign.read_prop thy) eqns
			 |> map (term_of o cterm_of thy) (* HACK to prevent strange things from happening with abbreviations *)

	val (curry_info, name, (data, thy)) = FundefPrep.prepare_fundef_curried congs t_eqns thy
	val Prep {complete, compat, ...} = data

	val props = (complete :: compat) (*(complete :: fst (chop 110 compat))*)
    in
	thy |> ProofContext.init
	    |> Proof.theorem_i PureThy.internalK NONE (fundef_afterqed congs curry_info name data names atts) NONE ("", [])
	    (map (fn t => (("", []), [(t, [])])) props)
    end


fun total_termination_afterqed name thmss thy =
    let
	val totality = hd (hd thmss)

	val FundefResult {psimps, simple_pinduct, ... }
	  = the (get_fundef_data name thy)

	val remove_domain_condition = full_simplify (HOL_basic_ss addsimps [totality, True_implies])

	val tsimps = map remove_domain_condition psimps
	val tinduct = remove_domain_condition simple_pinduct

	val thy = Theory.add_path name thy
		  
		  (* Need the names and attributes. Apply the attributes again? *)
(*	val thy = thy |> Theory.add_path "simps"
	val (_, thy) = PureThy.add_thms ((names ~~ tsimps) ~~ atts) thy;
	val thy = thy |> Theory.parent_path*)

	val (_, thy) = PureThy.add_thms [(("induct", tinduct), [])] thy 
	val (_, thy) = PureThy.add_thmss [(("simps", tsimps), [Simplifier.simp_add, RecfunCodegen.add NONE])] thy
	val thy = Theory.parent_path thy
    in
	thy
    end

(*
fun mk_partial_rules name D_name D domT idomT thmss thy =
    let
	val [subs, dcl] = (hd thmss)

	val {f_const, f_curried_const, G_const, R_const, G_elims, completeness, f_simps, names_attrs, subset_induct, ... }
	  = the (Symtab.lookup (FundefData.get thy) name)

	val D_implies_dom = subs COMP (instantiate' [SOME (ctyp_of thy idomT)] 
						    [SOME (cterm_of thy D)]
						    subsetD)

	val D_simps = map (curry op RS D_implies_dom) f_simps

	val D_induct = subset_induct
			   |> cterm_instantiate [(cterm_of thy (Var (("D",0), fastype_of D)) ,cterm_of thy D)]
			   |> curry op COMP subs
			   |> curry op COMP (dcl |> forall_intr (cterm_of thy (Var (("z",0), idomT)))
						 |> forall_intr (cterm_of thy (Var (("x",0), idomT))))

	val ([tinduct'], thy2) = PureThy.add_thms [((name ^ "_" ^ D_name ^ "_induct", D_induct), [])] thy
	val ([tsimps'], thy3) = PureThy.add_thmss [((name ^ "_" ^ D_name ^ "_simps", D_simps), [])] thy2
    in
	thy3
    end
*)
 

fun fundef_setup_termination_proof name NONE thy = 
    let
	val name = if name = "" then get_last_fundef thy else name
	val data = the (get_fundef_data name thy)

	val FundefResult {total_intro, ...} = data
	val goal = FundefTermination.mk_total_termination_goal data
    in
	thy |> ProofContext.init
	    |> ProofContext.note_thmss_i [(("termination_intro", 
					    [ContextRules.intro_query NONE]), [([total_intro], [])])] |> snd
	    |> Proof.theorem_i PureThy.internalK NONE (total_termination_afterqed name) NONE ("", [])
	    [(("", []), [(goal, [])])]
    end	
  | fundef_setup_termination_proof name (SOME (dom_name, dom)) thy =
    let
	val name = if name = "" then get_last_fundef thy else name
	val data = the (get_fundef_data name thy)
	val (subs, dcl) = FundefTermination.mk_partial_termination_goal thy data dom
    in
	thy |> ProofContext.init
	    |> Proof.theorem_i PureThy.internalK NONE (K I) NONE ("", [])
	    [(("", []), [(subs, []), (dcl, [])])]
    end	


val add_fundef = gen_add_fundef Attrib.attribute



(* congruence rules *)

val cong_add = Thm.declaration_attribute (map_fundef_congs o Drule.add_rule o safe_mk_meta_eq);
val cong_del = Thm.declaration_attribute (map_fundef_congs o Drule.del_rule o safe_mk_meta_eq);


(* setup *)

val setup = FundefData.init #> FundefCongs.init 
	#>  Attrib.add_attributes
		[("fundef_cong", Attrib.add_del_args cong_add cong_del, "declaration of congruence rule for function definitions")]


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val function_decl =
    Scan.repeat1 (P.opt_thm_name ":" -- P.prop);

val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
    (function_decl >> (fn eqns =>
      Toplevel.print o Toplevel.theory_to_proof (add_fundef eqns)));

val terminationP =
  OuterSyntax.command "termination" "prove termination of a recursive function" K.thy_goal
  ((Scan.optional P.name "" -- Scan.option (P.$$$ "(" |-- Scan.optional (P.name --| P.$$$ ":") "dom" -- P.term --| P.$$$ ")"))
       >> (fn (name,dom) =>
	      Toplevel.print o Toplevel.theory_to_proof (fundef_setup_termination_proof name dom)));

val _ = OuterSyntax.add_parsers [functionP];
val _ = OuterSyntax.add_parsers [terminationP];


end;


end
