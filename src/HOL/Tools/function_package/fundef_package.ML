(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Isar commands.

*)

signature FUNDEF_PACKAGE = 
sig
    val add_fundef : ((bstring * Attrib.src list) * string) list list -> theory -> Proof.state (* Need an _i variant *)

    val cong_add: attribute
    val cong_del: attribute
							 
    val setup : theory -> theory
    val get_congs : theory -> thm list
end


structure FundefPackage : FUNDEF_PACKAGE =
struct

open FundefCommon

val True_implies = thm "True_implies"


fun add_simps label moreatts (MutualPart {f_name, ...}, psimps) (names, attss) thy =
    let 
      val thy = thy |> Theory.add_path f_name 
                
      val thy = thy |> Theory.add_path label
      val spsimps = map standard psimps
      val add_list = (names ~~ spsimps) ~~ attss
      val (_, thy) = PureThy.add_thms add_list thy
      val thy = thy |> Theory.parent_path
                
      val (_, thy) = PureThy.add_thmss [((label, spsimps), Simplifier.simp_add :: moreatts)] thy
      val thy = thy |> Theory.parent_path
    in
      thy
    end
    





fun fundef_afterqed congs mutual_info name data names atts [[result]] thy =
    let
	val fundef_data = FundefMutual.mk_partial_rules_mutual thy mutual_info data result
	val FundefMResult {psimps, subset_pinducts, simple_pinducts, termination, domintros, cases, ...} = fundef_data
        val Mutual {parts, ...} = mutual_info

	val Prep {names = Names {acc_R=accR, ...}, ...} = data
	val dom_abbrev = Logic.mk_equals (Free (name ^ "_dom", fastype_of accR), accR)
	val (_, thy) = LocalTheory.mapping NONE (Specification.abbreviation_i ("", false) [(NONE, dom_abbrev)]) thy

        val thy = fold2 (add_simps "psimps" []) (parts ~~ psimps) (names ~~ atts) thy

	val thy = thy |> Theory.add_path name
	val (_, thy) = PureThy.add_thms [(("cases", cases), [RuleCases.case_names (flat names)])] thy
	val (_, thy) = PureThy.add_thmss [(("domintros", domintros), [])] thy
	val (_, thy) = PureThy.add_thms [(("termination", standard termination), [])] thy
	val (_,thy) = PureThy.add_thmss [(("pinduct", map standard simple_pinducts), [RuleCases.case_names (flat names), InductAttrib.induct_set ""])] thy
	val thy = thy |> Theory.parent_path
    in
	add_fundef_data name (fundef_data, mutual_info, names, atts) thy
    end

fun gen_add_fundef prep_att eqns_attss thy =
    let
	fun split eqns_atts =
	    let 
		val (natts, eqns) = split_list eqns_atts
		val (names, raw_atts) = split_list natts
		val atts = map (map (prep_att thy)) raw_atts
	    in
		((names, atts), eqns)
	    end


	val (natts, eqns) = split_list (map split_list eqns_attss)
	val (names, raw_atts) = split_list (map split_list natts)

	val atts = map (map (map (prep_att thy))) raw_atts

	val congs = get_fundef_congs (Context.Theory thy)

	val t_eqns = map (map (Sign.read_prop thy)) eqns

	val (mutual_info, name, (data, thy)) = FundefMutual.prepare_fundef_mutual congs t_eqns thy
	val Prep {goal, goalI, ...} = data
    in
	thy |> ProofContext.init
	    |> Proof.theorem_i PureThy.internalK NONE (fundef_afterqed congs mutual_info name data names atts) NONE ("", [])
	    [(("", []), [(goal, [])])]
            |> Proof.refine (Method.primitive_text (fn _ => goalI))
            |> Seq.hd
    end


fun total_termination_afterqed name (Mutual {parts, ...}) thmss thy =
    let
	val totality = hd (hd thmss)

	val (FundefMResult {psimps, simple_pinducts, ... }, Mutual {parts, ...}, names, atts)
	  = the (get_fundef_data name thy)

	val remove_domain_condition = full_simplify (HOL_basic_ss addsimps [totality, True_implies])

	val tsimps = map (map remove_domain_condition) psimps
	val tinduct = map remove_domain_condition simple_pinducts

        val has_guards = exists ((fn (Const ("Trueprop", _) $ _) => false | _ => true) o prop_of) (flat tsimps)
        val allatts = if has_guards then [] else [RecfunCodegen.add NONE]

        val thy = fold2 (add_simps "simps" allatts) (parts ~~ tsimps) (names ~~ atts) thy

	val thy = Theory.add_path name thy
		  
	val (_, thy) = PureThy.add_thmss [(("induct", map standard tinduct), [])] thy 
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
                   handle Option.Option => raise ERROR ("No such function definition: " ^ name)

	val (res as FundefMResult {termination, ...}, mutual, _, _) = data
	val goal = FundefTermination.mk_total_termination_goal data
    in
	thy |> ProofContext.init
	    |> ProofContext.note_thmss_i [(("termination", 
					    [ContextRules.intro_query NONE]), [([standard termination], [])])] |> snd
	    |> Proof.theorem_i PureThy.internalK NONE (total_termination_afterqed name mutual) NONE ("", [])
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


val get_congs = FundefCommon.get_fundef_congs o Context.Theory


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val function_decl =
    Scan.repeat1 (P.opt_thm_name ":" -- P.prop);

val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
    (P.and_list1 function_decl >> (fn eqnss =>
      Toplevel.print o Toplevel.theory_to_proof (add_fundef eqnss)));

val terminationP =
  OuterSyntax.command "termination" "prove termination of a recursive function" K.thy_goal
  ((Scan.optional P.name "" -- Scan.option (P.$$$ "(" |-- Scan.optional (P.name --| P.$$$ ":") "dom" -- P.term --| P.$$$ ")"))
       >> (fn (name,dom) =>
	      Toplevel.print o Toplevel.theory_to_proof (fundef_setup_termination_proof name dom)));

val _ = OuterSyntax.add_parsers [functionP];
val _ = OuterSyntax.add_parsers [terminationP];


end;


end
