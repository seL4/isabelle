(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Isar commands.

*)

signature FUNDEF_PACKAGE =
sig
    val add_fundef :  (string * string option * mixfix) list
                      -> ((bstring * Attrib.src list) * string) list 
                      -> FundefCommon.fundef_config
                      -> bool list
                      -> local_theory
                      -> Proof.state

    val add_fundef_i:  (string * typ option * mixfix) list
                       -> ((bstring * Attrib.src list) * term) list
                       -> FundefCommon.fundef_config
                       -> bool list
                       -> local_theory
                       -> Proof.state

    val setup_termination_proof : string option -> local_theory -> Proof.state

    val cong_add: attribute
    val cong_del: attribute

    val setup : theory -> theory
    val setup_case_cong_hook : theory -> theory
    val get_congs : theory -> thm list
end


structure FundefPackage : FUNDEF_PACKAGE =
struct

open FundefLib
open FundefCommon

val note_theorem = LocalTheory.note Thm.theoremK

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_" 

fun add_simps fixes post sort label moreatts simps lthy =
    let
      val fnames = map (fst o fst) fixes

      val (saved_spec_simps, lthy) =
        fold_map note_theorem (post simps) lthy
      val saved_simps = flat (map snd saved_spec_simps)

      val simps_by_f = sort saved_simps

      fun add_for_f fname simps =
        note_theorem
          ((NameSpace.qualified fname label, Attrib.internal (K Simplifier.simp_add) :: moreatts),
            simps) #> snd
    in
      (saved_simps,
       fold2 add_for_f fnames simps_by_f lthy)
    end

fun fundef_afterqed config fixes post defname cont sort_cont [[proof]] lthy =
    let
      val FundefResult {fs, R, psimps, trsimps, subset_pinducts, simple_pinducts, termination, domintros, cases, ...} = 
          cont (Goal.close_result proof)

      val qualify = NameSpace.qualified defname
      val addsmps = add_simps fixes post sort_cont

      val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
            |> addsmps "psimps" [] psimps
            ||> fold_option (snd oo addsmps "simps" []) trsimps
            ||>> note_theorem ((qualify "pinduct",
                                [Attrib.internal (K (InductAttrib.induct_set ""))]), simple_pinducts)
            ||>> note_theorem ((qualify "termination", []), [termination])
            ||> (snd o note_theorem ((qualify "cases", []), [cases]))
            ||> fold_option (snd oo curry note_theorem (qualify "domintros", [])) domintros

      val cdata = FundefCtxData { add_simps=addsmps, psimps=psimps',
                                  pinducts=snd pinducts', termination=termination', fs=fs, R=R, defname=defname }
      val cdata' = cdata |> morph_fundef_data (LocalTheory.target_morphism lthy);  (* FIXME !? *)
    in
      lthy 
        |> LocalTheory.declaration (fn phi => add_fundef_data (morph_fundef_data phi cdata)) (* save in target *)
        |> Context.proof_map (add_fundef_data cdata') (* also save in local context *)
    end (* FIXME: Add cases for induct and cases thm *)


fun prepare_spec prep fixspec eqnss lthy = (* FIXME: obsolete when "read_specification" etc. is there *)
    let
      val eqns = map (apsnd single) eqnss

      val ((fixes, _), ctxt') = prep fixspec [] lthy             
      fun prep_eqn e = the_single (snd (fst (prep [] [e] ctxt')))

      val spec = map prep_eqn eqns
                 |> map (apsnd (map (fn t => fold_rev (mk_forall o Free) (frees_in_term ctxt' t) t))) (* Add quantifiers *)
    in
      ((fixes, spec), ctxt')
    end

fun gen_add_fundef prep fixspec eqnss config flags lthy =
    let
      val ((fixes, spec), ctxt') = prepare_spec prep fixspec eqnss lthy
      val (eqs, post) = FundefCommon.get_preproc lthy config flags ctxt' fixes spec

      val defname = mk_defname fixes

      val ((goalstate, cont, sort_cont), lthy) =
          FundefMutual.prepare_fundef_mutual config defname fixes eqs lthy

      val afterqed = fundef_afterqed config fixes post defname cont sort_cont
    in
      lthy
        |> Proof.theorem_i NONE afterqed [[(Logic.unprotect (concl_of goalstate), [])]]
        |> Proof.refine (Method.primitive_text (fn _ => goalstate)) |> Seq.hd
    end

fun total_termination_afterqed data [[totality]] lthy =
    let
      val FundefCtxData { add_simps, psimps, pinducts, defname, ... } = data

      val totality = Goal.close_result totality

      val remove_domain_condition = full_simplify (HOL_basic_ss addsimps [totality, True_implies_equals])

      val tsimps = map remove_domain_condition psimps
      val tinduct = map remove_domain_condition pinducts

      val has_guards = exists ((fn (Const ("Trueprop", _) $ _) => false | _ => true) o prop_of) tsimps
      val allatts = if has_guards then [] else [Attrib.internal (K (RecfunCodegen.add NONE))]

      val qualify = NameSpace.qualified defname;
    in
      lthy
        |> add_simps "simps" allatts tsimps |> snd
        |> note_theorem ((qualify "induct", []), tinduct) |> snd
    end


fun setup_termination_proof term_opt lthy =
    let
      val data = the (case term_opt of
                        SOME t => import_fundef_data (ProofContext.read_term lthy t) (Context.Proof lthy)
                      | NONE => import_last_fundef (Context.Proof lthy))
          handle Option.Option => raise ERROR ("Not a function: " ^ quote (the_default "" term_opt))

        val FundefCtxData {termination, R, ...} = data
        val domT = domain_type (fastype_of R)
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
    in
      lthy
        |> ProofContext.note_thmss_i "" [(("", [ContextRules.rule_del]), [([allI], [])])] |> snd
        |> ProofContext.note_thmss_i "" [(("", [ContextRules.intro_bang (SOME 1)]), [([allI], [])])] |> snd
        |> ProofContext.note_thmss_i ""
          [(("termination", [ContextRules.intro_bang (SOME 0)]),
            [([Goal.norm_result termination], [])])] |> snd
        |> Proof.theorem_i NONE (total_termination_afterqed data) [[(goal, [])]]
    end


val add_fundef = gen_add_fundef Specification.read_specification
val add_fundef_i = gen_add_fundef Specification.cert_specification



(* congruence rules *)

val cong_add = Thm.declaration_attribute (map_fundef_congs o Drule.add_rule o safe_mk_meta_eq);
val cong_del = Thm.declaration_attribute (map_fundef_congs o Drule.del_rule o safe_mk_meta_eq);

(* Datatype hook to declare datatype congs as "fundef_congs" *)


fun add_case_cong n thy =
    Context.theory_map (map_fundef_congs (Drule.add_rule
                          (DatatypePackage.get_datatype thy n |> the
                           |> #case_cong
                           |> safe_mk_meta_eq)))
                       thy

val case_cong_hook = fold add_case_cong

val setup_case_cong_hook =
    DatatypeHooks.add case_cong_hook
    #> (fn thy => case_cong_hook (Symtab.keys (DatatypePackage.get_datatypes thy)) thy)

(* ad-hoc method to convert elimination-style goals to existential statements *)

fun insert_int_goal thy subg st =
    let
      val goal = hd (prems_of st)
      val (ps, imp) = dest_all_all goal
      val cps = map (cterm_of thy) ps

      val imp_subg = fold (fn p => fn t => betapply (t,p)) ps subg
      val new_subg = implies $ imp_subg $ imp
                      |> fold_rev mk_forall ps
                      |> cterm_of thy 
                      |> assume 

      val sg2 = imp_subg
                 |> fold_rev mk_forall ps
                 |> cterm_of thy 
                 |> assume

      val t' = new_subg
                |> fold forall_elim cps
                |> flip implies_elim (fold forall_elim cps sg2)
                |> fold_rev forall_intr cps

      val st' = implies_elim st t'
                 |> implies_intr (cprop_of sg2)
                 |> implies_intr (cprop_of new_subg)
    in
      Seq.single st'
    end

fun mk_cases_statement thy t =
    let
      fun mk_clause t = 
          let 
            val (qs, imp) = dest_all_all t
          in 
            Logic.strip_imp_prems imp
             |> map (ObjectLogic.atomize_term thy)
             |> foldr1 HOLogic.mk_conj
             |> fold_rev (fn Free (v,T) => fn t => HOLogic.mk_exists (v,T,t)) qs
          end

      val (ps, imp) = dest_all_all t
    in 
      Logic.strip_imp_prems imp
       |> map mk_clause
       |> foldr1 HOLogic.mk_disj
       |> HOLogic.mk_Trueprop
       |> fold_rev lambda ps
    end

fun elim_to_cases1 ctxt st =
    let
      val thy = theory_of_thm st
      val [subg] = prems_of st
      val cex = mk_cases_statement thy subg
    in
      (insert_int_goal thy cex
       THEN REPEAT_ALL_NEW (Tactic.ematch_tac [disjE, exE, conjE]) 1
       THEN REPEAT (Goal.assume_rule_tac ctxt 1)
    (*   THEN REPEAT (etac thin_rl 1)*)) st
    end

fun elim_to_cases_tac ctxt = SELECT_GOAL (elim_to_cases1 ctxt)

val elim_to_cases_setup = Method.add_methods
  [("elim_to_cases", Method.ctxt_args (Method.SIMPLE_METHOD' o elim_to_cases_tac),
    "convert elimination-style goal to a disjunction of existentials")]

(* setup *)

val setup =
  Attrib.add_attributes
    [("fundef_cong", Attrib.add_del_args cong_add cong_del,
      "declaration of congruence rule for function definitions")]
  #> setup_case_cong_hook
  #> FundefRelation.setup
  #> elim_to_cases_setup

val get_congs = FundefCommon.get_fundef_congs o Context.Theory



(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
  (fundef_parser default_config
     >> (fn ((config, fixes), (flags, statements)) =>
            Toplevel.local_theory_to_proof (target_of config) (add_fundef fixes statements config flags)
            #> Toplevel.print));

val terminationP =
  OuterSyntax.command "termination" "prove termination of a recursive function" K.thy_goal
  (P.opt_target -- Scan.option P.term
    >> (fn (target, name) =>
           Toplevel.print o
           Toplevel.local_theory_to_proof target (setup_termination_proof name)));

val _ = OuterSyntax.add_parsers [functionP];
val _ = OuterSyntax.add_parsers [terminationP];
val _ = OuterSyntax.add_keywords ["sequential", "otherwise"];

end;


end
