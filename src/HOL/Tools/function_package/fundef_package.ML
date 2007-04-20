(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Isar commands.

*)

signature FUNDEF_PACKAGE =
sig
    val add_fundef :  (string * string option * mixfix) list
                      -> ((bstring * Attrib.src list) * (string * bool)) list 
                      -> FundefCommon.fundef_config
                      -> local_theory
                      -> Proof.state

    val add_fundef_i:  (string * typ option * mixfix) list
                       -> ((bstring * Attrib.src list) * (term * bool)) list
                       -> FundefCommon.fundef_config
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

fun burrow_snd f ps = (* ('a list -> 'b list) -> ('c * 'a) list -> ('c * 'b) list *)
    let val (xs, ys) = split_list ps
    in xs ~~ f ys end

fun restore_spec_structure reps spec =
    (burrow_snd o burrow o K) reps spec

fun add_simps fixes spec sort label moreatts simps lthy =
    let
      val fnames = map (fst o fst) fixes

      val (saved_spec_simps, lthy) =
        fold_map note_theorem (restore_spec_structure simps spec) lthy
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

fun fundef_afterqed config fixes spec defname cont sort_cont [[proof]] lthy =
    let
      val FundefResult {fs, R, psimps, trsimps, subset_pinducts, simple_pinducts, termination, domintros, cases, ...} = 
          cont (Goal.close_result proof)

      val qualify = NameSpace.qualified defname
      val addsmps = add_simps fixes spec sort_cont

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



fun prep_with_flags prep fixspec eqnss_flags global_flag lthy =
    let
      val flags = map (fn x => global_flag orelse (snd (snd x))) eqnss_flags
      val eqns = map (apsnd (single o fst)) eqnss_flags

      val ((fixes, _), ctxt') = prep fixspec [] lthy

      fun prep_eqn e = the_single (snd (fst (prep [] [e] ctxt')))
                         |> apsnd the_single

      val spec = map prep_eqn eqns
                     |> map (apsnd (fn t => fold_rev (mk_forall o Free) (frees_in_term ctxt' t) t)) (* Add quantifiers *)
                     |> burrow_snd (fn ts => FundefSplit.split_some_equations ctxt' (flags ~~ ts))
    in
      ((fixes, spec), ctxt')
    end

fun gen_add_fundef prep_spec fixspec eqnss_flags config lthy =
    let
      val FundefConfig {sequential, default, tailrec, ...} = config

      val ((fixes, spec), ctxt') = prep_with_flags prep_spec fixspec eqnss_flags sequential lthy

      val defname = mk_defname fixes

      val t_eqns = spec |> map snd |> flat (* flatten external structure *)

      val ((goalstate, cont, sort_cont), lthy) =
          FundefMutual.prepare_fundef_mutual config defname fixes t_eqns default lthy

      val afterqed = fundef_afterqed config fixes spec defname cont sort_cont
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

        (* FIXME: How to generate code from (possibly) local contexts*)
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

(* setup *)

val setup =
    FundefData.init
      #> FundefCongs.init
      #> TerminationRule.init
      #>  Attrib.add_attributes
            [("fundef_cong", Attrib.add_del_args cong_add cong_del, "declaration of congruence rule for function definitions")]
      #> setup_case_cong_hook
      #> FundefRelation.setup

val get_congs = FundefCommon.get_fundef_congs o Context.Theory



(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
  (fundef_parser default_config
     >> (fn ((config, fixes), statements) =>
            Toplevel.local_theory_to_proof (target_of config) (add_fundef fixes statements config)
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
