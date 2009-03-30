(*  Title:      HOL/Tools/function_package/fundef_package.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Isar commands.
*)

signature FUNDEF_PACKAGE =
sig
    val add_fundef :  (binding * typ option * mixfix) list
                       -> (Attrib.binding * term) list
                       -> FundefCommon.fundef_config
                       -> local_theory
                       -> Proof.state
    val add_fundef_cmd :  (binding * string option * mixfix) list
                      -> (Attrib.binding * string) list
                      -> FundefCommon.fundef_config
                      -> local_theory
                      -> Proof.state

    val termination_proof : term option -> local_theory -> Proof.state
    val termination_proof_cmd : string option -> local_theory -> Proof.state
    val termination : term option -> local_theory -> Proof.state
    val termination_cmd : string option -> local_theory -> Proof.state

    val setup : theory -> theory
    val get_congs : Proof.context -> thm list
end


structure FundefPackage : FUNDEF_PACKAGE =
struct

open FundefLib
open FundefCommon

val simp_attribs = map (Attrib.internal o K)
    [Simplifier.simp_add,
     Code.add_default_eqn_attribute,
     Nitpick_Const_Simp_Thms.add]

val psimp_attribs = map (Attrib.internal o K)
    [Simplifier.simp_add,
     Nitpick_Const_Psimp_Thms.add]

fun note_theorem ((name, atts), ths) =
  LocalTheory.note Thm.theoremK ((Binding.qualified_name name, atts), ths)

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_"

fun add_simps fnames post sort extra_qualify label moreatts simps lthy =
    let
      val spec = post simps
                   |> map (apfst (apsnd (fn ats => moreatts @ ats)))
                   |> map (apfst (apfst extra_qualify))

      val (saved_spec_simps, lthy) =
        fold_map (LocalTheory.note Thm.theoremK) spec lthy

      val saved_simps = flat (map snd saved_spec_simps)
      val simps_by_f = sort saved_simps

      fun add_for_f fname simps =
        note_theorem ((Long_Name.qualify fname label, []), simps) #> snd
    in
      (saved_simps,
       fold2 add_for_f fnames simps_by_f lthy)
    end

fun fundef_afterqed do_print fixes post defname cont sort_cont cnames [[proof]] lthy =
    let
      val FundefResult {fs, R, psimps, trsimps,  simple_pinducts, termination, domintros, cases, ...} = 
          cont (Thm.close_derivation proof)

      val fnames = map (fst o fst) fixes
      val qualify = Long_Name.qualify defname
      val addsmps = add_simps fnames post sort_cont

      val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
            |> addsmps (Binding.qualify false "partial") "psimps"
                 psimp_attribs psimps
            ||> fold_option (snd oo addsmps I "simps" simp_attribs) trsimps
            ||>> note_theorem ((qualify "pinduct",
                   [Attrib.internal (K (RuleCases.case_names cnames)),
                    Attrib.internal (K (RuleCases.consumes 1)),
                    Attrib.internal (K (Induct.induct_pred ""))]), simple_pinducts)
            ||>> note_theorem ((qualify "termination", []), [termination])
            ||> (snd o note_theorem ((qualify "cases",
                   [Attrib.internal (K (RuleCases.case_names cnames))]), [cases]))
            ||> fold_option (snd oo curry note_theorem (qualify "domintros", [])) domintros

      val cdata = FundefCtxData { add_simps=addsmps, case_names=cnames, psimps=psimps',
                                  pinducts=snd pinducts', termination=termination', fs=fs, R=R, defname=defname }
      val _ =
        if not do_print then ()
        else Specification.print_consts lthy (K false) (map fst fixes)
    in
      lthy
        |> LocalTheory.declaration (add_fundef_data o morph_fundef_data cdata)
    end


fun gen_add_fundef is_external prep default_constraint fixspec eqns config lthy =
    let
      val constrn_fxs = map (fn (b, T, mx) => (b, SOME (the_default default_constraint T), mx))
      val ((fixes0, spec0), ctxt') = prep (constrn_fxs fixspec) eqns lthy
      val fixes = map (apfst (apfst Binding.name_of)) fixes0;
      val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0;
      val (eqs, post, sort_cont, cnames) = FundefCommon.get_preproc lthy config ctxt' fixes spec

      val defname = mk_defname fixes

      val ((goalstate, cont), lthy) =
          FundefMutual.prepare_fundef_mutual config defname fixes eqs lthy

      val afterqed = fundef_afterqed is_external fixes post defname cont sort_cont cnames
    in
      lthy
        |> is_external ? LocalTheory.set_group (serial_string ())
        |> Proof.theorem_i NONE afterqed [[(Logic.unprotect (concl_of goalstate), [])]]
        |> Proof.refine (Method.primitive_text (fn _ => goalstate)) |> Seq.hd
    end

val add_fundef = gen_add_fundef false Specification.check_spec (TypeInfer.anyT HOLogic.typeS)
val add_fundef_cmd = gen_add_fundef true Specification.read_spec "_::type"


fun total_termination_afterqed data [[totality]] lthy =
    let
      val FundefCtxData { add_simps, case_names, psimps, pinducts, defname, ... } = data

      val totality = Thm.close_derivation totality

      val remove_domain_condition = full_simplify (HOL_basic_ss addsimps [totality, True_implies_equals])

      val tsimps = map remove_domain_condition psimps
      val tinduct = map remove_domain_condition pinducts

      val qualify = Long_Name.qualify defname;
    in
      lthy
        |> add_simps I "simps" simp_attribs tsimps |> snd
        |> note_theorem ((qualify "induct", [Attrib.internal (K (RuleCases.case_names case_names))]), tinduct) |> snd
    end

fun gen_termination_proof prep_term raw_term_opt lthy =
    let
      val term_opt = Option.map (prep_term lthy) raw_term_opt
      val data = the (case term_opt of
                        SOME t => (import_fundef_data t lthy
                          handle Option.Option =>
                            error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
                      | NONE => (import_last_fundef lthy handle Option.Option => error "Not a function"))

        val FundefCtxData {termination, R, ...} = data
        val domT = domain_type (fastype_of R)
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
    in
      lthy
        |> ProofContext.note_thmss "" [((Binding.empty, [ContextRules.rule_del]), [([allI], [])])] |> snd
        |> ProofContext.note_thmss "" [((Binding.empty, [ContextRules.intro_bang (SOME 1)]), [([allI], [])])] |> snd
        |> ProofContext.note_thmss ""
          [((Binding.name "termination", [ContextRules.intro_bang (SOME 0)]),
            [([Goal.norm_result termination], [])])] |> snd
        |> Proof.theorem_i NONE (total_termination_afterqed data) [[(goal, [])]]
    end

val termination_proof = gen_termination_proof Syntax.check_term;
val termination_proof_cmd = gen_termination_proof Syntax.read_term;

fun termination term_opt lthy =
  lthy
  |> LocalTheory.set_group (serial_string ())
  |> termination_proof term_opt;

fun termination_cmd term_opt lthy =
  lthy
  |> LocalTheory.set_group (serial_string ())
  |> termination_proof_cmd term_opt;


(* Datatype hook to declare datatype congs as "fundef_congs" *)


fun add_case_cong n thy =
    Context.theory_map (FundefCtxTree.map_fundef_congs (Thm.add_thm
                          (DatatypePackage.get_datatype thy n |> the
                           |> #case_cong
                           |> safe_mk_meta_eq)))
                       thy

val case_cong = fold add_case_cong

val setup_case_cong = DatatypePackage.interpretation case_cong


(* setup *)

val setup =
  Attrib.setup @{binding fundef_cong} (Attrib.add_del FundefCtxTree.cong_add FundefCtxTree.cong_del)
      "declaration of congruence rule for function definitions"
  #> setup_case_cong
  #> FundefRelation.setup
  #> FundefCommon.TerminationSimps.setup

val get_congs = FundefCtxTree.get_fundef_congs


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val _ =
  OuterSyntax.local_theory_to_proof "function" "define general recursive functions" K.thy_goal
  (fundef_parser default_config
     >> (fn ((config, fixes), statements) => add_fundef_cmd fixes statements config));

val _ =
  OuterSyntax.local_theory_to_proof "termination" "prove termination of a recursive function" K.thy_goal
  (Scan.option P.term >> termination_cmd);

end;


end
