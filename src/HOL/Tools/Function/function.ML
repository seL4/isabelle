(*  Title:      HOL/Tools/Function/function.ML
    Author:     Alexander Krauss, TU Muenchen

Main entry points to the function package.
*)

signature FUNCTION =
sig
  type info = Function_Common.info

  val add_function: (binding * typ option * mixfix) list ->
    Specification.multi_specs -> Function_Common.function_config ->
    (Proof.context -> tactic) -> local_theory -> info * local_theory

  val add_function_cmd: (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> Function_Common.function_config ->
    (Proof.context -> tactic) -> bool -> local_theory -> info * local_theory

  val function: (binding * typ option * mixfix) list ->
    Specification.multi_specs -> Function_Common.function_config ->
    local_theory -> Proof.state

  val function_cmd: (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> Function_Common.function_config ->
    bool -> local_theory -> Proof.state

  val prove_termination: term option -> tactic -> local_theory ->
    info * local_theory
  val prove_termination_cmd: string option -> tactic -> local_theory ->
    info * local_theory

  val termination : term option -> local_theory -> Proof.state
  val termination_cmd : string option -> local_theory -> Proof.state

  val get_congs : Proof.context -> thm list

  val get_info : Proof.context -> term -> info
end


structure Function : FUNCTION =
struct

open Function_Lib
open Function_Common

val simp_attribs =
  @{attributes [simp, nitpick_simp]}

val psimp_attribs =
  @{attributes [nitpick_psimp]}

fun note_derived (a, atts) (fname, thms) =
  Local_Theory.note ((derived_name fname a, atts), thms) #> apfst snd

fun add_simps fnames post sort extra_qualify label mod_binding moreatts simps lthy =
  let
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify))

    val (saved_spec_simps, lthy') =
      fold_map Local_Theory.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun note fname simps =
      Local_Theory.note ((mod_binding (derived_name fname label), []), simps) #> snd
  in (saved_simps, fold2 note fnames simps_by_f lthy') end

fun prepare_function do_print prep fixspec eqns config lthy =
  let
    val ((fixes0, spec0), ctxt') = prep fixspec eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0
    val (eqs, post, sort_cont, cnames) = get_preproc lthy config ctxt' fixes spec
    val props0 = map snd spec0
    val vars0 = map Term.strip_all_vars props0
    val input_eqns =
      map (fn (ps,prop) => Term.subst_bounds (rev (map Free ps), Term.strip_all_body prop))
        (vars0 ~~ props0)
    val fnames = map (fst o fst) fixes0
    val defname = Binding.conglomerate fnames;

    val FunctionConfig {partials, default, ...} = config
    val _ =
      if is_some default
      then legacy_feature "\"function (default)\" -- use 'partial_function' instead"
      else ()

    val ((goal_state, cont), lthy') =
      Function_Mutual.prepare_function_mutual config defname fixes0 eqs lthy

    fun afterqed [[proof]] lthy1 =
      let
        val result = cont lthy1 (Thm.close_derivation \<^here> proof)
        val FunctionResult {fs, R, dom, psimps, simple_pinducts,
                termination, domintros, cases, ...} = result

        val pelims = Function_Elims.mk_partial_elim_rules lthy1 result

        val concealed_partial = if partials then I else Binding.concealed

        val addsmps = add_simps fnames post sort_cont

        val (((((psimps', [pinducts']), [termination']), cases'), pelims'), lthy2) =
          lthy1
          |> addsmps (concealed_partial o Binding.qualify false "partial")
               "psimps" concealed_partial psimp_attribs psimps
          ||>> Local_Theory.notes [((concealed_partial (derived_name defname "pinduct"), []),
                simple_pinducts |> map (fn th => ([th],
                 [Attrib.case_names cnames, Attrib.consumes (1 - Thm.nprems_of th)] @
                 @{attributes [induct pred]})))]
          ||>> (apfst snd o
            Local_Theory.note
              ((Binding.concealed (derived_name defname "termination"), []), [termination]))
          ||>> fold_map (note_derived ("cases", [Attrib.case_names cnames]))
            (fnames ~~ map single cases)
          ||>> fold_map (note_derived ("pelims", [Attrib.consumes 1, Attrib.constraints 1]))
            (fnames ~~ pelims)
          ||> (case domintros of NONE => I | SOME thms =>
                Local_Theory.note ((derived_name defname "domintros", []), thms) #> snd)

        val info =
          { add_simps=addsmps, fnames=fnames, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination', totality=NONE,
          fs=fs, R=R, dom=dom, defname=defname, is_partial=true, cases=flat cases',
          pelims=pelims', elims=NONE, input_eqns = input_eqns}

        val _ =
          Proof_Display.print_consts do_print (Position.thread_data ()) lthy2
            (K false) (map fst fixes)
      in
        (info,
         lthy2 |> Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
          (fn phi => add_function_data (transform_function_data phi info)))
      end
  in
    ((goal_state, afterqed), lthy')
  end

fun gen_add_function do_print prep fixspec eqns config tac lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep fixspec eqns config lthy
    val pattern_thm =
      case SINGLE (tac lthy') goal_state of
        NONE => error "pattern completeness and compatibility proof failed"
      | SOME st => Goal.finish lthy' st
  in
    lthy'
    |> afterqed [[pattern_thm]]
  end

val add_function = gen_add_function false Specification.check_multi_specs
fun add_function_cmd a b c d int = gen_add_function int Specification.read_multi_specs a b c d

fun gen_function do_print prep fixspec eqns config lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep fixspec eqns config lthy
  in
    lthy'
    |> Proof.theorem NONE (snd oo afterqed) [[(Logic.unprotect (Thm.concl_of goal_state), [])]]
    |> Proof.refine_singleton (Method.primitive_text (K (K goal_state)))
  end

val function = gen_function false Specification.check_multi_specs
fun function_cmd a b c int = gen_function int Specification.read_multi_specs a b c

fun prepare_termination_proof prep_binding prep_term raw_term_opt lthy =
  let
    val term_opt = Option.map (prep_term lthy) raw_term_opt
    val info =
      (case term_opt of
        SOME t =>
          (case import_function_data t lthy of
            SOME info => info
          | NONE => error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
      | NONE =>
          (case import_last_function lthy of
            SOME info => info
          | NONE => error "Not a function"))

    val { termination, fs, R, add_simps, case_names, psimps,
      pinducts, defname, fnames, cases, dom, pelims, input_eqns, ...} = info
    val domT = domain_type (fastype_of R)
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
    fun afterqed [[raw_totality]] lthy1 =
      let
        val totality = Thm.close_derivation \<^here> raw_totality
        val remove_domain_condition =
          full_simplify (put_simpset HOL_basic_ss lthy1
            addsimps [totality, @{thm True_implies_equals}])
        val tsimps = map remove_domain_condition psimps
        val tinduct = map remove_domain_condition pinducts
        val telims = map (map remove_domain_condition) pelims
      in
        lthy1
        |> add_simps prep_binding "simps" prep_binding simp_attribs tsimps
        ||> Code.declare_default_eqns (map (rpair true) tsimps)
        ||>> Local_Theory.note
          ((prep_binding (derived_name defname "induct"), [Attrib.case_names case_names]), tinduct)
        ||>> fold_map (note_derived ("elims", [Attrib.consumes 1, Attrib.constraints 1]))
          (map prep_binding fnames ~~ telims)
        |-> (fn ((simps,(_,inducts)), elims) => fn lthy2 =>
          let val info' = { is_partial=false, defname=defname, fnames=fnames, add_simps=add_simps,
            case_names=case_names, fs=fs, R=R, dom=dom, psimps=psimps, pinducts=pinducts,
            simps=SOME simps, inducts=SOME inducts, termination=termination, totality=SOME totality,
            cases=cases, pelims=pelims, elims=SOME elims, input_eqns = input_eqns}
            |> transform_function_data (Morphism.binding_morphism "" prep_binding)
          in
            (info',
             lthy2
             |> Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
               (fn phi => add_function_data (transform_function_data phi info'))
             |> Spec_Rules.add Binding.empty Spec_Rules.equational_recdef fs tsimps)
          end)
      end
  in
    (goal, afterqed, termination)
  end

fun gen_prove_termination prep_term raw_term_opt tac lthy =
  let
    val (goal, afterqed, termination) =
      prepare_termination_proof I prep_term raw_term_opt lthy

    val totality = Goal.prove lthy [] [] goal (K tac)
  in
    afterqed [[totality]] lthy
end

val prove_termination = gen_prove_termination Syntax.check_term
val prove_termination_cmd = gen_prove_termination Syntax.read_term

fun gen_termination prep_term raw_term_opt lthy =
  let
    val (goal, afterqed, termination) =
      prepare_termination_proof Binding.reset_pos prep_term raw_term_opt lthy
  in
    lthy
    |> Proof_Context.note_thms ""
       ((Binding.empty, [Context_Rules.rule_del]), [([allI], [])]) |> snd
    |> Proof_Context.note_thms ""
       ((Binding.empty, [Context_Rules.intro_bang (SOME 1)]), [([allI], [])]) |> snd
    |> Proof_Context.note_thms ""
       ((Binding.name "termination", [Context_Rules.intro_bang (SOME 0)]),
         [([Goal.norm_result lthy termination], [])]) |> snd
    |> Proof.theorem NONE (snd oo afterqed) [[(goal, [])]]
  end

val termination = gen_termination Syntax.check_term
val termination_cmd = gen_termination Syntax.read_term


(* Datatype hook to declare datatype congs as "function_congs" *)

fun add_case_cong n thy =
  let
    val cong = #case_cong (Old_Datatype_Data.the_info thy n)
      |> safe_mk_meta_eq
  in
    Context.theory_map (Function_Context_Tree.add_function_cong cong) thy
  end

val _ = Theory.setup (Old_Datatype_Data.interpretation (K (fold add_case_cong)))


(* get info *)

val get_congs = Function_Context_Tree.get_function_congs

fun get_info ctxt t = Function_Common.retrieve_function_data ctxt t
  |> the_single |> snd


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>function\<close>
    "define general recursive functions"
    (function_parser default_config
      >> (fn (config, (fixes, specs)) => function_cmd fixes specs config))

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>termination\<close>
    "prove termination of a recursive function"
    (Scan.option Parse.term >> termination_cmd)

end
