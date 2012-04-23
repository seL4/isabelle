(*  Title:      HOL/Tools/Function/function.ML
    Author:     Alexander Krauss, TU Muenchen

Main entry points to the function package.
*)

signature FUNCTION =
sig
  include FUNCTION_DATA

  val add_function: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> Function_Common.function_config ->
    (Proof.context -> tactic) -> local_theory -> info * local_theory

  val add_function_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> Function_Common.function_config ->
    (Proof.context -> tactic) -> bool -> local_theory -> info * local_theory

  val function: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> Function_Common.function_config ->
    local_theory -> Proof.state

  val function_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> Function_Common.function_config ->
    bool -> local_theory -> Proof.state

  val prove_termination: term option -> tactic -> local_theory -> 
    info * local_theory
  val prove_termination_cmd: string option -> tactic -> local_theory ->
    info * local_theory

  val termination : term option -> local_theory -> Proof.state
  val termination_cmd : string option -> local_theory -> Proof.state

  val setup : theory -> theory
  val get_congs : Proof.context -> thm list

  val get_info : Proof.context -> term -> info
end


structure Function : FUNCTION =
struct

open Function_Lib
open Function_Common

val simp_attribs =
  @{attributes [simp, nitpick_simp]} @ [Attrib.internal (K Code.add_default_eqn_attribute)]

val psimp_attribs =
  @{attributes [nitpick_psimp]}

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_"

fun add_simps fnames post sort extra_qualify label mod_binding moreatts
  simps lthy =
  let
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify))

    val (saved_spec_simps, lthy) =
      fold_map Local_Theory.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun add_for_f fname simps =
      Local_Theory.note
        ((mod_binding (Binding.qualify true fname (Binding.name label)), []), simps)
      #> snd
  in
    (saved_simps, fold2 add_for_f fnames simps_by_f lthy)
  end

fun prepare_function do_print prep default_constraint fixspec eqns config lthy =
  let
    val constrn_fxs = map (fn (b, T, mx) => (b, SOME (the_default default_constraint T), mx))
    val ((fixes0, spec0), ctxt') = prep (constrn_fxs fixspec) eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0;
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0;
    val (eqs, post, sort_cont, cnames) = get_preproc lthy config ctxt' fixes spec

    val defname = mk_defname fixes
    val FunctionConfig {partials, default, ...} = config
    val _ =
      if is_some default
      then legacy_feature "\"function (default)\" -- use 'partial_function' instead"
      else ()

    val ((goal_state, cont), lthy') =
      Function_Mutual.prepare_function_mutual config defname fixes eqs lthy

    fun afterqed [[proof]] lthy =
      let
        val FunctionResult {fs, R, psimps, simple_pinducts,
          termination, domintros, cases, ...} =
          cont (Thm.close_derivation proof)

        val fnames = map (fst o fst) fixes
        fun qualify n = Binding.name n
          |> Binding.qualify true defname
        val conceal_partial = if partials then I else Binding.conceal

        val addsmps = add_simps fnames post sort_cont

        val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
          |> addsmps (conceal_partial o Binding.qualify false "partial")
               "psimps" conceal_partial psimp_attribs psimps
          ||>> Local_Theory.note ((conceal_partial (qualify "pinduct"),
                 [Attrib.internal (K (Rule_Cases.case_names cnames)),
                  Attrib.internal (K (Rule_Cases.consumes 1)),
                  Attrib.internal (K (Induct.induct_pred ""))]), simple_pinducts)
          ||>> Local_Theory.note ((Binding.conceal (qualify "termination"), []), [termination])
          ||> (snd o Local_Theory.note ((qualify "cases",
                 [Attrib.internal (K (Rule_Cases.case_names cnames))]), [cases]))
          ||> (case domintros of NONE => I | SOME thms => 
                   Local_Theory.note ((qualify "domintros", []), thms) #> snd)

        val info = { add_simps=addsmps, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination',
          fs=fs, R=R, defname=defname, is_partial=true }

        val _ = Proof_Display.print_consts do_print lthy (K false) (map fst fixes)
      in
        (info,
         lthy |> Local_Theory.declaration {syntax = false, pervasive = false}
          (add_function_data o transform_function_data info))
      end
  in
    ((goal_state, afterqed), lthy')
  end

fun gen_add_function do_print prep default_constraint fixspec eqns config tac lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep default_constraint fixspec eqns config lthy
    val pattern_thm =
      case SINGLE (tac lthy') goal_state of
        NONE => error "pattern completeness and compatibility proof failed"
      | SOME st => Goal.finish lthy' st
  in
    lthy'
    |> afterqed [[pattern_thm]]
  end

val add_function =
  gen_add_function false Specification.check_spec (Type_Infer.anyT HOLogic.typeS)
fun add_function_cmd a b c d int = gen_add_function int Specification.read_spec "_::type" a b c d

fun gen_function do_print prep default_constraint fixspec eqns config lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep default_constraint fixspec eqns config lthy
  in
    lthy'
    |> Proof.theorem NONE (snd oo afterqed) [[(Logic.unprotect (concl_of goal_state), [])]]
    |> Proof.refine (Method.primitive_text (K goal_state)) |> Seq.hd
  end

val function =
  gen_function false Specification.check_spec (Type_Infer.anyT HOLogic.typeS)
fun function_cmd a b c int = gen_function int Specification.read_spec "_::type" a b c

fun prepare_termination_proof prep_term raw_term_opt lthy =
  let
    val term_opt = Option.map (prep_term lthy) raw_term_opt
    val info = the (case term_opt of
                      SOME t => (import_function_data t lthy
                        handle Option.Option =>
                          error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
                    | NONE => (import_last_function lthy handle Option.Option => error "Not a function"))

      val { termination, fs, R, add_simps, case_names, psimps,
        pinducts, defname, ...} = info
      val domT = domain_type (fastype_of R)
      val goal = HOLogic.mk_Trueprop
                   (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
      fun afterqed [[totality]] lthy =
        let
          val totality = Thm.close_derivation totality
          val remove_domain_condition =
            full_simplify (HOL_basic_ss addsimps [totality, @{thm True_implies_equals}])
          val tsimps = map remove_domain_condition psimps
          val tinduct = map remove_domain_condition pinducts

          fun qualify n = Binding.name n
            |> Binding.qualify true defname
        in
          lthy
          |> add_simps I "simps" I simp_attribs tsimps
          ||>> Local_Theory.note
             ((qualify "induct",
               [Attrib.internal (K (Rule_Cases.case_names case_names))]),
              tinduct)
          |-> (fn (simps, (_, inducts)) => fn lthy =>
            let val info' = { is_partial=false, defname=defname, add_simps=add_simps,
              case_names=case_names, fs=fs, R=R, psimps=psimps, pinducts=pinducts,
              simps=SOME simps, inducts=SOME inducts, termination=termination }
            in
              (info',
               lthy 
               |> Local_Theory.declaration {syntax = false, pervasive = false}
                 (add_function_data o transform_function_data info')
               |> Spec_Rules.add Spec_Rules.Equational (fs, tsimps))
            end)
        end
  in
    (goal, afterqed, termination)
  end

fun gen_prove_termination prep_term raw_term_opt tac lthy =
  let
    val (goal, afterqed, termination) =
      prepare_termination_proof prep_term raw_term_opt lthy

    val totality = Goal.prove lthy [] [] goal (K tac)
  in
    afterqed [[totality]] lthy
end

val prove_termination = gen_prove_termination Syntax.check_term
val prove_termination_cmd = gen_prove_termination Syntax.read_term

fun gen_termination prep_term raw_term_opt lthy =
  let
    val (goal, afterqed, termination) = prepare_termination_proof prep_term raw_term_opt lthy
  in
    lthy
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.rule_del]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.intro_bang (SOME 1)]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.name "termination", [Context_Rules.intro_bang (SOME 0)]),
         [([Goal.norm_result termination], [])])] |> snd
    |> Proof.theorem NONE (snd oo afterqed) [[(goal, [])]]
  end

val termination = gen_termination Syntax.check_term
val termination_cmd = gen_termination Syntax.read_term


(* Datatype hook to declare datatype congs as "function_congs" *)


fun add_case_cong n thy =
  let
    val cong = #case_cong (Datatype.the_info thy n)
      |> safe_mk_meta_eq
  in
    Context.theory_map
      (Function_Ctx_Tree.map_function_congs (Thm.add_thm cong)) thy
  end

val setup_case_cong = Datatype.interpretation (K (fold add_case_cong))


(* setup *)

val setup =
  Attrib.setup @{binding fundef_cong}
    (Attrib.add_del Function_Ctx_Tree.cong_add Function_Ctx_Tree.cong_del)
    "declaration of congruence rule for function definitions"
  #> setup_case_cong
  #> Function_Common.Termination_Simps.setup

val get_congs = Function_Ctx_Tree.get_function_congs

fun get_info ctxt t = Item_Net.retrieve (get_function ctxt) t
  |> the_single |> snd


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof' @{command_spec "function"}
    "define general recursive functions"
    (function_parser default_config
      >> (fn ((config, fixes), statements) => function_cmd fixes statements config))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "termination"}
    "prove termination of a recursive function"
    (Scan.option Parse.term >> termination_cmd)


end
