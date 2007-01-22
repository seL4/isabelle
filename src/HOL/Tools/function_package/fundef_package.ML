(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Isar commands.

*)

signature FUNDEF_PACKAGE =
sig
    val add_fundef :  (string * string option * mixfix) list
                      -> ((bstring * Attrib.src list) * string list) list list
                      -> FundefCommon.fundef_config
                      -> local_theory
                      -> string * Proof.state

    val add_fundef_i:  (string * typ option * mixfix) list
                       -> ((bstring * Attrib.src list) * term list) list list
                       -> bool
                       -> local_theory
                       -> string * Proof.state

    val setup_termination_proof : string option -> local_theory -> Proof.state

    val cong_add: attribute
    val cong_del: attribute

    val setup : theory -> theory
    val setup_case_cong_hook : theory -> theory
    val get_congs : theory -> thm list
end


structure FundefPackage  =
struct

open FundefLib
open FundefCommon

val note_theorem = LocalTheory.note Thm.theoremK

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_" 

fun burrow_snd f ps = (* ('a list -> 'b list) -> ('c * 'a) list -> ('c * 'b) list *)
    let val (xs, ys) = split_list ps
    in xs ~~ f ys end

fun restore_spec_structure reps spec =
    (burrow o burrow_snd o burrow o K) reps spec

fun add_simps fixes spec sort label moreatts simps lthy =
    let
      val fnames = map (fst o fst) fixes

      val (saved_spec_simps, lthy) =
        fold_map (fold_map note_theorem) (restore_spec_structure simps spec) lthy
      val saved_simps = flat (map snd (flat saved_spec_simps))

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
      val FundefResult {f, R, psimps, trsimps, subset_pinducts, simple_pinducts, termination, domintros, cases, ...} = 
          cont (Goal.close_result proof)

      val qualify = NameSpace.qualified defname
      val addsimps = add_simps fixes spec sort_cont

      val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
            |> addsimps "psimps" [] psimps
            ||> fold_option (snd oo addsimps "simps" []) trsimps
            ||>> note_theorem ((qualify "pinduct",
                                [Attrib.internal (K (InductAttrib.induct_set ""))]), simple_pinducts)
            ||>> note_theorem ((qualify "termination", []), [termination])
            ||> (snd o note_theorem ((qualify "cases", []), [cases]))
            ||> fold_option (snd oo curry note_theorem (qualify "domintros", [])) domintros

      val cdata = FundefCtxData { add_simps=addsimps, psimps=psimps',
                                  pinducts=snd pinducts', termination=termination', f=f, R=R }
    in
      lthy  (* FIXME proper handling of morphism *)
        |> LocalTheory.declaration (fn phi => add_fundef_data defname cdata) (* save in target *)
        |> Context.proof_map (add_fundef_data defname cdata) (* also save in local context *)
    end (* FIXME: Add cases for induct and cases thm *)



fun prep_with_flags prep fixspec eqnss_flags global_flag lthy =
    let
      val eqnss = map (map (apsnd (map fst))) eqnss_flags
      val flags = map (map (map (fn (_, f) => global_flag orelse f) o snd)) eqnss_flags

      val ((fixes, _), ctxt') = prep fixspec [] lthy
      val spec = map (fn eqns => snd (fst (prep [] eqns ctxt'))) eqnss
                     |> map (map (apsnd (map (fn t => fold_rev (mk_forall o Free) (frees_in_term ctxt' t) t)))) (* Add quantifiers *)
                     |> map2 (map2 (fn fs => fn (r, thms) => (r, fs ~~ thms))) flags
                     |> (burrow o burrow_snd o burrow)
                          (FundefSplit.split_some_equations lthy)
                     |> map (map (apsnd flat))
    in
      ((fixes, spec), ctxt')
    end


fun gen_add_fundef prep_spec fixspec eqnss_flags config lthy =
    let
      val FundefConfig {sequential, default, tailrec, ...} = config

      val ((fixes, spec), ctxt') = prep_with_flags prep_spec fixspec eqnss_flags sequential lthy

      val defname = mk_defname fixes

      val t_eqns = spec
                     |> flat |> map snd |> flat (* flatten external structure *)

      val ((goalstate, cont, sort_cont), lthy) =
          FundefMutual.prepare_fundef_mutual config defname fixes t_eqns default lthy

      val afterqed = fundef_afterqed config fixes spec defname cont sort_cont
    in
      (defname, lthy
         |> Proof.theorem_i NONE afterqed [[(Logic.unprotect (concl_of goalstate), [])]]
         |> Proof.refine (Method.primitive_text (fn _ => goalstate)) |> Seq.hd)
    end


fun total_termination_afterqed defname data [[totality]] lthy =
    let
      val FundefCtxData { add_simps, psimps, pinducts, ... } = data

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


fun setup_termination_proof name_opt lthy =
    let
        val defname = the_default (get_last_fundef (Context.Proof lthy)) name_opt
        val data = the (get_fundef_data defname (Context.Proof lthy))
                   handle Option.Option => raise ERROR ("No such function definition: " ^ defname)

        val FundefCtxData {termination, R, ...} = data
        val goal = FundefTermination.mk_total_termination_goal R
    in
      lthy
        |> ProofContext.note_thmss_i ""
          [(("termination", [ContextRules.intro_query NONE]),
            [([Goal.norm_result termination], [])])] |> snd
        |> set_termination_rule termination
        |> Proof.theorem_i NONE (total_termination_afterqed defname data) [[(goal, [])]]
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



fun or_list1 s = P.enum1 "|" s

val opt_sequential = Scan.optional ((P.$$$ "(" |-- P.$$$ "sequential" --| P.$$$ ")") >> K true) false

val otherwise = P.$$$ "(" |-- P.$$$ "otherwise" --| P.$$$ ")"
val statement_ow = P.and_list1 (SpecParse.opt_thm_name ":" -- Scan.repeat1 (P.prop -- Scan.optional (otherwise >> K true) false))
val statements_ow = or_list1 statement_ow


val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
  ((config_parser default_config -- P.opt_target -- P.fixes --| P.$$$ "where" -- statements_ow)
     >> (fn (((config, target), fixes), statements) =>
            Toplevel.local_theory_to_proof target (add_fundef fixes statements config #> snd)
            #> Toplevel.print));



val terminationP =
  OuterSyntax.command "termination" "prove termination of a recursive function" K.thy_goal
  (P.opt_target -- Scan.option P.name
    >> (fn (target, name) =>
           Toplevel.print o
           Toplevel.local_theory_to_proof target (setup_termination_proof name)));


val _ = OuterSyntax.add_parsers [functionP];
val _ = OuterSyntax.add_parsers [terminationP];
val _ = OuterSyntax.add_keywords ["sequential", "otherwise"];

end;


end
