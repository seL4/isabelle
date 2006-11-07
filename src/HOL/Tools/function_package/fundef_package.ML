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
    val get_congs : theory -> thm list
end


structure FundefPackage  =
struct

open FundefLib
open FundefCommon

(*fn (ctxt,s) => Variable.importT_terms (fst (ProofContext.read_termTs ctxt (K false) (K NONE) (K NONE) [] [s])) ctxt;*)

fun burrow_snd f ps = (* ('a list -> 'b list) -> ('c * 'a) list -> ('c * 'b) list *)
    let val (xs, ys) = split_list ps
    in xs ~~ f ys end

fun restore_spec_structure reps spec =
    (burrow o burrow_snd o burrow o K) reps spec

fun add_simps label moreatts mutual_info fixes psimps spec lthy =
    let
      val fnames = map (fst o fst) fixes
      val psimps_by_f = FundefMutual.sort_by_function mutual_info fnames psimps

      fun add_for_f fname psimps =
          LocalTheory.note ((NameSpace.append fname label, Attrib.internal Simplifier.simp_add :: moreatts), psimps) #> snd
    in
      lthy
        |> fold_map (fold_map LocalTheory.note) (restore_spec_structure psimps spec) |> snd
        |> fold2 add_for_f fnames psimps_by_f
    end


fun fundef_afterqed fixes spec mutual_info defname data [[result]] lthy =
    let
        val fundef_data = FundefMutual.mk_partial_rules_mutual lthy mutual_info data result
        val FundefMResult {psimps, subset_pinducts, simple_pinducts, termination, domintros, cases, ...} = fundef_data
        val qualify = NameSpace.append defname;
    in
      lthy
        |> add_simps "psimps" [] mutual_info fixes psimps spec
        |> LocalTheory.note ((qualify "domintros", []), domintros) |> snd
        |> LocalTheory.note ((qualify "termination", []), [termination]) |> snd
        |> LocalTheory.note ((qualify "cases", []), [cases]) |> snd
        |> LocalTheory.note ((qualify "pinduct", [Attrib.internal (InductAttrib.induct_set "")]), simple_pinducts) |> snd
        |> LocalTheory.declaration (add_fundef_data defname (fundef_data, mutual_info, (fixes,spec)))
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
      val FundefConfig {sequential, default, ...} = config

      val ((fixes, spec), ctxt') = prep_with_flags prep_spec fixspec eqnss_flags sequential lthy
      val t_eqns = spec
                     |> flat |> map snd |> flat (* flatten external structure *)

      val ((mutual_info, name, prep_result as Prep {goal, goalI, ...}), lthy) =
          FundefMutual.prepare_fundef_mutual fixes t_eqns default lthy

      val afterqed = fundef_afterqed fixes spec mutual_info name prep_result
    in
      (name, lthy
         |> Proof.theorem_i PureThy.internalK NONE afterqed NONE ("", []) [(("", []), [(goal, [])])]
         |> Proof.refine (Method.primitive_text (fn _ => goalI)) |> Seq.hd)
    end


fun total_termination_afterqed defname data [[totality]] lthy =
    let
        val (FundefMResult {psimps, simple_pinducts, ... }, mutual_info, (fixes, stmts)) = data

        val remove_domain_condition = full_simplify (HOL_basic_ss addsimps [totality, True_implies_equals])

        val tsimps = map remove_domain_condition psimps
        val tinduct = map remove_domain_condition simple_pinducts

        (* FIXME: How to generate code from (possibly) local contexts
        val has_guards = exists ((fn (Const ("Trueprop", _) $ _) => false | _ => true) o prop_of) tsimps
        val allatts = if has_guards then [] else [Attrib.internal (RecfunCodegen.add NONE)]
        *)
        val qualify = NameSpace.append defname;
    in
        lthy
          |> add_simps "simps" [] mutual_info fixes tsimps stmts
          |> LocalTheory.note ((qualify "induct", []), tinduct) |> snd
    end


fun setup_termination_proof name_opt lthy =
    let
        val name = the_default (get_last_fundef (Context.Proof lthy)) name_opt
        val data = the (get_fundef_data name (Context.Proof lthy))
                   handle Option.Option => raise ERROR ("No such function definition: " ^ name)

        val (res as FundefMResult {termination, ...}, _, _) = data
        val goal = FundefTermination.mk_total_termination_goal data
    in
      lthy
        |> ProofContext.note_thmss_i [(("termination",
                                 [ContextRules.intro_query NONE]), [(ProofContext.standard lthy [termination], [])])] |> snd
        |> Proof.theorem_i PureThy.internalK NONE
                           (total_termination_afterqed name data) NONE ("", [])
                           [(("", []), [(goal, [])])]
    end


val add_fundef = gen_add_fundef Specification.read_specification
val add_fundef_i = gen_add_fundef Specification.cert_specification



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



fun or_list1 s = P.enum1 "|" s

val opt_sequential = Scan.optional ((P.$$$ "(" |-- P.$$$ "sequential" --| P.$$$ ")") >> K true) false

val otherwise = P.$$$ "(" |-- P.$$$ "otherwise" --| P.$$$ ")"
val statement_ow = P.and_list1 (P.opt_thm_name ":" -- Scan.repeat1 (P.prop -- Scan.optional (otherwise >> K true) false))
val statements_ow = or_list1 statement_ow


val functionP =
  OuterSyntax.command "function" "define general recursive functions" K.thy_goal
  ((config_parser default_config -- P.opt_locale_target -- P.fixes --| P.$$$ "where" -- statements_ow)
     >> (fn (((config, target), fixes), statements) =>
            Toplevel.local_theory_to_proof target (add_fundef fixes statements config #> snd)
            #> Toplevel.print));



val terminationP =
  OuterSyntax.command "termination" "prove termination of a recursive function" K.thy_goal
  (P.opt_locale_target -- Scan.option P.name
    >> (fn (target, name) =>
           Toplevel.print o
           Toplevel.local_theory_to_proof target (setup_termination_proof name)));


val _ = OuterSyntax.add_parsers [functionP];
val _ = OuterSyntax.add_parsers [terminationP];
val _ = OuterSyntax.add_keywords ["sequential", "otherwise"];

end;


end
