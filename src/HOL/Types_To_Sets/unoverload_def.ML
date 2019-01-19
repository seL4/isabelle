(*  Title:      HOL/Types_To_Sets/unoverload_def.ML
    Author:     Fabian Immler, CMU

Define unoverloaded constants from overloaded definitions.
*)

structure Unoverload_Def = struct

fun unoverload_def name_opt thm thy =
  let
    val ctxt = Proof_Context.init_global thy
    val thm_abs = Local_Defs.abs_def_rule ctxt thm
      |> Conv.fconv_rule (Conv.top_conv
        (K (Conv.try_conv (Conv.rewrs_conv
              (Named_Theorems.get ctxt @{named_theorems unoverload_def})))) ctxt)
    val (lhs, rhs) = thm_abs
      |> Thm.cprop_of
      |> Thm.dest_equals
    val c = lhs |> Thm.term_of |> Term.dest_Const
    val binding_with =
      case name_opt of NONE =>
        Binding.qualify_name true
          (Binding.name (Binding.name_of (Binding.qualified_name (#1 c))))
          "with"
      | SOME name => name

    val tvars = Term.add_tvars (Thm.term_of rhs) [] |> map fst

    val thm_with = Thm.reflexive rhs
      |> Unoverload_Type.unoverload_type (Context.Proof ctxt) (tvars)

    val rhs_with' = thm_with |> Thm.cconcl_of |> Thm.dest_equals |> #2 |> Thm.term_of
    val vars = Term.add_vars rhs_with' []
    val rhs_abs = fold (Var #> Term.lambda) vars rhs_with'

    val ([rhs_abs'], ctxt') = Variable.importT_terms [rhs_abs] ctxt
    val (with_const, thy') = Sign.declare_const_global
      ((binding_with, Term.fastype_of rhs_abs'), NoSyn)
      thy
    val ([with_def], thy'') = Global_Theory.add_defs false
      [((Binding.suffix_name "_def" binding_with,
      Logic.mk_equals (with_const, rhs_abs')), [])] thy'

    val with_var_def =
      fold_rev
        (fn (x, _) => fn thm =>
          let
            val ty = Thm.concl_of thm |> Logic.dest_equals |> #2 |>
              fastype_of |> dest_funT |> #1
          in
            Thm.combination thm
              (Thm.reflexive (Thm.var (x, Thm.ctyp_of (Proof_Context.init_global thy'') ty)))
          end)
        (vars)
        (with_def)

    val thm_with = ([thm_abs, Thm.symmetric with_var_def] MRS @{thm Pure.transitive})
    val thy''' =
      Global_Theory.add_thm
        ((binding_with, thm_with), [Named_Theorems.add @{named_theorems "unoverload_def"}]) thy''
      |> #2
  in thy''' end

fun unoverload_def1_cmd (name_opt, facts) thy =
  let
    val [thm] = Attrib.eval_thms (Proof_Context.init_global thy) [facts]
  in unoverload_def name_opt thm thy end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>unoverload_definition\<close>
    "definition of unoverloaded constants"
    (Parse.and_list (Scan.option (Parse.binding --| \<^keyword>\<open>:\<close>) -- Parse.thm) >>
      (fn things => Local_Theory.raw_theory (fold unoverload_def1_cmd things))
    )

end