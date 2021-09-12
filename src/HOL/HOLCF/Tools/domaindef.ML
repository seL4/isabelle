(*  Title:      HOL/HOLCF/Tools/domaindef.ML
    Author:     Brian Huffman

Defining representable domains using algebraic deflations.
*)

signature DOMAINDEF =
sig
  type rep_info =
    {
      emb_def : thm,
      prj_def : thm,
      defl_def : thm,
      liftemb_def : thm,
      liftprj_def : thm,
      liftdefl_def : thm,
      DEFL : thm
    }

  val add_domaindef: binding * (string * sort) list * mixfix ->
    term -> Typedef.bindings option -> theory ->
    (Typedef.info * Cpodef.cpo_info * Cpodef.pcpo_info * rep_info) * theory

  val domaindef_cmd: (binding * (string * string option) list * mixfix) * string
    * Typedef.bindings option -> theory -> theory
end

structure Domaindef : DOMAINDEF =
struct

open HOLCF_Library

infixr 6 ->>
infix -->>

(** type definitions **)

type rep_info =
  {
    emb_def : thm,
    prj_def : thm,
    defl_def : thm,
    liftemb_def : thm,
    liftprj_def : thm,
    liftdefl_def : thm,
    DEFL : thm
  }

(* building types and terms *)

val udomT = \<^typ>\<open>udom\<close>
val deflT = \<^typ>\<open>udom defl\<close>
fun emb_const T = \<^Const>\<open>emb T\<close>
fun prj_const T = \<^Const>\<open>prj T\<close>
fun defl_const T = \<^Const>\<open>defl T\<close>
fun liftemb_const T = \<^Const>\<open>liftemb T\<close>
fun liftprj_const T = \<^Const>\<open>liftprj T\<close>
fun liftdefl_const T = \<^Const>\<open>liftdefl T\<close>

fun mk_u_map t =
  let
    val (T, U) = dest_cfunT (fastype_of t)
    val u_map_const = \<^Const>\<open>u_map T U\<close>
  in
    mk_capply (u_map_const, t)
  end

fun mk_cast (t, x) =
  capply_const (udomT, udomT)
  $ (capply_const (deflT, udomT ->> udomT) $ \<^term>\<open>cast :: udom defl -> udom -> udom\<close> $ t)
  $ x

(* manipulating theorems *)

(* proving class instances *)

fun gen_add_domaindef
      (prep_term: Proof.context -> 'a -> term)
      (typ as (tname, raw_args, _) : binding * (string * sort) list * mixfix)
      (raw_defl: 'a)
      (opt_bindings: Typedef.bindings option)
      (thy: theory)
    : (Typedef.info * Cpodef.cpo_info * Cpodef.pcpo_info * rep_info) * theory =
  let
    (*rhs*)
    val tmp_ctxt =
      Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) raw_args
    val defl = prep_term tmp_ctxt raw_defl
    val tmp_ctxt = tmp_ctxt |> Variable.declare_constraints defl

    val deflT = Term.fastype_of defl
    val _ = if deflT = \<^typ>\<open>udom defl\<close> then ()
            else error ("Not type defl: " ^ quote (Syntax.string_of_typ tmp_ctxt deflT))

    (*lhs*)
    val lhs_tfrees = map (Proof_Context.check_tfree tmp_ctxt) raw_args
    val full_tname = Sign.full_name thy tname
    val newT = Type (full_tname, map TFree lhs_tfrees)

    (*set*)
    val set = \<^term>\<open>defl_set :: udom defl => udom set\<close> $ defl

    (*pcpodef*)
    fun tac1 ctxt = resolve_tac ctxt @{thms defl_set_bottom} 1
    fun tac2 ctxt = resolve_tac ctxt @{thms adm_defl_set} 1
    val ((info, cpo_info, pcpo_info), thy) = thy
      |> Cpodef.add_pcpodef typ set opt_bindings (tac1, tac2)

    (*definitions*)
    val Rep_const = Const (#Rep_name (#1 info), newT --> udomT)
    val Abs_const = Const (#Abs_name (#1 info), udomT --> newT)
    val emb_eqn = Logic.mk_equals (emb_const newT, cabs_const (newT, udomT) $ Rep_const)
    val prj_eqn = Logic.mk_equals (prj_const newT, cabs_const (udomT, newT) $
      Abs ("x", udomT, Abs_const $ mk_cast (defl, Bound 0)))
    val defl_eqn = Logic.mk_equals (defl_const newT,
      Abs ("x", Term.itselfT newT, defl))
    val liftemb_eqn =
      Logic.mk_equals (liftemb_const newT, mk_u_map (emb_const newT))
    val liftprj_eqn =
      Logic.mk_equals (liftprj_const newT, mk_u_map (prj_const newT))
    val liftdefl_eqn =
      Logic.mk_equals (liftdefl_const newT,
        Abs ("t", Term.itselfT newT,
          mk_capply (\<^Const>\<open>liftdefl_of\<close>, defl_const newT $ Logic.mk_type newT)))

    val name_def = Thm.def_binding tname
    val emb_bind = (Binding.prefix_name "emb_" name_def, [])
    val prj_bind = (Binding.prefix_name "prj_" name_def, [])
    val defl_bind = (Binding.prefix_name "defl_" name_def, [])
    val liftemb_bind = (Binding.prefix_name "liftemb_" name_def, [])
    val liftprj_bind = (Binding.prefix_name "liftprj_" name_def, [])
    val liftdefl_bind = (Binding.prefix_name "liftdefl_" name_def, [])

    (*instantiate class rep*)
    val lthy = thy
      |> Class.instantiation ([full_tname], lhs_tfrees, \<^sort>\<open>domain\<close>)
    val ((_, (_, emb_ldef)), lthy) =
        Specification.definition NONE [] [] (emb_bind, emb_eqn) lthy
    val ((_, (_, prj_ldef)), lthy) =
        Specification.definition NONE [] [] (prj_bind, prj_eqn) lthy
    val ((_, (_, defl_ldef)), lthy) =
        Specification.definition NONE [] [] (defl_bind, defl_eqn) lthy
    val ((_, (_, liftemb_ldef)), lthy) =
        Specification.definition NONE [] [] (liftemb_bind, liftemb_eqn) lthy
    val ((_, (_, liftprj_ldef)), lthy) =
        Specification.definition NONE [] [] (liftprj_bind, liftprj_eqn) lthy
    val ((_, (_, liftdefl_ldef)), lthy) =
        Specification.definition NONE [] [] (liftdefl_bind, liftdefl_eqn) lthy
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
    val emb_def = singleton (Proof_Context.export lthy ctxt_thy) emb_ldef
    val prj_def = singleton (Proof_Context.export lthy ctxt_thy) prj_ldef
    val defl_def = singleton (Proof_Context.export lthy ctxt_thy) defl_ldef
    val liftemb_def = singleton (Proof_Context.export lthy ctxt_thy) liftemb_ldef
    val liftprj_def = singleton (Proof_Context.export lthy ctxt_thy) liftprj_ldef
    val liftdefl_def = singleton (Proof_Context.export lthy ctxt_thy) liftdefl_ldef
    val typedef_thms =
      [#type_definition (#2 info), #below_def cpo_info, emb_def, prj_def, defl_def,
      liftemb_def, liftprj_def, liftdefl_def]
    val thy = lthy
      |> Class.prove_instantiation_instance
          (fn ctxt => resolve_tac ctxt [@{thm typedef_domain_class} OF typedef_thms] 1)
      |> Local_Theory.exit_global

    (*other theorems*)
    val defl_thm' = Thm.transfer thy defl_def
    val (DEFL_thm, thy) = thy
      |> Sign.add_path (Binding.name_of tname)
      |> Global_Theory.add_thm
         ((Binding.prefix_name "DEFL_" tname,
          Drule.zero_var_indexes (@{thm typedef_DEFL} OF [defl_thm'])), [])
      ||> Sign.restore_naming thy

    val rep_info =
      { emb_def = emb_def, prj_def = prj_def, defl_def = defl_def,
        liftemb_def = liftemb_def, liftprj_def = liftprj_def,
        liftdefl_def = liftdefl_def, DEFL = DEFL_thm }
  in
    ((info, cpo_info, pcpo_info, rep_info), thy)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in domaindef " ^ Binding.print tname)

fun add_domaindef typ defl opt_bindings thy =
  gen_add_domaindef Syntax.check_term typ defl opt_bindings thy

fun domaindef_cmd ((b, raw_args, mx), A, morphs) thy =
  let
    val ctxt = Proof_Context.init_global thy
    val args = map (apsnd (Typedecl.read_constraint ctxt)) raw_args
  in snd (gen_add_domaindef Syntax.read_term (b, args, mx) A morphs thy) end


(** outer syntax **)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>domaindef\<close> "HOLCF definition of domains from deflations"
    ((Parse.type_args_constrained -- Parse.binding) --
      Parse.opt_mixfix -- (\<^keyword>\<open>=\<close> |-- Parse.term) --
      Scan.option
        (\<^keyword>\<open>morphisms\<close> |-- Parse.!!! (Parse.binding -- Parse.binding)) >>
     (fn (((((args, t)), mx), A), morphs) =>
      Toplevel.theory (domaindef_cmd ((t, args, mx), A, SOME (Typedef.make_morphisms t morphs)))));

end
