(*  Title:      HOL/HOLCF/Tools/cpodef.ML
    Author:     Brian Huffman

Primitive domain definitions for HOLCF, similar to Gordon/HOL-style
typedef (see also ~~/src/HOL/Tools/typedef.ML).
*)

signature CPODEF =
sig
  type cpo_info =
    { below_def: thm, adm: thm, cont_Rep: thm, cont_Abs: thm,
      lub: thm, compact: thm }
  type pcpo_info =
    { Rep_strict: thm, Abs_strict: thm,
      Rep_bottom_iff: thm, Abs_bottom_iff: thm }

  val add_podef: bool -> binding option -> binding * (string * sort) list * mixfix ->
    term -> (binding * binding) option -> tactic -> theory ->
    (Typedef.info * thm) * theory
  val add_cpodef: bool -> binding option -> binding * (string * sort) list * mixfix ->
    term -> (binding * binding) option -> tactic * tactic -> theory ->
    (Typedef.info * cpo_info) * theory
  val add_pcpodef: bool -> binding option -> binding * (string * sort) list * mixfix ->
    term -> (binding * binding) option -> tactic * tactic -> theory ->
    (Typedef.info * cpo_info * pcpo_info) * theory

  val cpodef_proof: (bool * binding)
    * (binding * (string * sort) list * mixfix) * term
    * (binding * binding) option -> theory -> Proof.state
  val cpodef_proof_cmd: (bool * binding)
    * (binding * (string * string option) list * mixfix) * string
    * (binding * binding) option -> theory -> Proof.state
  val pcpodef_proof: (bool * binding)
    * (binding * (string * sort) list * mixfix) * term
    * (binding * binding) option -> theory -> Proof.state
  val pcpodef_proof_cmd: (bool * binding)
    * (binding * (string * string option) list * mixfix) * string
    * (binding * binding) option -> theory -> Proof.state
end

structure Cpodef : CPODEF =
struct

(** type definitions **)

type cpo_info =
  { below_def: thm, adm: thm, cont_Rep: thm, cont_Abs: thm,
    lub: thm, compact: thm }

type pcpo_info =
  { Rep_strict: thm, Abs_strict: thm,
    Rep_bottom_iff: thm, Abs_bottom_iff: thm }

(* building terms *)

fun adm_const T = Const (@{const_name adm}, (T --> HOLogic.boolT) --> HOLogic.boolT)
fun mk_adm (x, T, P) = adm_const T $ absfree (x, T) P

fun below_const T = Const (@{const_name below}, T --> T --> HOLogic.boolT)

(* manipulating theorems *)

fun fold_adm_mem thm NONE = thm
  | fold_adm_mem thm (SOME set_def) =
    let val rule = @{lemma "A == B ==> adm (%x. x : B) ==> adm (%x. x : A)" by simp}
    in rule OF [set_def, thm] end

fun fold_bottom_mem thm NONE = thm
  | fold_bottom_mem thm (SOME set_def) =
    let val rule = @{lemma "A == B ==> bottom : B ==> bottom : A" by simp}
    in rule OF [set_def, thm] end

(* proving class instances *)

fun prove_cpo
      (name: binding)
      (newT: typ)
      (Rep_name: binding, Abs_name: binding)
      (type_definition: thm)  (* type_definition Rep Abs A *)
      (set_def: thm option)   (* A == set *)
      (below_def: thm)        (* op << == %x y. Rep x << Rep y *)
      (admissible: thm)       (* adm (%x. x : set) *)
      (thy: theory)
    =
  let
    val admissible' = fold_adm_mem admissible set_def
    val cpo_thms = map (Thm.transfer thy) [type_definition, below_def, admissible']
    val (full_tname, Ts) = dest_Type newT
    val lhs_sorts = map (snd o dest_TFree) Ts
    val tac = Tactic.rtac (@{thm typedef_cpo} OF cpo_thms) 1
    val thy = AxClass.prove_arity (full_tname, lhs_sorts, @{sort cpo}) tac thy
    (* transfer thms so that they will know about the new cpo instance *)
    val cpo_thms' = map (Thm.transfer thy) cpo_thms
    fun make thm = Drule.zero_var_indexes (thm OF cpo_thms')
    val cont_Rep = make @{thm typedef_cont_Rep}
    val cont_Abs = make @{thm typedef_cont_Abs}
    val lub = make @{thm typedef_lub}
    val compact = make @{thm typedef_compact}
    val (_, thy) =
      thy
      |> Sign.add_path (Binding.name_of name)
      |> Global_Theory.add_thms
        ([((Binding.prefix_name "adm_"      name, admissible'), []),
          ((Binding.prefix_name "cont_" Rep_name, cont_Rep   ), []),
          ((Binding.prefix_name "cont_" Abs_name, cont_Abs   ), []),
          ((Binding.prefix_name "lub_"      name, lub        ), []),
          ((Binding.prefix_name "compact_"  name, compact    ), [])])
      ||> Sign.parent_path
    val cpo_info : cpo_info =
      { below_def = below_def, adm = admissible', cont_Rep = cont_Rep,
        cont_Abs = cont_Abs, lub = lub, compact = compact }
  in
    (cpo_info, thy)
  end

fun prove_pcpo
      (name: binding)
      (newT: typ)
      (Rep_name: binding, Abs_name: binding)
      (type_definition: thm)  (* type_definition Rep Abs A *)
      (set_def: thm option)   (* A == set *)
      (below_def: thm)        (* op << == %x y. Rep x << Rep y *)
      (bottom_mem: thm)       (* bottom : set *)
      (thy: theory)
    =
  let
    val bottom_mem' = fold_bottom_mem bottom_mem set_def
    val pcpo_thms = map (Thm.transfer thy) [type_definition, below_def, bottom_mem']
    val (full_tname, Ts) = dest_Type newT
    val lhs_sorts = map (snd o dest_TFree) Ts
    val tac = Tactic.rtac (@{thm typedef_pcpo} OF pcpo_thms) 1
    val thy = AxClass.prove_arity (full_tname, lhs_sorts, @{sort pcpo}) tac thy
    val pcpo_thms' = map (Thm.transfer thy) pcpo_thms
    fun make thm = Drule.zero_var_indexes (thm OF pcpo_thms')
    val Rep_strict = make @{thm typedef_Rep_strict}
    val Abs_strict = make @{thm typedef_Abs_strict}
    val Rep_bottom_iff = make @{thm typedef_Rep_bottom_iff}
    val Abs_bottom_iff = make @{thm typedef_Abs_bottom_iff}
    val (_, thy) =
      thy
      |> Sign.add_path (Binding.name_of name)
      |> Global_Theory.add_thms
        ([((Binding.suffix_name "_strict"     Rep_name, Rep_strict), []),
          ((Binding.suffix_name "_strict"     Abs_name, Abs_strict), []),
          ((Binding.suffix_name "_bottom_iff" Rep_name, Rep_bottom_iff), []),
          ((Binding.suffix_name "_bottom_iff" Abs_name, Abs_bottom_iff), [])])
      ||> Sign.parent_path
    val pcpo_info =
      { Rep_strict = Rep_strict, Abs_strict = Abs_strict,
        Rep_bottom_iff = Rep_bottom_iff, Abs_bottom_iff = Abs_bottom_iff }
  in
    (pcpo_info, thy)
  end

(* prepare_cpodef *)

fun prepare prep_term name (tname, raw_args, _) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Cpodef" "cpodefs"

    (*rhs*)
    val tmp_ctxt =
      Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) raw_args
    val set = prep_term tmp_ctxt raw_set
    val tmp_ctxt' = tmp_ctxt |> Variable.declare_term set

    val setT = Term.fastype_of set
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ tmp_ctxt setT))

    (*lhs*)
    val lhs_tfrees = map (Proof_Context.check_tfree tmp_ctxt') raw_args
    val full_tname = Sign.full_name thy tname
    val newT = Type (full_tname, map TFree lhs_tfrees)

    val morphs = opt_morphs
      |> the_default (Binding.prefix_name "Rep_" name, Binding.prefix_name "Abs_" name)
  in
    (newT, oldT, set, morphs)
  end

fun add_podef def opt_name typ set opt_morphs tac thy =
  let
    val name = the_default (#1 typ) opt_name
    val ((full_tname, info as ({Rep_name, ...}, {type_definition, ...})), thy) = thy
      |> Typedef.add_typedef_global def opt_name typ set opt_morphs tac
    val oldT = #rep_type (#1 info)
    val newT = #abs_type (#1 info)
    val lhs_tfrees = map dest_TFree (snd (dest_Type newT))

    val RepC = Const (Rep_name, newT --> oldT)
    val below_eqn = Logic.mk_equals (below_const newT,
      Abs ("x", newT, Abs ("y", newT, below_const oldT $ (RepC $ Bound 1) $ (RepC $ Bound 0))))
    val ((_, (_, below_ldef)), lthy) = thy
      |> Class.instantiation ([full_tname], lhs_tfrees, @{sort po})
      |> Specification.definition (NONE,
          ((Binding.prefix_name "below_" (Thm.def_binding name), []), below_eqn))
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
    val below_def = singleton (Proof_Context.export lthy ctxt_thy) below_ldef
    val thy = lthy
      |> Class.prove_instantiation_exit
          (K (Tactic.rtac (@{thm typedef_po} OF [type_definition, below_def]) 1))
  in ((info, below_def), thy) end

fun prepare_cpodef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ: binding * (string * sort) list * mixfix)
      (raw_set: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : term * term * (thm -> thm -> theory -> (Typedef.info * cpo_info) * theory) =
  let
    val (newT, oldT, set, morphs) =
      prepare prep_term name typ raw_set opt_morphs thy

    val goal_nonempty =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)))
    val goal_admissible =
      HOLogic.mk_Trueprop (mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)))

    fun cpodef_result nonempty admissible thy =
      let
        val ((info as (_, {type_definition, set_def, ...}), below_def), thy) = thy
          |> add_podef def (SOME name) typ set opt_morphs (Tactic.rtac nonempty 1)
        val (cpo_info, thy) = thy
          |> prove_cpo name newT morphs type_definition set_def below_def admissible
      in
        ((info, cpo_info), thy)
      end
  in
    (goal_nonempty, goal_admissible, cpodef_result)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in cpodef " ^ Binding.print name)

fun prepare_pcpodef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ: binding * (string * sort) list * mixfix)
      (raw_set: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : term * term * (thm -> thm -> theory -> (Typedef.info * cpo_info * pcpo_info) * theory) =
  let
    val (newT, oldT, set, morphs) =
      prepare prep_term name typ raw_set opt_morphs thy

    val goal_bottom_mem =
      HOLogic.mk_Trueprop (HOLogic.mk_mem (Const (@{const_name bottom}, oldT), set))

    val goal_admissible =
      HOLogic.mk_Trueprop (mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)))

    fun pcpodef_result bottom_mem admissible thy =
      let
        val tac = Tactic.rtac exI 1 THEN Tactic.rtac bottom_mem 1
        val ((info as (_, {type_definition, set_def, ...}), below_def), thy) = thy
          |> add_podef def (SOME name) typ set opt_morphs tac
        val (cpo_info, thy) = thy
          |> prove_cpo name newT morphs type_definition set_def below_def admissible
        val (pcpo_info, thy) = thy
          |> prove_pcpo name newT morphs type_definition set_def below_def bottom_mem
      in
        ((info, cpo_info, pcpo_info), thy)
      end
  in
    (goal_bottom_mem, goal_admissible, pcpodef_result)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in pcpodef " ^ Binding.print name)


(* tactic interface *)

fun add_cpodef def opt_name typ set opt_morphs (tac1, tac2) thy =
  let
    val name = the_default (#1 typ) opt_name
    val (goal1, goal2, cpodef_result) =
      prepare_cpodef Syntax.check_term def name typ set opt_morphs thy
    val thm1 = Goal.prove_global thy [] [] goal1 (K tac1)
      handle ERROR msg => cat_error msg
        ("Failed to prove non-emptiness of " ^ quote (Syntax.string_of_term_global thy set))
    val thm2 = Goal.prove_global thy [] [] goal2 (K tac2)
      handle ERROR msg => cat_error msg
        ("Failed to prove admissibility of " ^ quote (Syntax.string_of_term_global thy set))
  in cpodef_result thm1 thm2 thy end

fun add_pcpodef def opt_name typ set opt_morphs (tac1, tac2) thy =
  let
    val name = the_default (#1 typ) opt_name
    val (goal1, goal2, pcpodef_result) =
      prepare_pcpodef Syntax.check_term def name typ set opt_morphs thy
    val thm1 = Goal.prove_global thy [] [] goal1 (K tac1)
      handle ERROR msg => cat_error msg
        ("Failed to prove non-emptiness of " ^ quote (Syntax.string_of_term_global thy set))
    val thm2 = Goal.prove_global thy [] [] goal2 (K tac2)
      handle ERROR msg => cat_error msg
        ("Failed to prove admissibility of " ^ quote (Syntax.string_of_term_global thy set))
  in pcpodef_result thm1 thm2 thy end


(* proof interface *)

local

fun gen_cpodef_proof prep_term prep_constraint
    ((def, name), (b, raw_args, mx), set, opt_morphs) thy =
  let
    val ctxt = Proof_Context.init_global thy
    val args = map (apsnd (prep_constraint ctxt)) raw_args
    val (goal1, goal2, make_result) =
      prepare_cpodef prep_term def name (b, args, mx) set opt_morphs thy
    fun after_qed [[th1, th2]] = Proof_Context.background_theory (snd o make_result th1 th2)
      | after_qed _ = raise Fail "cpodef_proof"
  in Proof.theorem NONE after_qed [[(goal1, []), (goal2, [])]] ctxt end

fun gen_pcpodef_proof prep_term prep_constraint
    ((def, name), (b, raw_args, mx), set, opt_morphs) thy =
  let
    val ctxt = Proof_Context.init_global thy
    val args = map (apsnd (prep_constraint ctxt)) raw_args
    val (goal1, goal2, make_result) =
      prepare_pcpodef prep_term def name (b, args, mx) set opt_morphs thy
    fun after_qed [[th1, th2]] = Proof_Context.background_theory (snd o make_result th1 th2)
      | after_qed _ = raise Fail "pcpodef_proof"
  in Proof.theorem NONE after_qed [[(goal1, []), (goal2, [])]] ctxt end

in

fun cpodef_proof x = gen_cpodef_proof Syntax.check_term (K I) x
fun cpodef_proof_cmd x = gen_cpodef_proof Syntax.read_term Typedecl.read_constraint x

fun pcpodef_proof x = gen_pcpodef_proof Syntax.check_term (K I) x
fun pcpodef_proof_cmd x = gen_pcpodef_proof Syntax.read_term Typedecl.read_constraint x

end



(** outer syntax **)

val typedef_proof_decl =
  Scan.optional (@{keyword "("} |--
      ((@{keyword "open"} >> K false) -- Scan.option Parse.binding ||
        Parse.binding >> (fn s => (true, SOME s)))
        --| @{keyword ")"}) (true, NONE) --
    (Parse.type_args_constrained -- Parse.binding) -- Parse.opt_mixfix --
    (@{keyword "="} |-- Parse.term) --
    Scan.option (@{keyword "morphisms"} |-- Parse.!!! (Parse.binding -- Parse.binding))

fun mk_pcpodef_proof pcpo ((((((def, opt_name), (args, t)), mx), A), morphs)) =
  (if pcpo then pcpodef_proof_cmd else cpodef_proof_cmd)
    ((def, the_default t opt_name), (t, args, mx), A, morphs)

val _ =
  Outer_Syntax.command @{command_spec "pcpodef"}
    "HOLCF type definition (requires admissibility proof)"
    (typedef_proof_decl >>
      (Toplevel.print oo (Toplevel.theory_to_proof o mk_pcpodef_proof true)))

val _ =
  Outer_Syntax.command @{command_spec "cpodef"}
    "HOLCF type definition (requires admissibility proof)"
    (typedef_proof_decl >>
      (Toplevel.print oo (Toplevel.theory_to_proof o mk_pcpodef_proof false)))

end
