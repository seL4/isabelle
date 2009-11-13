(*  Title:      HOLCF/Tools/pcpodef.ML
    Author:     Brian Huffman

Primitive domain definitions for HOLCF, similar to Gordon/HOL-style
typedef (see also ~~/src/HOL/Tools/typedef.ML).
*)

signature PCPODEF =
sig
  type cpo_info =
    { below_def: thm, adm: thm, cont_Rep: thm, cont_Abs: thm,
      lub: thm, thelub: thm, compact: thm }
  type pcpo_info =
    { Rep_strict: thm, Abs_strict: thm, Rep_strict_iff: thm, Abs_strict_iff: thm,
      Rep_defined: thm, Abs_defined: thm }

  val add_podef: bool -> binding option -> binding * string list * mixfix ->
    term -> (binding * binding) option -> tactic -> theory ->
    (Typedef.info * thm) * theory
  val add_cpodef: bool -> binding option -> binding * string list * mixfix ->
    term -> (binding * binding) option -> tactic * tactic -> theory ->
    (Typedef.info * cpo_info) * theory
  val add_pcpodef: bool -> binding option -> binding * string list * mixfix ->
    term -> (binding * binding) option -> tactic * tactic -> theory ->
    (Typedef.info * cpo_info * pcpo_info) * theory

  val cpodef_proof: (bool * binding) * (binding * string list * mixfix) * term
    * (binding * binding) option -> theory -> Proof.state
  val cpodef_proof_cmd: (bool * binding) * (binding * string list * mixfix) * string
    * (binding * binding) option -> theory -> Proof.state
  val pcpodef_proof: (bool * binding) * (binding * string list * mixfix) * term
    * (binding * binding) option -> theory -> Proof.state
  val pcpodef_proof_cmd: (bool * binding) * (binding * string list * mixfix) * string
    * (binding * binding) option -> theory -> Proof.state
end;

structure Pcpodef :> PCPODEF =
struct

(** type definitions **)

type cpo_info =
  { below_def: thm, adm: thm, cont_Rep: thm, cont_Abs: thm,
    lub: thm, thelub: thm, compact: thm }

type pcpo_info =
  { Rep_strict: thm, Abs_strict: thm, Rep_strict_iff: thm, Abs_strict_iff: thm,
    Rep_defined: thm, Abs_defined: thm }

(* building terms *)

fun adm_const T = Const (@{const_name adm}, (T --> HOLogic.boolT) --> HOLogic.boolT);
fun mk_adm (x, T, P) = adm_const T $ absfree (x, T, P);

fun below_const T = Const (@{const_name below}, T --> T --> HOLogic.boolT);

(* manipulating theorems *)

fun fold_adm_mem thm NONE = thm
  | fold_adm_mem thm (SOME set_def) =
    let val rule = @{lemma "A == B ==> adm (%x. x : B) ==> adm (%x. x : A)" by simp}
    in rule OF [set_def, thm] end;

fun fold_UU_mem thm NONE = thm
  | fold_UU_mem thm (SOME set_def) =
    let val rule = @{lemma "A == B ==> UU : B ==> UU : A" by simp}
    in rule OF [set_def, thm] end;

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
    val admissible' = fold_adm_mem admissible set_def;
    val cpo_thms = map (Thm.transfer thy) [type_definition, below_def, admissible'];
    val (full_tname, Ts) = dest_Type newT;
    val lhs_sorts = map (snd o dest_TFree) Ts;
    val thy2 =
      thy
      |> AxClass.prove_arity (full_tname, lhs_sorts, @{sort cpo})
          (Tactic.rtac (@{thm typedef_cpo} OF cpo_thms) 1);
    val cpo_thms' = map (Thm.transfer thy2) cpo_thms;
    fun make thm = Drule.standard (thm OF cpo_thms');
    val ([adm, cont_Rep, cont_Abs, lub, thelub, compact], thy3) =
      thy2
      |> Sign.add_path (Binding.name_of name)
      |> PureThy.add_thms
        ([((Binding.prefix_name "adm_" name, admissible'), []),
          ((Binding.prefix_name "cont_" Rep_name, make @{thm typedef_cont_Rep}), []),
          ((Binding.prefix_name "cont_" Abs_name, make @{thm typedef_cont_Abs}), []),
          ((Binding.prefix_name "lub_" name, make @{thm typedef_lub}), []),
          ((Binding.prefix_name "thelub_" name, make @{thm typedef_thelub}), []),
          ((Binding.prefix_name "compact_" name, make @{thm typedef_compact}), [])])
      ||> Sign.parent_path;
    val cpo_info : cpo_info =
      { below_def = below_def, adm = admissible', cont_Rep = cont_Rep,
        cont_Abs = cont_Abs, lub = lub, thelub = thelub, compact = compact };
  in
    (cpo_info, thy3)
  end;

fun prove_pcpo
      (name: binding)
      (newT: typ)
      (Rep_name: binding, Abs_name: binding)
      (type_definition: thm)  (* type_definition Rep Abs A *)
      (set_def: thm option)   (* A == set *)
      (below_def: thm)        (* op << == %x y. Rep x << Rep y *)
      (UU_mem: thm)           (* UU : set *)
      (thy: theory)
    =
  let
    val UU_mem' = fold_UU_mem UU_mem set_def;
    val pcpo_thms = map (Thm.transfer thy) [type_definition, below_def, UU_mem'];
    val (full_tname, Ts) = dest_Type newT;
    val lhs_sorts = map (snd o dest_TFree) Ts;
    val thy2 = thy
      |> AxClass.prove_arity (full_tname, lhs_sorts, @{sort pcpo})
        (Tactic.rtac (@{thm typedef_pcpo} OF pcpo_thms) 1);
    val pcpo_thms' = map (Thm.transfer thy2) pcpo_thms;
    fun make thm = Drule.standard (thm OF pcpo_thms');
    val ([Rep_strict, Abs_strict, Rep_strict_iff, Abs_strict_iff,
          Rep_defined, Abs_defined], thy3) =
      thy2
      |> Sign.add_path (Binding.name_of name)
      |> PureThy.add_thms
        ([((Binding.suffix_name "_strict" Rep_name, make @{thm typedef_Rep_strict}), []),
          ((Binding.suffix_name "_strict" Abs_name, make @{thm typedef_Abs_strict}), []),
          ((Binding.suffix_name "_strict_iff" Rep_name, make @{thm typedef_Rep_strict_iff}), []),
          ((Binding.suffix_name "_strict_iff" Abs_name, make @{thm typedef_Abs_strict_iff}), []),
          ((Binding.suffix_name "_defined" Rep_name, make @{thm typedef_Rep_defined}), []),
          ((Binding.suffix_name "_defined" Abs_name, make @{thm typedef_Abs_defined}), [])])
      ||> Sign.parent_path;
    val pcpo_info =
      { Rep_strict = Rep_strict, Abs_strict = Abs_strict,
        Rep_strict_iff = Rep_strict_iff, Abs_strict_iff = Abs_strict_iff,
        Rep_defined = Rep_defined, Abs_defined = Abs_defined };
  in
    (pcpo_info, thy3)
  end;

(* prepare_cpodef *)

fun declare_type_name a =
  Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

fun prepare prep_term _ name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Pcpodef" "pcpodefs";
    val ctxt = ProofContext.init thy;

    (*rhs*)
    val set = prep_term (ctxt |> fold declare_type_name vs) raw_set;
    val setT = Term.fastype_of set;
    val rhs_tfrees = Term.add_tfrees set [];
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ ctxt setT));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val lhs_sorts = map snd lhs_tfrees;
    val tname = Binding.map_name (Syntax.type_name mx) t;
    val full_tname = Sign.full_name thy tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val morphs = opt_morphs
      |> the_default (Binding.prefix_name "Rep_" name, Binding.prefix_name "Abs_" name);
  in
    (newT, oldT, set, morphs, lhs_sorts)
  end

fun add_podef def opt_name typ set opt_morphs tac thy =
  let
    val name = the_default (#1 typ) opt_name;
    val ((full_tname, info as {type_definition, set_def, Rep_name, ...}), thy2) = thy
      |> Typedef.add_typedef def opt_name typ set opt_morphs tac;
    val oldT = #rep_type info;
    val newT = #abs_type info;
    val lhs_tfrees = map dest_TFree (snd (dest_Type newT));

    val RepC = Const (Rep_name, newT --> oldT);
    val below_def = Logic.mk_equals (below_const newT,
      Abs ("x", newT, Abs ("y", newT, below_const oldT $ (RepC $ Bound 1) $ (RepC $ Bound 0))));
    val lthy3 = thy2
      |> Theory_Target.instantiation ([full_tname], lhs_tfrees, @{sort po});
    val below_def' = Syntax.check_term lthy3 below_def;
    val ((_, (_, below_definition')), lthy4) = lthy3
      |> Specification.definition (NONE,
          ((Binding.prefix_name "below_" (Binding.suffix_name "_def" name), []), below_def'));
    val ctxt_thy = ProofContext.init (ProofContext.theory_of lthy4);
    val below_definition = singleton (ProofContext.export lthy4 ctxt_thy) below_definition';
    val thy5 = lthy4
      |> Class.prove_instantiation_instance
          (K (Tactic.rtac (@{thm typedef_po} OF [type_definition, below_definition]) 1))
      |> Local_Theory.exit_global;
  in ((info, below_definition), thy5) end;

fun prepare_cpodef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ: binding * string list * mixfix)
      (raw_set: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : term * term * (thm -> thm -> theory -> (Typedef.info * cpo_info) * theory) =
  let
    val (newT, oldT, set, morphs as (Rep_name, Abs_name), lhs_sorts) =
      prepare prep_term def name typ raw_set opt_morphs thy;

    val goal_nonempty =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)));
    val goal_admissible =
      HOLogic.mk_Trueprop (mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)));

    fun cpodef_result nonempty admissible thy =
      let
        val ((info as {type_definition, set_def, ...}, below_def), thy2) = thy
          |> add_podef def (SOME name) typ set opt_morphs (Tactic.rtac nonempty 1);
        val (cpo_info, thy3) = thy2
          |> prove_cpo name newT morphs type_definition set_def below_def admissible;
      in
        ((info, cpo_info), thy3)
      end;
  in
    (goal_nonempty, goal_admissible, cpodef_result)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in cpodef " ^ quote (Binding.str_of name));

fun prepare_pcpodef
      (prep_term: Proof.context -> 'a -> term)
      (def: bool)
      (name: binding)
      (typ: binding * string list * mixfix)
      (raw_set: 'a)
      (opt_morphs: (binding * binding) option)
      (thy: theory)
    : term * term * (thm -> thm -> theory -> (Typedef.info * cpo_info * pcpo_info) * theory) =
  let
    val (newT, oldT, set, morphs as (Rep_name, Abs_name), lhs_sorts) =
      prepare prep_term def name typ raw_set opt_morphs thy;

    val goal_UU_mem =
      HOLogic.mk_Trueprop (HOLogic.mk_mem (Const (@{const_name UU}, oldT), set));

    val goal_admissible =
      HOLogic.mk_Trueprop (mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set)));

    fun pcpodef_result UU_mem admissible thy =
      let
        val tac = Tactic.rtac exI 1 THEN Tactic.rtac UU_mem 1;
        val ((info as {type_definition, set_def, ...}, below_def), thy2) = thy
          |> add_podef def (SOME name) typ set opt_morphs tac;
        val (cpo_info, thy3) = thy2
          |> prove_cpo name newT morphs type_definition set_def below_def admissible;
        val (pcpo_info, thy4) = thy3
          |> prove_pcpo name newT morphs type_definition set_def below_def UU_mem;
      in
        ((info, cpo_info, pcpo_info), thy4)
      end;
  in
    (goal_UU_mem, goal_admissible, pcpodef_result)
  end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in pcpodef " ^ quote (Binding.str_of name));


(* tactic interface *)

fun add_cpodef def opt_name typ set opt_morphs (tac1, tac2) thy =
  let
    val name = the_default (#1 typ) opt_name;
    val (goal1, goal2, cpodef_result) =
      prepare_cpodef Syntax.check_term def name typ set opt_morphs thy;
    val thm1 = Goal.prove_global thy [] [] goal1 (K tac1)
      handle ERROR msg => cat_error msg
        ("Failed to prove non-emptiness of " ^ quote (Syntax.string_of_term_global thy set));
    val thm2 = Goal.prove_global thy [] [] goal2 (K tac2)
      handle ERROR msg => cat_error msg
        ("Failed to prove admissibility of " ^ quote (Syntax.string_of_term_global thy set));
  in cpodef_result thm1 thm2 thy end;

fun add_pcpodef def opt_name typ set opt_morphs (tac1, tac2) thy =
  let
    val name = the_default (#1 typ) opt_name;
    val (goal1, goal2, pcpodef_result) =
      prepare_pcpodef Syntax.check_term def name typ set opt_morphs thy;
    val thm1 = Goal.prove_global thy [] [] goal1 (K tac1)
      handle ERROR msg => cat_error msg
        ("Failed to prove non-emptiness of " ^ quote (Syntax.string_of_term_global thy set));
    val thm2 = Goal.prove_global thy [] [] goal2 (K tac2)
      handle ERROR msg => cat_error msg
        ("Failed to prove admissibility of " ^ quote (Syntax.string_of_term_global thy set));
  in pcpodef_result thm1 thm2 thy end;


(* proof interface *)

local

fun gen_cpodef_proof prep_term ((def, name), typ, set, opt_morphs) thy =
  let
    val (goal1, goal2, make_result) =
      prepare_cpodef prep_term def name typ set opt_morphs thy;
    fun after_qed [[th1, th2]] = ProofContext.theory (snd o make_result th1 th2);
  in Proof.theorem_i NONE after_qed [[(goal1, []), (goal2, [])]] (ProofContext.init thy) end;

fun gen_pcpodef_proof prep_term ((def, name), typ, set, opt_morphs) thy =
  let
    val (goal1, goal2, make_result) =
      prepare_pcpodef prep_term def name typ set opt_morphs thy;
    fun after_qed [[th1, th2]] = ProofContext.theory (snd o make_result th1 th2);
  in Proof.theorem_i NONE after_qed [[(goal1, []), (goal2, [])]] (ProofContext.init thy) end;

in

fun cpodef_proof x = gen_cpodef_proof Syntax.check_term x;
fun cpodef_proof_cmd x = gen_cpodef_proof Syntax.read_term x;

fun pcpodef_proof x = gen_pcpodef_proof Syntax.check_term x;
fun pcpodef_proof_cmd x = gen_pcpodef_proof Syntax.read_term x;

end;



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val typedef_proof_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.binding || P.binding >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.binding) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.binding -- P.binding));

fun mk_pcpodef_proof pcpo ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  (if pcpo then pcpodef_proof_cmd else cpodef_proof_cmd)
    ((def, the_default (Binding.map_name (Syntax.type_name mx) t) opt_name), (t, vs, mx), A, morphs);

val _ =
  OuterSyntax.command "pcpodef" "HOLCF type definition (requires admissibility proof)" K.thy_goal
    (typedef_proof_decl >>
      (Toplevel.print oo (Toplevel.theory_to_proof o mk_pcpodef_proof true)));

val _ =
  OuterSyntax.command "cpodef" "HOLCF type definition (requires admissibility proof)" K.thy_goal
    (typedef_proof_decl >>
      (Toplevel.print oo (Toplevel.theory_to_proof o mk_pcpodef_proof false)));

end;

end;
