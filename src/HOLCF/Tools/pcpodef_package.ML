(*  Title:      HOLCF/Tools/pcpodef_package.ML
    Author:     Brian Huffman

Primitive domain definitions for HOLCF, similar to Gordon/HOL-style
typedef (see also ~~/src/HOL/Tools/typedef_package.ML).
*)

signature PCPODEF_PACKAGE =
sig
  val pcpodef_proof: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
  val pcpodef_proof_cmd: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
  val cpodef_proof: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
  val cpodef_proof_cmd: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
end;

structure PcpodefPackage: PCPODEF_PACKAGE =
struct

(** type definitions **)

(* prepare_cpodef *)

fun err_in_cpodef msg name =
  cat_error msg ("The error(s) above occurred in cpodef " ^ quote name);

fun declare_type_name a = Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

fun adm_const T = Const (@{const_name adm}, (T --> HOLogic.boolT) --> HOLogic.boolT);
fun mk_adm (x, T, P) = adm_const T $ absfree (x, T, P);

fun prepare_pcpodef prep_term pcpo def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Pcpodef" "pcpodefs";
    val ctxt = ProofContext.init thy;
    val full = Sign.full_bname thy;

    (*rhs*)
    val full_name = full name;
    val set = prep_term (ctxt |> fold declare_type_name vs) raw_set;
    val setT = Term.fastype_of set;
    val rhs_tfrees = Term.add_tfrees set [];
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ ctxt setT));

    (*goal*)
    val goal_UU_mem = HOLogic.mk_mem (Const (@{const_name UU}, oldT), set);
    val goal_nonempty = HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set));
    val goal_admissible = mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), set));
    val goal = HOLogic.mk_Trueprop
      (HOLogic.mk_conj (if pcpo then goal_UU_mem else goal_nonempty, goal_admissible));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val lhs_sorts = map snd lhs_tfrees;

    val tname = Syntax.type_name t mx;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) = the_default ("Rep_" ^ name, "Abs_" ^ name) opt_morphs;
    val RepC = Const (full Rep_name, newT --> oldT);
    fun lessC T = Const (@{const_name sq_le}, T --> T --> HOLogic.boolT);
    val less_def = Logic.mk_equals (lessC newT,
      Abs ("x", newT, Abs ("y", newT, lessC oldT $ (RepC $ Bound 1) $ (RepC $ Bound 0))));

    fun make_po tac thy1 =
      let
        val ((_, {type_definition, set_def, ...}), thy2) = thy1
          |> TypedefPackage.add_typedef def (SOME name) (t, vs, mx) set opt_morphs tac;
        val lthy3 = thy2
          |> TheoryTarget.instantiation ([full_tname], lhs_tfrees, @{sort po});
        val less_def' = Syntax.check_term lthy3 less_def;
        val ((_, (_, less_definition')), lthy4) = lthy3
          |> Specification.definition (NONE, ((Binding.name ("less_" ^ name ^ "_def"), []), less_def'));
        val ctxt_thy = ProofContext.init (ProofContext.theory_of lthy4);
        val less_definition = singleton (ProofContext.export lthy4 ctxt_thy) less_definition';
        val thy5 = lthy4
          |> Class.prove_instantiation_instance
              (K (Tactic.rtac (@{thm typedef_po} OF [type_definition, less_definition]) 1))
          |> LocalTheory.exit_global;
      in ((type_definition, less_definition, set_def), thy5) end;

    fun make_cpo admissible (type_def, less_def, set_def) theory =
      let
        val admissible' = fold_rule (the_list set_def) admissible;
        val cpo_thms = map (Thm.transfer theory) [type_def, less_def, admissible'];
        val theory' = theory
          |> AxClass.prove_arity (full_tname, lhs_sorts, @{sort cpo})
            (Tactic.rtac (@{thm typedef_cpo} OF cpo_thms) 1);
        val cpo_thms' = map (Thm.transfer theory') cpo_thms;
      in
        theory'
        |> Sign.add_path name
        |> PureThy.add_thms
          ([(("adm_" ^ name, admissible'), []),
            (("cont_" ^ Rep_name, @{thm typedef_cont_Rep} OF cpo_thms'), []),
            (("cont_" ^ Abs_name, @{thm typedef_cont_Abs} OF cpo_thms'), []),
            (("lub_" ^ name, @{thm typedef_lub} OF cpo_thms'), []),
            (("thelub_" ^ name, @{thm typedef_thelub} OF cpo_thms'), []),
            (("compact_" ^ name, @{thm typedef_compact} OF cpo_thms'), [])])
        |> snd
        |> Sign.parent_path
      end;

    fun make_pcpo UUmem (type_def, less_def, set_def) theory =
      let
        val UUmem' = fold_rule (the_list set_def) UUmem;
        val pcpo_thms = map (Thm.transfer theory) [type_def, less_def, UUmem'];
        val theory' = theory
          |> AxClass.prove_arity (full_tname, lhs_sorts, @{sort pcpo})
            (Tactic.rtac (@{thm typedef_pcpo} OF pcpo_thms) 1);
        val pcpo_thms' = map (Thm.transfer theory') pcpo_thms;
      in
        theory'
        |> Sign.add_path name
        |> PureThy.add_thms
            ([((Rep_name ^ "_strict", @{thm typedef_Rep_strict} OF pcpo_thms'), []),
              ((Abs_name ^ "_strict", @{thm typedef_Abs_strict} OF pcpo_thms'), []),
              ((Rep_name ^ "_strict_iff", @{thm typedef_Rep_strict_iff} OF pcpo_thms'), []),
              ((Abs_name ^ "_strict_iff", @{thm typedef_Abs_strict_iff} OF pcpo_thms'), []),
              ((Rep_name ^ "_defined", @{thm typedef_Rep_defined} OF pcpo_thms'), []),
              ((Abs_name ^ "_defined", @{thm typedef_Abs_defined} OF pcpo_thms'), [])
              ])
        |> snd
        |> Sign.parent_path
      end;

    fun pcpodef_result UUmem_admissible theory =
      let
        val UUmem = UUmem_admissible RS conjunct1;
        val admissible = UUmem_admissible RS conjunct2;
      in
        theory
        |> make_po (Tactic.rtac exI 1 THEN Tactic.rtac UUmem 1)
        |-> (fn defs => make_cpo admissible defs #> make_pcpo UUmem defs)
      end;

    fun cpodef_result nonempty_admissible theory =
      let
        val nonempty = nonempty_admissible RS conjunct1;
        val admissible = nonempty_admissible RS conjunct2;
      in
        theory
        |> make_po (Tactic.rtac nonempty 1)
        |-> make_cpo admissible
      end;

  in (goal, if pcpo then pcpodef_result else cpodef_result) end
  handle ERROR msg => err_in_cpodef msg name;


(* proof interface *)

local

fun gen_pcpodef_proof prep_term pcpo ((def, name), typ, set, opt_morphs) thy =
  let
    val (goal, pcpodef_result) =
      prepare_pcpodef prep_term pcpo def name typ set opt_morphs thy;
    fun after_qed [[th]] = ProofContext.theory (pcpodef_result th);
  in Proof.theorem_i NONE after_qed [[(goal, [])]] (ProofContext.init thy) end;

in

fun pcpodef_proof x = gen_pcpodef_proof Syntax.check_term true x;
fun pcpodef_proof_cmd x = gen_pcpodef_proof Syntax.read_term true x;

fun cpodef_proof x = gen_pcpodef_proof Syntax.check_term false x;
fun cpodef_proof_cmd x = gen_pcpodef_proof Syntax.read_term false x;

end;



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val typedef_proof_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.name || P.name >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.name -- P.name));

fun mk_pcpodef_proof pcpo ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  (if pcpo then pcpodef_proof_cmd else cpodef_proof_cmd)
    ((def, the_default (Syntax.type_name t mx) opt_name), (t, vs, mx), A, morphs);

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
