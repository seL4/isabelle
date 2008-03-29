(*  Title:      HOLCF/Tools/pcpodef_package.ML
    ID:         $Id$
    Author:     Brian Huffman

Primitive domain definitions for HOLCF, similar to Gordon/HOL-style
typedef.
*)

signature PCPODEF_PACKAGE =
sig
  val pcpodef_proof: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
  val pcpodef_proof_i: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
  val cpodef_proof: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
  val cpodef_proof_i: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
end;

structure PcpodefPackage: PCPODEF_PACKAGE =
struct

(** theory context references **)

val typedef_po = thm "typedef_po";
val typedef_cpo = thm "typedef_cpo";
val typedef_pcpo = thm "typedef_pcpo";
val typedef_lub = thm "typedef_lub";
val typedef_thelub = thm "typedef_thelub";
val typedef_compact = thm "typedef_compact";
val cont_Rep = thm "typedef_cont_Rep";
val cont_Abs = thm "typedef_cont_Abs";
val Rep_strict = thm "typedef_Rep_strict";
val Abs_strict = thm "typedef_Abs_strict";
val Rep_strict_iff = thm "typedef_Rep_strict_iff";
val Abs_strict_iff = thm "typedef_Abs_strict_iff";
val Rep_defined = thm "typedef_Rep_defined";
val Abs_defined = thm "typedef_Abs_defined";


(** type definitions **)

(* prepare_cpodef *)

fun err_in_cpodef msg name =
  cat_error msg ("The error(s) above occurred in cpodef " ^ quote name);

fun declare_type_name a = Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

fun adm_const T = Const ("Adm.adm", (T --> HOLogic.boolT) --> HOLogic.boolT);
fun mk_adm (x, T, P) = adm_const T $ absfree (x, T, P);

fun prepare_pcpodef prep_term pcpo def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val ctxt = ProofContext.init thy;
    val full = Sign.full_name thy;

    (*rhs*)
    val full_name = full name;
    val set = prep_term (ctxt |> fold declare_type_name vs) raw_set;
    val setT = Term.fastype_of set;
    val rhs_tfrees = term_tfrees set;
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ ctxt setT));
    fun mk_nonempty A =
      HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A));
    fun mk_admissible A =
      mk_adm ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A));
    fun mk_UU_mem A = HOLogic.mk_mem (Const ("Pcpo.UU", oldT), A);
    val goal = if pcpo
      then HOLogic.mk_Trueprop (HOLogic.mk_conj (mk_UU_mem set, mk_admissible set))
      else HOLogic.mk_Trueprop (HOLogic.mk_conj (mk_nonempty set, mk_admissible set));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val lhs_sorts = map snd lhs_tfrees;
    val tname = Syntax.type_name t mx;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) = the_default ("Rep_" ^ name, "Abs_" ^ name) opt_morphs;
    val RepC = Const (full Rep_name, newT --> oldT);
    fun lessC T = Const (@{const_name Porder.sq_le}, T --> T --> HOLogic.boolT);
    val less_def = ("less_" ^ name ^ "_def", Logic.mk_equals (lessC newT,
      Abs ("x", newT, Abs ("y", newT, lessC oldT $ (RepC $ Bound 1) $ (RepC $ Bound 0)))));

    fun make_po tac theory = theory
      |> TypedefPackage.add_typedef_i def (SOME name) (t, vs, mx) set opt_morphs tac
      ||> AxClass.prove_arity (full_tname, lhs_sorts, ["Porder.sq_ord"])
           (Class.intro_classes_tac [])
      ||>> PureThy.add_defs_i true [Thm.no_attributes less_def]
      |-> (fn ((_, {type_definition, set_def, ...}), [less_definition]) =>
          AxClass.prove_arity (full_tname, lhs_sorts, ["Porder.po"])
             (Tactic.rtac (typedef_po OF [type_definition, less_definition]) 1)
           #> pair (type_definition, less_definition, set_def));

    fun make_cpo admissible (type_def, less_def, set_def) theory =
      let
        val admissible' = fold_rule (the_list set_def) admissible;
        val cpo_thms = [type_def, less_def, admissible'];
      in
        theory
        |> AxClass.prove_arity (full_tname, lhs_sorts, ["Pcpo.cpo"])
          (Tactic.rtac (typedef_cpo OF cpo_thms) 1)
        |> Sign.add_path name
        |> PureThy.add_thms
            ([(("adm_" ^ name, admissible'), []),
              (("cont_" ^ Rep_name, cont_Rep OF cpo_thms), []),
              (("cont_" ^ Abs_name, cont_Abs OF cpo_thms), []),
              (("lub_"     ^ name, typedef_lub     OF cpo_thms), []),
              (("thelub_"  ^ name, typedef_thelub  OF cpo_thms), []),
              (("compact_" ^ name, typedef_compact OF cpo_thms), [])])
        |> snd
        |> Sign.parent_path
      end;

    fun make_pcpo UUmem (type_def, less_def, set_def) theory =
      let
        val UUmem' = fold_rule (the_list set_def) UUmem;
        val pcpo_thms = [type_def, less_def, UUmem'];
      in
        theory
        |> AxClass.prove_arity (full_tname, lhs_sorts, ["Pcpo.pcpo"])
          (Tactic.rtac (typedef_pcpo OF pcpo_thms) 1)
        |> Sign.add_path name
        |> PureThy.add_thms
            ([((Rep_name ^ "_strict", Rep_strict OF pcpo_thms), []),
              ((Abs_name ^ "_strict", Abs_strict OF pcpo_thms), []),
              ((Rep_name ^ "_strict_iff", Rep_strict_iff OF pcpo_thms), []),
              ((Abs_name ^ "_strict_iff", Abs_strict_iff OF pcpo_thms), []),
              ((Rep_name ^ "_defined", Rep_defined OF pcpo_thms), []),
              ((Abs_name ^ "_defined", Abs_defined OF pcpo_thms), [])
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


(* cpodef_proof interface *)

fun gen_pcpodef_proof prep_term pcpo ((def, name), typ, set, opt_morphs) thy =
  let
    val (goal, pcpodef_result) =
      prepare_pcpodef prep_term pcpo def name typ set opt_morphs thy;
    fun after_qed [[th]] = ProofContext.theory (pcpodef_result th);
  in Proof.theorem_i NONE after_qed [[(goal, [])]] (ProofContext.init thy) end;

fun pcpodef_proof x = gen_pcpodef_proof Syntax.read_term true x;
fun pcpodef_proof_i x = gen_pcpodef_proof Syntax.check_term true x;

fun cpodef_proof x = gen_pcpodef_proof Syntax.read_term false x;
fun cpodef_proof_i x = gen_pcpodef_proof Syntax.check_term false x;


(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

(* cf. HOL/Tools/typedef_package.ML *)
val typedef_proof_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.name || P.name >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.name -- P.name));

fun mk_pcpodef_proof pcpo ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  (if pcpo then pcpodef_proof else cpodef_proof)
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
