(*  Title:      HOL/Tools/Datatype/datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val setup: theory -> theory
end;

structure Datatype_Codegen : DATATYPE_CODEGEN =
struct

(** generic code generator **)

(* liberal addition of code data for datatypes *)

fun mk_constr_consts thy vs tyco cos =
  let
    val cs = map (fn (c, tys) => (c, tys ---> Type (tyco, map TFree vs))) cos;
    val cs' = map (fn c_ty as (_, ty) => (AxClass.unoverload_const thy c_ty, ty)) cs;
  in
    if is_some (try (Code.constrset_of_consts thy) cs')
    then SOME cs
    else NONE
  end;


(* case certificates *)

fun mk_case_cert thy tyco =
  let
    val raw_thms = #case_rewrites (Datatype_Data.the_info thy tyco);
    val thms as hd_thm :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify_global
      |> Conjunction.elim_balanced (length raw_thms)
      |> map Simpdata.mk_meta_eq
      |> map Drule.zero_var_indexes;
    val params = fold_aterms (fn (Free (v, _)) => insert (op =) v | _ => I) (Thm.prop_of hd_thm) [];
    val rhs = hd_thm
      |> Thm.prop_of
      |> Logic.dest_equals
      |> fst
      |> Term.strip_comb
      |> apsnd (fst o split_last)
      |> list_comb;
    val lhs = Free (singleton (Name.variant_list params) "case", Term.fastype_of rhs);
    val asm = Thm.cterm_of thy (Logic.mk_equals (lhs, rhs));
  in
    thms
    |> Conjunction.intr_balanced
    |> Raw_Simplifier.rewrite_rule [Thm.symmetric (Thm.assume asm)]
    |> Thm.implies_intr asm
    |> Thm.generalize ([], params) 0
    |> AxClass.unoverload thy
    |> Thm.varifyT_global
  end;


(* equality *)

fun mk_eq_eqns thy tyco =
  let
    val (vs, cos) = Datatype_Data.the_spec thy tyco;
    val {descr, index, inject = inject_thms, distinct = distinct_thms, ...} =
      Datatype_Data.the_info thy tyco;
    val ty = Type (tyco, map TFree vs);
    fun mk_eq (t1, t2) = Const (@{const_name HOL.equal}, ty --> ty --> HOLogic.boolT) $ t1 $ t2;
    fun true_eq t12 = HOLogic.mk_eq (mk_eq t12, HOLogic.true_const);
    fun false_eq t12 = HOLogic.mk_eq (mk_eq t12, HOLogic.false_const);
    val triv_injects =
      map_filter
        (fn (c, []) => SOME (HOLogic.mk_Trueprop (true_eq (Const (c, ty), Const (c, ty))))
          | _ => NONE) cos;
    fun prep_inject (trueprop $ (equiv $ (_ $ t1 $ t2) $ rhs)) =
      trueprop $ (equiv $ mk_eq (t1, t2) $ rhs);
    val injects = map prep_inject (nth (Datatype_Prop.make_injs [descr] vs) index);
    fun prep_distinct (trueprop $ (not $ (_ $ t1 $ t2))) =
      [trueprop $ false_eq (t1, t2), trueprop $ false_eq (t2, t1)];
    val distincts =
      maps prep_distinct (snd (nth (Datatype_Prop.make_distincts [descr] vs) index));
    val refl = HOLogic.mk_Trueprop (true_eq (Free ("x", ty), Free ("x", ty)));
    val simpset =
      Simplifier.global_context thy
        (HOL_basic_ss addsimps
          (map Simpdata.mk_eq (@{thms equal eq_True} @ inject_thms @ distinct_thms)));
    fun prove prop =
      Skip_Proof.prove_global thy [] [] prop (K (ALLGOALS (simp_tac simpset)))
      |> Simpdata.mk_eq;
  in (map prove (triv_injects @ injects @ distincts), prove refl) end;

fun add_equality vs tycos thy =
  let
    fun add_def tyco lthy =
      let
        val ty = Type (tyco, map TFree vs);
        fun mk_side const_name =
          Const (const_name, ty --> ty --> HOLogic.boolT) $ Free ("x", ty) $ Free ("y", ty);
        val def =
          HOLogic.mk_Trueprop (HOLogic.mk_eq
            (mk_side @{const_name HOL.equal}, mk_side @{const_name HOL.eq}));
        val def' = Syntax.check_term lthy def;
        val ((_, (_, thm)), lthy') =
          Specification.definition (NONE, (Attrib.empty_binding, def')) lthy;
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy);
        val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm;
      in (thm', lthy') end;
    fun tac thms = Class.intro_classes_tac [] THEN ALLGOALS (Proof_Context.fact_tac thms);
    fun prefix tyco =
      Binding.qualify true (Long_Name.base_name tyco) o Binding.qualify true "eq" o Binding.name;
    fun add_eq_thms tyco =
      Theory.checkpoint
      #> `(fn thy => mk_eq_eqns thy tyco)
      #-> (fn (thms, thm) =>
        Global_Theory.note_thmss Thm.lemmaK
          [((prefix tyco "refl", [Code.add_nbe_default_eqn_attribute]), [([thm], [])]),
            ((prefix tyco "simps", [Code.add_default_eqn_attribute]), [(rev thms, [])])])
      #> snd;
  in
    thy
    |> Class.instantiation (tycos, vs, [HOLogic.class_equal])
    |> fold_map add_def tycos
    |-> (fn def_thms => Class.prove_instantiation_exit_result (map o Morphism.thm)
         (fn _ => fn def_thms => tac def_thms) def_thms)
    |-> (fn def_thms => fold Code.del_eqn def_thms)
    |> fold add_eq_thms tycos
  end;


(* register a datatype etc. *)

fun add_all_code config tycos thy =
  let
    val (vs :: _, coss) = split_list (map (Datatype_Data.the_spec thy) tycos);
    val any_css = map2 (mk_constr_consts thy vs) tycos coss;
    val css = if exists is_none any_css then [] else map_filter I any_css;
    val case_rewrites = maps (#case_rewrites o Datatype_Data.the_info thy) tycos;
    val certs = map (mk_case_cert thy) tycos;
    val tycos_eq =
      filter_out
        (fn tyco => can (Sorts.mg_domain (Sign.classes_of thy) tyco) [HOLogic.class_equal]) tycos;
  in
    if null css then thy
    else
      thy
      |> tap (fn _ => Datatype_Aux.message config "Registering datatype for code generator ...")
      |> fold Code.add_datatype css
      |> fold_rev Code.add_default_eqn case_rewrites
      |> fold Code.add_case certs
      |> not (null tycos_eq) ? add_equality vs tycos_eq
   end;


(** theory setup **)

val setup = Datatype_Data.interpretation add_all_code;

end;
