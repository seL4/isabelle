(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_specialisation.ML
    Author:     Lukas Bulwahn, TU Muenchen

Deriving specialised predicates and their intro rules
*)

signature PREDICATE_COMPILE_SPECIALISATION =
sig
  val find_specialisations : string list -> (string * thm list) list ->
    theory -> (string * thm list) list * theory
end;

structure Predicate_Compile_Specialisation : PREDICATE_COMPILE_SPECIALISATION =
struct

open Predicate_Compile_Aux;

(* table of specialisations *)
structure Specialisations = Theory_Data
(
  type T = (term * term) Item_Net.T
  val empty : T = Item_Net.init (op aconv o apply2 fst) (single o fst)
  val merge = Item_Net.merge
)

fun specialisation_of thy atom =
  Item_Net.retrieve (Specialisations.get thy) atom

fun import (_, intros) args ctxt =
  let
    val ((_, intros'), ctxt') = Variable.importT intros ctxt
    val pred' =
      fst (strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl (Thm.prop_of (hd intros')))))
    val Ts = binder_types (fastype_of pred')
    val argTs = map fastype_of args
    val Tsubst = Type.raw_matches (argTs, Ts) Vartab.empty
    val args' = map (Envir.subst_term_types Tsubst) args
  in
    (((pred', intros'), args'), ctxt')
  end

(* patterns only constructed of variables and pairs/tuples are trivial constructor terms*)
fun is_nontrivial_constrt ctxt t =
  let
    val lookup_constr = lookup_constr ctxt
    fun check t =
      (case strip_comb t of
        (Var _, []) => (true, true)
      | (Free _, []) => (true, true)
      | (Const (\<^const_name>\<open>Pair\<close>, _), ts) =>
        apply2 (forall I) (split_list (map check ts))
      | (Const cT, ts) =>
          (case lookup_constr cT of
            SOME i => (false,
              length ts = i andalso forall (snd o check) ts)
          | _ => (false, false))
      | _ => (false, false))
  in check t = (false, true) end

fun specialise_intros black_list (pred, intros) pats thy =
  let
    val ctxt = Proof_Context.init_global thy
    val maxidx = fold (Term.maxidx_term o Thm.prop_of) intros ~1
    val pats = map (Logic.incr_indexes ([], maxidx + 1)) pats
    val (((pred, intros), pats), ctxt') = import (pred, intros) pats ctxt
    val result_pats = map Var (fold_rev Term.add_vars pats [])
    fun mk_fresh_name names =
      let
        val name =
          singleton (Name.variant_list names)
            ("specialised_" ^ Long_Name.base_name (dest_Const_name pred))
        val bname = Sign.full_bname thy name
      in
        if Sign.declared_const thy bname then
          mk_fresh_name (name :: names)
        else
          bname
      end
    val constname = mk_fresh_name []
    val constT = map fastype_of result_pats ---> \<^typ>\<open>bool\<close>
    val specialised_const = Const (constname, constT)
    fun specialise_intro intro =
      (let
        val (prems, concl) = Logic.strip_horn (Thm.prop_of intro)
        val env = Pattern.unify (Context.Theory thy)
          (HOLogic.mk_Trueprop (list_comb (pred, pats)), concl) Envir.init
        val prems = map (Envir.norm_term env) prems
        val args = map (Envir.norm_term env) result_pats
        val concl = HOLogic.mk_Trueprop (list_comb (specialised_const, args))
        val intro = Logic.list_implies (prems, concl)
      in
        SOME intro
      end handle Pattern.Unif => NONE)
    val specialised_intros_t = map_filter I (map specialise_intro intros)
    val thy' =
      Sign.add_consts [(Binding.name (Long_Name.base_name constname), constT, NoSyn)] thy
    val specialised_intros = map (Skip_Proof.make_thm thy') specialised_intros_t
    val exported_intros = Variable.exportT ctxt' ctxt specialised_intros
    val [t, specialised_t] = Variable.exportT_terms ctxt' ctxt
      [list_comb (pred, pats), list_comb (specialised_const, result_pats)]
    val thy'' = Specialisations.map (Item_Net.update (t, specialised_t)) thy'
    val optimised_intros =
      map_filter (Predicate_Compile_Aux.peephole_optimisation thy'') exported_intros
    val ([spec], thy''') = find_specialisations black_list [(constname, optimised_intros)] thy''
    val thy'''' = Core_Data.register_intros spec thy'''
  in
    thy''''
  end

and find_specialisations black_list specs thy =
  let
    val ctxt = Proof_Context.init_global thy
    val add_vars = fold_aterms (fn Var v => cons v | _ => I);
    fun fresh_free T free_names =
      let
        val free_name = singleton (Name.variant_list free_names) "x"
      in
        (Free (free_name, T), free_name :: free_names)
      end
    fun replace_term_and_restrict thy T t Tts free_names =
      let
        val (free, free_names') = fresh_free T free_names
        val Tts' = map (apsnd (Pattern.rewrite_term thy [(t, free)] [])) Tts
        val (ts', free_names'') = restrict_pattern' thy Tts' free_names'
      in
        (free :: ts', free_names'')
      end
    and restrict_pattern' thy [] free_names = ([], free_names)
      | restrict_pattern' thy ((T, Free (x, _)) :: Tts) free_names =
          let
            val (ts', free_names') = restrict_pattern' thy Tts free_names
          in
            (Free (x, T) :: ts', free_names')
          end
      | restrict_pattern' thy ((T as TFree _, t) :: Tts) free_names =
          replace_term_and_restrict thy T t Tts free_names
      | restrict_pattern' thy ((T as Type (Tcon, _), t) :: Tts) free_names =
        case Ctr_Sugar.ctr_sugar_of ctxt Tcon of
          NONE => replace_term_and_restrict thy T t Tts free_names
        | SOME {ctrs, ...} =>
          (case strip_comb t of
            (Const (s, _), ats) =>
              (case AList.lookup (op =) (map_filter (try dest_Const) ctrs) s of
                SOME constr_T =>
                  let
                    val (Ts', T') = strip_type constr_T
                    val Tsubst = Type.raw_match (T', T) Vartab.empty
                    val Ts = map (Envir.subst_type Tsubst) Ts'
                    val (bts', free_names') = restrict_pattern' thy ((Ts ~~ ats) @ Tts) free_names
                    val (ats', ts') = chop (length ats) bts'
                  in
                    (list_comb (Const (s, map fastype_of ats' ---> T), ats') :: ts', free_names')
                  end
              | NONE => replace_term_and_restrict thy T t Tts free_names))
    fun restrict_pattern thy Ts args =
      let
        val args = map Logic.unvarify_global args
        val Ts = map Logic.unvarifyT_global Ts
        val free_names = fold Term.add_free_names args []
        val (pat, _) = restrict_pattern' thy (Ts ~~ args) free_names
      in map Logic.varify_global pat end
    fun detect' atom thy =
      (case strip_comb atom of
        (pred as Const (pred_name, _), args) =>
          let
            val Ts = binder_types (Sign.the_const_type thy pred_name)
            val pats = restrict_pattern thy Ts args
          in
            if (exists (is_nontrivial_constrt ctxt) pats)
              orelse (has_duplicates (op =) (fold add_vars pats [])) then
              let
                val thy' =
                  (case specialisation_of thy atom of
                    [] =>
                      if member (op =) ((map fst specs) @ black_list) pred_name then
                        thy
                      else
                        (case try (Core_Data.intros_of (Proof_Context.init_global thy)) pred_name of
                          NONE => thy
                        | SOME [] => thy
                        | SOME intros =>
                            specialise_intros ((map fst specs) @ (pred_name :: black_list))
                              (pred, intros) pats thy)
                  | _ :: _ => thy)
                val atom' =
                  (case specialisation_of thy' atom of
                    [] => atom
                  | (t, specialised_t) :: _ =>
                    let
                      val subst = Pattern.match thy' (t, atom) (Vartab.empty, Vartab.empty)
                    in Envir.subst_term subst specialised_t end handle Pattern.MATCH => atom)
                    (*FIXME: this exception could be handled earlier in specialisation_of *)
              in
                (atom', thy')
              end
            else (atom, thy)
          end
      | _ => (atom, thy))
    fun specialise' (constname, intros) thy =
      let
        (* FIXME: only necessary because of sloppy Logic.unvarify in restrict_pattern *)
        val intros = Drule.zero_var_indexes_list intros
        val (intros_t', thy') = (fold_map o fold_map_atoms) detect' (map Thm.prop_of intros) thy
      in
        ((constname, map (Skip_Proof.make_thm thy') intros_t'), thy')
      end
  in
    fold_map specialise' specs thy
  end

end
