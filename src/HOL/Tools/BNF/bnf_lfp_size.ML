(*  Title:      HOL/Tools/BNF/bnf_lfp_size.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Generation of size functions for new-style datatypes.
*)

structure BNF_LFP_Size : sig end =
struct

open BNF_Util
open BNF_Def
open BNF_FP_Def_Sugar

val size_N = "size_"

val sizeN = "size"
val size_mapN = "size_map"

structure Data = Theory_Data
(
  type T = (string * (thm list * thm list)) Symtab.table;
  val empty = Symtab.empty;
  val extend = I
  fun merge data = Symtab.merge (K true) data;
);

val zero_nat = @{const zero_class.zero (nat)};

fun mk_plus_nat (t1, t2) = Const (@{const_name Groups.plus},
  HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t1 $ t2;

fun mk_to_natT T = T --> HOLogic.natT;

fun mk_abs_zero_nat T = Term.absdummy T zero_nat;

fun generate_size (fp_sugars as ({T = Type (_, As), BT = Type (_, Bs),
    fp_res = {bnfs = fp_bnfs, ...}, common_co_inducts = common_inducts, ...} : fp_sugar) :: _) thy =
  let
    val data = Data.get thy;

    val Ts = map #T fp_sugars
    val T_names = map (fst o dest_Type) Ts;
    val nn = length Ts;

    val B_ify = Term.typ_subst_atomic (As ~~ Bs);

    val recs = map #co_rec fp_sugars;
    val rec_thmss = map #co_rec_thms fp_sugars;
    val rec_Ts = map fastype_of recs;
    val Cs = map body_type rec_Ts;
    val Cs_rho = map (rpair HOLogic.natT) Cs;
    val substCT = Term.subst_atomic_types Cs_rho;

    val f_Ts = map mk_to_natT As;
    val f_TsB = map mk_to_natT Bs;
    val num_As = length As;

    val f_names = map (prefix "f" o string_of_int) (1 upto num_As);
    val fs = map2 (curry Free) f_names f_Ts;
    val fsB = map2 (curry Free) f_names f_TsB;
    val As_fs = As ~~ fs;

    val gen_size_names = map (Long_Name.map_base_name (prefix size_N)) T_names;

    fun is_pair_C @{type_name prod} [_, T'] = member (op =) Cs T'
      | is_pair_C _ _ = false;

    fun mk_size_of_typ (T as TFree _) =
        pair (case AList.lookup (op =) As_fs T of
            SOME f => f
          | NONE => if member (op =) Cs T then Term.absdummy T (Bound 0) else mk_abs_zero_nat T)
      | mk_size_of_typ (T as Type (s, Ts)) =
        if is_pair_C s Ts then
          pair (snd_const T)
        else if exists (exists_subtype_in As) Ts then
          (case Symtab.lookup data s of
            SOME (gen_size_name, (_, gen_size_maps)) =>
            let
              val (args, gen_size_mapss') = split_list (map (fn T => mk_size_of_typ T []) Ts);
              val gen_size_const = Const (gen_size_name, map fastype_of args ---> mk_to_natT T);
            in
              fold (union Thm.eq_thm) (gen_size_maps :: gen_size_mapss')
              #> pair (Term.list_comb (gen_size_const, args))
            end
          | NONE => pair (mk_abs_zero_nat T))
        else
          pair (mk_abs_zero_nat T);

    fun mk_size_of_arg t =
      mk_size_of_typ (fastype_of t) #>> (fn s => substCT (betapply (s, t)));

    fun mk_gen_size_arg arg_T gen_size_maps =
      let
        val x_Ts = binder_types arg_T;
        val m = length x_Ts;
        val x_names = map (prefix "x" o string_of_int) (1 upto m);
        val xs = map2 (curry Free) x_names x_Ts;
        val (summands, gen_size_maps') =
          fold_map mk_size_of_arg xs gen_size_maps
          |>> remove (op =) zero_nat;
        val sum =
          if null summands then HOLogic.zero
          else foldl1 mk_plus_nat (summands @ [HOLogic.Suc_zero]);
      in
        (fold_rev Term.lambda (map substCT xs) sum, gen_size_maps')
      end;

    fun mk_gen_size_rhs rec_T recx gen_size_maps =
      let
        val arg_Ts = binder_fun_types rec_T;
        val (args, gen_size_maps') = fold_map mk_gen_size_arg arg_Ts gen_size_maps;
      in
        (fold_rev Term.lambda fs (Term.list_comb (substCT recx, args)), gen_size_maps')
      end;

    fun mk_def_binding f = Binding.conceal o Binding.name o Thm.def_name o f o Long_Name.base_name;

    val (gen_size_rhss, nested_gen_size_maps) = fold_map2 mk_gen_size_rhs rec_Ts recs [];
    val gen_size_Ts = map fastype_of gen_size_rhss;
    val gen_size_consts = map2 (curry Const) gen_size_names gen_size_Ts;
    val gen_size_constsB = map (Term.map_types B_ify) gen_size_consts;
    val gen_size_def_bs = map (mk_def_binding I) gen_size_names;

    val (gen_size_defs, thy2) =
      thy
      |> Sign.add_consts (map (fn (s, T) => (Binding.name (Long_Name.base_name s), T, NoSyn))
        (gen_size_names ~~ gen_size_Ts))
      |> Global_Theory.add_defs false (map Thm.no_attributes (gen_size_def_bs ~~
        map Logic.mk_equals (gen_size_consts ~~ gen_size_rhss)));

    val zeros = map mk_abs_zero_nat As;

    val spec_size_rhss = map (fn c => Term.list_comb (c, zeros)) gen_size_consts;
    val spec_size_Ts = map fastype_of spec_size_rhss;
    val spec_size_consts = map (curry Const @{const_name size}) spec_size_Ts;
    val spec_size_def_bs = map (mk_def_binding (suffix "_overloaded")) gen_size_names;

    fun define_spec_size def_b lhs0 rhs lthy =
      let
        val Free (c, _) = Syntax.check_term lthy lhs0;
        val (thm, lthy') = lthy
          |> Local_Theory.define ((Binding.name c, NoSyn), ((def_b, []), rhs))
          |-> (fn (t, (_, thm)) => Spec_Rules.add Spec_Rules.Equational ([t], [thm]) #> pair thm);
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
        val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm;
      in (thm', lthy') end;

    val (spec_size_defs, thy3) = thy2
      |> Class.instantiation (T_names, map dest_TFree As, [HOLogic.class_size])
      |> fold_map3 define_spec_size spec_size_def_bs spec_size_consts spec_size_rhss
      ||> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      ||> Local_Theory.exit_global;

    val thy3_ctxt = Proof_Context.init_global thy3;

    val gen_size_defs' =
      map (mk_unabs_def (num_As + 1) o (fn thm => thm RS meta_eq_to_obj_eq)) gen_size_defs;
    val spec_size_defs' =
      map (mk_unabs_def 1 o (fn thm => thm RS meta_eq_to_obj_eq)) spec_size_defs;

    fun derive_size_simp unfolds folds size_def' simp0 =
      fold_thms thy3_ctxt folds (unfold_thms thy3_ctxt unfolds (trans OF [size_def', simp0]));
    val derive_gen_size_simp =
      derive_size_simp (@{thm snd_o_convol} :: nested_gen_size_maps) gen_size_defs';
    val derive_spec_size_simp = derive_size_simp @{thms add_0_left add_0_right} spec_size_defs';

    val gen_size_simpss = map2 (map o derive_gen_size_simp) gen_size_defs' rec_thmss;
    val gen_size_simps = flat gen_size_simpss;
    val spec_size_simpss = map2 (map o derive_spec_size_simp) spec_size_defs' gen_size_simpss;

    val ABs = As ~~ Bs;
    val g_names = map (prefix "g" o string_of_int) (1 upto num_As);
    val gs = map2 (curry Free) g_names (map (op -->) ABs);

    val liveness = map (op <>) ABs;
    val live_gs = AList.find (op =) (gs ~~ liveness) true;
    val live = length live_gs;

    val u_names = map (prefix "u" o string_of_int) (1 upto nn);
    val us = map2 (curry Free) u_names Ts;

    val maps0 = map map_of_bnf fp_bnfs;
    val map_thms = maps #maps fp_sugars;

    fun mk_gen_size_map_tac ctxt =
      HEADGOAL (rtac (co_induct_of common_inducts)) THEN
      ALLGOALS (asm_simp_tac (ss_only (o_apply :: map_thms @ gen_size_simps) ctxt));

    val gen_size_map_thmss =
      if live = 0 then
        replicate nn []
      else if null nested_gen_size_maps then
        let
          val xgmaps =
            map2 (fn map0 => fn u => Term.list_comb (mk_map live As Bs map0, live_gs) $ u) maps0 us;
          val fsizes =
            map (fn gen_size_constB => Term.list_comb (gen_size_constB, fsB)) gen_size_constsB;
          val lhss = map2 (curry (op $)) fsizes xgmaps;

          val fgs = map2 (fn fB => fn g as Free (_, Type (_, [A, B])) =>
            if A = B then fB else HOLogic.mk_comp (fB, g)) fsB gs;
          val rhss = map2 (fn gen_size_const => fn u => Term.list_comb (gen_size_const, fgs) $ u)
            gen_size_consts us;

          val goal = Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) lhss rhss)
            |> HOLogic.mk_Trueprop;
        in
          Goal.prove_global thy3 [] [] goal (mk_gen_size_map_tac o #context)
          |> Thm.close_derivation
          |> conj_dests nn
          |> map single
        end
      else
        (* TODO: implement general case, with nesting of datatypes that themselves nest other
           types *)
        replicate nn [];

    val (_, thy4) = thy3
      |> fold_map3 (fn T_name => fn size_simps => fn gen_size_map_thms =>
          let val qualify = Binding.qualify true (Long_Name.base_name T_name) in
            Global_Theory.note_thmss ""
              ([((qualify (Binding.name sizeN),
                   [Simplifier.simp_add, Nitpick_Simps.add, Thm.declaration_attribute
                      (fn thm => Context.mapping (Code.add_default_eqn thm) I)]),
                 [(size_simps, [])]),
                ((qualify (Binding.name size_mapN), []), [(gen_size_map_thms, [])])]
               |> filter_out (forall (null o fst) o snd))
          end)
        T_names (map2 append gen_size_simpss spec_size_simpss) gen_size_map_thmss
      ||> Spec_Rules.add_global Spec_Rules.Equational (gen_size_consts, gen_size_simps);
  in
    thy4
    |> Data.map (fold2 (fn T_name => fn gen_size_name =>
        Symtab.update_new (T_name, (gen_size_name, (gen_size_simps, flat gen_size_map_thmss))))
      T_names gen_size_names)
  end;

(* FIXME: get rid of "perhaps o try" once the code is stable *)
val _ = Theory.setup (fp_sugar_interpretation (perhaps o try o generate_size));

end;
