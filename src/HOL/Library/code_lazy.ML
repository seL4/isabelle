(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

signature CODE_LAZY =
sig
  type lazy_info =
    {eagerT: typ,
     lazyT: typ,
     ctr: term,
     destr: term,
     lazy_ctrs: term list,
     case_lazy: term,
     active: bool,
     activate: theory -> theory,
     deactivate: theory -> theory};
  val code_lazy_type: string -> theory -> theory
  val activate_lazy_type: string -> theory -> theory
  val deactivate_lazy_type: string -> theory -> theory
  val activate_lazy_types: theory -> theory
  val deactivate_lazy_types: theory -> theory

  val get_lazy_types: theory -> (string * lazy_info) list

  val print_lazy_types: theory -> unit

  val transform_code_eqs: Proof.context -> (thm * bool) list -> (thm * bool) list option
end;

structure Code_Lazy : CODE_LAZY =
struct

type lazy_info =
  {eagerT: typ,
   lazyT: typ,
   ctr: term,
   destr: term,
   lazy_ctrs: term list,
   case_lazy: term,
   active: bool,
   activate: theory -> theory,
   deactivate: theory -> theory};

fun map_active f {eagerT, lazyT, ctr, destr, lazy_ctrs, case_lazy, active, activate, deactivate} =
  { eagerT = eagerT, 
    lazyT = lazyT,
    ctr = ctr,
    destr = destr,
    lazy_ctrs = lazy_ctrs,
    case_lazy = case_lazy,
    active = f active,
    activate = activate,
    deactivate = deactivate
  }

structure Laziness_Data = Theory_Data(
  type T = lazy_info Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.join (fn _ => fn (_, record) => record);
  val extend = I;
);

fun fold_type type' tfree tvar typ =
  let
    fun go (Type (s, Ts)) = type' (s, map go Ts)
      | go (TFree T) = tfree T
      | go (TVar T) = tvar T
  in
    go typ
  end;

fun read_typ lthy name =
  let
    val (s, Ts) = Proof_Context.read_type_name {proper = true, strict = true} lthy name |> dest_Type
    val (Ts', _) = Ctr_Sugar_Util.mk_TFrees (length Ts) lthy
  in 
    Type (s, Ts')
  end

fun mk_name prefix suffix name ctxt =
  Ctr_Sugar_Util.mk_fresh_names ctxt 1 (prefix ^ name ^ suffix) |>> hd;
fun generate_typedef_name name ctxt = mk_name "" "_lazy" name ctxt;

fun add_syntax_definition short_type_name eagerT lazyT lazy_ctr lthy = 
  let
    val (name, _) = mk_name "lazy_" "" short_type_name lthy
    val freeT = HOLogic.unitT --> lazyT
    val lazyT' = Type (\<^type_name>\<open>lazy\<close>, [lazyT])
    val def = Logic.all_const freeT $ absdummy freeT (Logic.mk_equals (
      Free (name, (freeT --> eagerT)) $ Bound 0,
      lazy_ctr $ (Const (\<^const_name>\<open>delay\<close>, (freeT --> lazyT')) $ Bound 0)))
    val lthy' = (snd o Local_Theory.begin_nested) lthy
    val ((t, (_, thm)), lthy') = Specification.definition NONE [] [] 
      ((Thm.def_binding (Binding.name name), []), def) lthy'
    val lthy' = Local_Theory.notation true ("", false) [(t, Mixfix.mixfix "_")] lthy'
    val lthy = Local_Theory.end_nested lthy'
    val def_thm = singleton (Proof_Context.export lthy' lthy) thm
  in
    (def_thm, lthy)
  end;

fun add_ctr_code raw_ctrs case_thms thy =
  let
    fun mk_case_certificate ctxt raw_thms =
      let
        val thms = raw_thms
          |> Conjunction.intr_balanced
          |> Thm.unvarify_global (Proof_Context.theory_of ctxt)
          |> Conjunction.elim_balanced (length raw_thms)
          |> map Simpdata.mk_meta_eq
          |> map Drule.zero_var_indexes
        val thm1 = case thms of
          thm :: _ => thm
          | _ => raise Empty
        val params = Term.add_free_names (Thm.prop_of thm1) [];
        val rhs = thm1
          |> Thm.prop_of |> Logic.dest_equals |> fst |> strip_comb
          ||> fst o split_last |> list_comb
        val lhs = Free (singleton (Name.variant_list params) "case", fastype_of rhs);
        val assum = Thm.cterm_of ctxt (Logic.mk_equals (lhs, rhs))
      in
        thms
        |> Conjunction.intr_balanced
        |> rewrite_rule ctxt [Thm.symmetric (Thm.assume assum)]
        |> Thm.implies_intr assum
        |> Thm.generalize (Names.empty, Names.make_set params) 0
        |> Axclass.unoverload ctxt
        |> Thm.varifyT_global
      end
    val ctrs = map (apsnd (perhaps (try Logic.unvarifyT_global))) raw_ctrs
    val unover_ctrs = map (fn ctr as (_, fcT) => (Axclass.unoverload_const thy ctr, fcT)) ctrs
  in
    if can (Code.constrset_of_consts thy) unover_ctrs then
      thy
      |> Code.declare_datatype_global ctrs
      |> fold_rev (Code.add_eqn_global o rpair true) case_thms
      |> Code.declare_case_global (mk_case_certificate (Proof_Context.init_global thy) case_thms)
    else
      thy
  end;

fun not_found s = error (s ^ " has not been added as lazy type");

fun validate_type_name thy type_name =
  let
    val lthy = Named_Target.theory_init thy
    val eager_type = read_typ lthy type_name
    val type_name = case eager_type of
      Type (s, _) => s
      | _ => raise Match
  in
    type_name
  end;

fun set_active_lazy_type value eager_type_string thy =
  let
    val type_name = validate_type_name thy eager_type_string
    val x =
      case Symtab.lookup (Laziness_Data.get thy) type_name of
        NONE => not_found type_name
        | SOME x => x
    val new_x = map_active (K value) x
    val thy1 = if value = #active x
      then thy
      else if value
        then #activate x thy
        else #deactivate x thy
  in
    Laziness_Data.map (Symtab.update (type_name, new_x)) thy1
  end;

fun set_active_lazy_types value thy =
  let
    val lazy_type_names = Symtab.keys (Laziness_Data.get thy)
    fun fold_fun value type_name thy =
      let
        val x =
          case Symtab.lookup (Laziness_Data.get thy) type_name of
            SOME x => x
            | NONE => raise Match
        val new_x = map_active (K value) x
        val thy1 = if value = #active x
          then thy
          else if value
            then #activate x thy
            else #deactivate x thy
      in
        Laziness_Data.map (Symtab.update (type_name, new_x)) thy1
      end
  in
    fold (fold_fun value) lazy_type_names thy
  end;

(* code_lazy_type : string -> theory -> theory *)
fun code_lazy_type eager_type_string thy =
  let
    val lthy = Named_Target.theory_init thy
    val eagerT = read_typ lthy eager_type_string
    val (type_name, type_args) = dest_Type eagerT
    val short_type_name = Long_Name.base_name type_name
    val _ = if Symtab.defined (Laziness_Data.get thy) type_name
      then error (type_name ^ " has already been added as lazy type.")
      else ()
    val {case_thms, casex, ctrs, ...} = case Ctr_Sugar.ctr_sugar_of lthy type_name of
        SOME x => x
      | _ => error (type_name ^ " is not registered with free constructors.")

    fun substitute_ctr (old_T, new_T) ctr_T lthy =
      let
        val old_ctr_vars = map TVar (Term.add_tvarsT ctr_T [])
        val old_ctr_Ts = map TFree (Term.add_tfreesT ctr_T []) @ old_ctr_vars
        val (new_ctr_Ts, lthy') = Ctr_Sugar_Util.mk_TFrees (length old_ctr_Ts) lthy

        fun double_type_fold Ts = case Ts of
          (Type (_, Ts1), Type (_, Ts2)) => flat (map double_type_fold (Ts1 ~~ Ts2))
          | (Type _, _) => raise Match
          | (_, Type _) => raise Match
          | Ts => [Ts]
        fun map_fun1 f = List.foldr
          (fn ((T1, T2), f) => fn T => if T = T1 then T2 else f T)
          f
          (double_type_fold (old_T, new_T))
        val map_fun2 = AList.lookup (op =) (old_ctr_Ts ~~ new_ctr_Ts) #> the
        val map_fun = map_fun1 map_fun2

        val new_ctr_type = fold_type Type (map_fun o TFree) (map_fun o TVar) ctr_T
      in
        (new_ctr_type, lthy')
      end

    val (short_lazy_type_name, lthy1) = generate_typedef_name short_type_name lthy

    fun mk_lazy_typedef (name, eager_type) lthy =
      let
        val binding = Binding.name name
        val (result, lthy1) = (Typedef.add_typedef
            { overloaded=false }
            (binding, rev (Term.add_tfreesT eager_type []), Mixfix.NoSyn)
            (Const (\<^const_name>\<open>top\<close>, Type (\<^type_name>\<open>set\<close>, [eager_type])))
            NONE
            (fn ctxt => resolve_tac ctxt [@{thm UNIV_witness}] 1)
          o (snd o Local_Theory.begin_nested)) lthy
      in
         (binding, result, Local_Theory.end_nested lthy1)
      end;

    val (typedef_binding, (_, info), lthy2) = mk_lazy_typedef (short_lazy_type_name, eagerT) lthy1

    val lazy_type = Type (Local_Theory.full_name lthy2 typedef_binding, type_args)
    val (Abs_lazy, Rep_lazy) =
      let
        val info = fst info
        val Abs_name = #Abs_name info
        val Rep_name = #Rep_name info
        val Abs_type = eagerT --> lazy_type
        val Rep_type = lazy_type --> eagerT
      in
        (Const (Abs_name, Abs_type), Const (Rep_name, Rep_type))
      end
    val Abs_inverse = #Abs_inverse (snd info)
    val Rep_inverse = #Rep_inverse (snd info)

    val (ctrs', lthy3) = List.foldr
      (fn (Const (s, T), (ctrs, lthy)) => let
            val (T', lthy') = substitute_ctr (body_type T, eagerT) T lthy
          in
            ((Const (s, T')) :: ctrs, lthy')
          end
      )
      ([], lthy2)
      ctrs

    fun to_destr_eagerT typ = case typ of
          Type (\<^type_name>\<open>fun\<close>, [_, Type (\<^type_name>\<open>fun\<close>, Ts)]) => 
          to_destr_eagerT (Type (\<^type_name>\<open>fun\<close>, Ts))
        | Type (\<^type_name>\<open>fun\<close>, [T, _]) => T
        | _ => raise Match
    val (case', lthy4) = 
      let
        val (eager_case, caseT) = dest_Const casex
        val (caseT', lthy') = substitute_ctr (to_destr_eagerT caseT, eagerT) caseT lthy3
      in (Const (eager_case, caseT'), lthy') end

    val ctr_names = map (Long_Name.base_name o fst o dest_Const) ctrs
    val ((((lazy_ctr_name, lazy_sel_name), lazy_ctrs_name), lazy_case_name), ctxt) = lthy4
      |> mk_name "Lazy_" "" short_type_name
      ||>> mk_name "unlazy_" "" short_type_name
      ||>> fold_map (mk_name "" "_Lazy") ctr_names
      ||>> mk_name "case_" "_lazy" short_type_name

    fun mk_def (name, T, rhs) lthy =
      let
        val binding = Binding.name name
        val ((_, (_, thm)), lthy1) = 
          (snd o Local_Theory.begin_nested) lthy
          |> Specification.definition NONE [] [] ((Thm.def_binding binding, []), rhs)
        val lthy2 = Local_Theory.end_nested lthy1
        val def_thm = hd (Proof_Context.export lthy1 lthy2 [thm])
      in
        ({binding = binding, const = Const (Local_Theory.full_name lthy2 binding, T), thm = def_thm}, lthy2)
      end;
    
    val lazy_datatype = Type (\<^type_name>\<open>lazy\<close>, [lazy_type])
    val Lazy_type = lazy_datatype --> eagerT
    val unstr_type = eagerT --> lazy_datatype
    
    fun apply_bounds i n term =
      if n > i then apply_bounds i (n-1) (term $ Bound (n-1))
      else term
    fun all_abs Ts t = Logic.list_all (map (pair Name.uu) Ts, t)
    fun mk_force t = Const (\<^const_name>\<open>force\<close>, lazy_datatype --> lazy_type) $ t
    fun mk_delay t = Const (\<^const_name>\<open>delay\<close>, (\<^typ>\<open>unit\<close> --> lazy_type) --> lazy_datatype) $ t

    val lazy_ctr = all_abs [lazy_datatype]
      (Logic.mk_equals (Free (lazy_ctr_name, Lazy_type) $ Bound 0, Rep_lazy $ mk_force (Bound 0)))
    val (lazy_ctr_def, lthy5) = mk_def (lazy_ctr_name, Lazy_type, lazy_ctr) lthy4

    val lazy_sel = all_abs [eagerT]
      (Logic.mk_equals (Free (lazy_sel_name, unstr_type) $ Bound 0, 
        mk_delay (Abs (Name.uu, \<^typ>\<open>unit\<close>, Abs_lazy $ Bound 1))))
    val (lazy_sel_def, lthy6) = mk_def (lazy_sel_name, unstr_type, lazy_sel) lthy5

    fun mk_lazy_ctr (name, eager_ctr) =
      let
        val (_, ctrT) = dest_Const eager_ctr
        fun to_lazy_ctrT (Type (\<^type_name>\<open>fun\<close>, [T1, T2])) = T1 --> to_lazy_ctrT T2
          | to_lazy_ctrT T = if T = eagerT then lazy_type else raise Match
        val lazy_ctrT = to_lazy_ctrT ctrT
        val argsT = binder_types ctrT
        val lhs = apply_bounds 0 (length argsT) (Free (name, lazy_ctrT))
        val rhs = Abs_lazy $ apply_bounds 0 (length argsT) eager_ctr
      in
        mk_def (name, lazy_ctrT, all_abs argsT (Logic.mk_equals (lhs, rhs)))
      end
    val (lazy_ctrs_def, lthy7) = fold_map mk_lazy_ctr (lazy_ctrs_name ~~ ctrs') lthy6

    val (lazy_case_def, lthy8) =
      let
        val (_, caseT) = dest_Const case'
        fun to_lazy_caseT (Type (\<^type_name>\<open>fun\<close>, [T1, T2])) =
            if T1 = eagerT then lazy_type --> T2 else T1 --> to_lazy_caseT T2
        val lazy_caseT = to_lazy_caseT caseT
        val argsT = binder_types lazy_caseT
        val n = length argsT
        val lhs = apply_bounds 0 n (Free (lazy_case_name, lazy_caseT)) 
        val rhs = apply_bounds 1 n case' $ (Rep_lazy $ Bound 0)
      in
        mk_def (lazy_case_name, lazy_caseT, all_abs argsT (Logic.mk_equals (lhs, rhs))) lthy7
      end

    fun mk_thm ((name, term), thms) lthy =
      let
        val binding = Binding.name name
        fun tac {context, ...} = Simplifier.simp_tac
          (put_simpset HOL_basic_ss context addsimps thms)
          1
        val thm = Goal.prove lthy [] [] term tac
        val (_, lthy1) = lthy
          |> (snd o Local_Theory.begin_nested)
          |> Local_Theory.note ((binding, []), [thm])
      in
        (thm, Local_Theory.end_nested lthy1)
      end
    fun mk_thms exec_list lthy = fold_map mk_thm exec_list lthy

    val mk_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq

    val lazy_ctrs = map #const lazy_ctrs_def
    val eager_lazy_ctrs = ctrs' ~~ lazy_ctrs

    val (((((((Lazy_delay_eq_name, Rep_ctr_names), ctrs_lazy_names), force_sel_name), case_lazy_name),
      sel_lazy_name), case_ctrs_name), _) = lthy5
      |> mk_name "Lazy_" "_delay" short_type_name
      ||>> fold_map (mk_name "Rep_" "_Lazy") ctr_names
      ||>> fold_map (mk_name "" "_conv_lazy") ctr_names
      ||>> mk_name "force_unlazy_" "" short_type_name
      ||>> mk_name "case_" "_conv_lazy" short_type_name
      ||>> mk_name "Lazy_" "_inverse" short_type_name
      ||>> fold_map (mk_name ("case_" ^ short_type_name ^ "_lazy_") "") ctr_names

    val mk_Lazy_delay_eq =
      (#const lazy_ctr_def $ mk_delay (Bound 0), Rep_lazy $ (Bound 0 $ \<^Const>\<open>Unity\<close>))
      |> mk_eq |> all_abs [\<^Type>\<open>unit\<close> --> lazy_type]
    val (Lazy_delay_thm, lthy8a) = mk_thm 
      ((Lazy_delay_eq_name, mk_Lazy_delay_eq), [#thm lazy_ctr_def, @{thm force_delay}])
      lthy8

    fun mk_lazy_ctr_eq (eager_ctr, lazy_ctr) =
      let
        val (_, ctrT) = dest_Const eager_ctr
        val argsT = binder_types ctrT
        val args = length argsT
      in
        (Rep_lazy $ apply_bounds 0 args lazy_ctr, apply_bounds 0 args eager_ctr)
        |> mk_eq |> all_abs argsT
      end
    val Rep_ctr_eqs = map mk_lazy_ctr_eq eager_lazy_ctrs
    val (Rep_ctr_thms, lthy8b) = mk_thms
        ((Rep_ctr_names ~~ Rep_ctr_eqs) ~~
          (map (fn def => [#thm def, Abs_inverse, @{thm UNIV_I}]) lazy_ctrs_def)
        )
        lthy8a

    fun mk_ctrs_lazy_eq (eager_ctr, lazy_ctr) =
      let
        val argsT = dest_Const eager_ctr |> snd |> binder_types
        val n = length argsT
        val lhs = apply_bounds 0 n eager_ctr
        val rhs = #const lazy_ctr_def $ 
          (mk_delay (Abs (Name.uu, \<^typ>\<open>unit\<close>, apply_bounds 1 (n + 1) lazy_ctr)))
      in
        (lhs, rhs) |> mk_eq |> all_abs argsT
      end
    val ctrs_lazy_eq = map mk_ctrs_lazy_eq eager_lazy_ctrs 
    val (ctrs_lazy_thms, lthy8c) = mk_thms
      ((ctrs_lazy_names ~~ ctrs_lazy_eq) ~~ map (fn thm => [Lazy_delay_thm, thm]) Rep_ctr_thms)
      lthy8b

    val force_sel_eq = 
      (mk_force (#const lazy_sel_def $ Bound 0), Abs_lazy $ Bound 0)
      |> mk_eq |> all_abs [eagerT]
    val (force_sel_thm, lthy8d) = mk_thm
        ((force_sel_name, force_sel_eq), [#thm lazy_sel_def, @{thm force_delay}])
        lthy8c

    val case_lazy_eq = 
      let
        val (_, caseT) = case' |> dest_Const
        val argsT = binder_types caseT
        val n = length argsT
        val lhs = apply_bounds 0 n case'
        val rhs = apply_bounds 1 n (#const lazy_case_def) $ (mk_force (#const lazy_sel_def $ Bound 0))
      in
        (lhs, rhs) |> mk_eq |> all_abs argsT
      end
    val (case_lazy_thm, lthy8e) = mk_thm
        ((case_lazy_name, case_lazy_eq), 
        [#thm lazy_case_def, force_sel_thm, Abs_inverse, @{thm UNIV_I}])
        lthy8d

    val sel_lazy_eq =
      (#const lazy_sel_def $ (#const lazy_ctr_def $ Bound 0), Bound 0)
      |> mk_eq |> all_abs [lazy_datatype]
    val (sel_lazy_thm, lthy8f) = mk_thm
      ((sel_lazy_name, sel_lazy_eq),
      [#thm lazy_sel_def, #thm lazy_ctr_def, Rep_inverse, @{thm delay_force}])
      lthy8e

    fun mk_case_ctrs_eq (i, lazy_ctr) =
      let
        val lazy_case = #const lazy_case_def
        val (_, ctrT) = dest_Const lazy_ctr
        val ctr_argsT = binder_types ctrT
        val ctr_args_n = length ctr_argsT
        val (_, caseT) = dest_Const lazy_case
        val case_argsT = binder_types caseT

        fun n_bounds_from m n t =
          if n > 0 then n_bounds_from (m - 1) (n - 1) (t $ Bound (m - 1)) else t

        val case_argsT' = take (length case_argsT - 1) case_argsT
        val Ts = case_argsT' @ ctr_argsT
        val num_abs_types = length Ts
        val lhs = n_bounds_from num_abs_types (length case_argsT') lazy_case $
          apply_bounds 0 ctr_args_n lazy_ctr
        val rhs = apply_bounds 0 ctr_args_n (Bound (num_abs_types - i - 1))
      in
        (lhs, rhs) |> mk_eq |> all_abs Ts
      end
    val case_ctrs_eq = map_index mk_case_ctrs_eq lazy_ctrs
    val (case_ctrs_thms, lthy9) = mk_thms
        ((case_ctrs_name ~~ case_ctrs_eq) ~~
         map2 (fn thm1 => fn thm2 => [#thm lazy_case_def, thm1, thm2]) Rep_ctr_thms case_thms
        )
        lthy8f

    val (pat_def_thm, lthy10) = 
      add_syntax_definition short_type_name eagerT lazy_type (#const lazy_ctr_def) lthy9

    val add_lazy_ctrs =
      Code.declare_datatype_global [dest_Const (#const lazy_ctr_def)]
    val eager_ctrs = map (apsnd (perhaps (try Logic.unvarifyT_global)) o dest_Const) ctrs
    val add_eager_ctrs =
      fold Code.del_eqn_global ctrs_lazy_thms
      #> Code.declare_datatype_global eager_ctrs
    val add_code_eqs = fold (Code.add_eqn_global o rpair true) 
      ([case_lazy_thm, sel_lazy_thm])
    val add_lazy_ctr_thms = fold (Code.add_eqn_global o rpair true) ctrs_lazy_thms
    val add_lazy_case_thms =
      fold Code.del_eqn_global case_thms
      #> Code.add_eqn_global (case_lazy_thm, true)
    val add_eager_case_thms = Code.del_eqn_global case_lazy_thm
      #> fold (Code.add_eqn_global o rpair true) case_thms

    val delay_dummy_thm = (pat_def_thm RS @{thm symmetric})
      |> Drule.infer_instantiate' lthy10
         [SOME (Thm.cterm_of lthy10 (Const (\<^const_name>\<open>Pure.dummy_pattern\<close>, HOLogic.unitT --> lazy_type)))]
      |> Thm.generalize
         (Names.make_set (map (fst o dest_TFree) type_args), Names.empty)
         (Variable.maxidx_of lthy10 + 1);

    val ctr_post = delay_dummy_thm :: map (fn thm => thm RS @{thm sym}) ctrs_lazy_thms
    val ctr_thms_abs = map (fn thm => Drule.abs_def (thm RS @{thm eq_reflection})) ctrs_lazy_thms
    val case_thm_abs = Drule.abs_def (case_lazy_thm RS @{thm eq_reflection})
    val add_simps = Code_Preproc.map_pre
      (fn ctxt => ctxt addsimps (case_thm_abs :: ctr_thms_abs))
    val del_simps = Code_Preproc.map_pre
      (fn ctxt => ctxt delsimps (case_thm_abs :: ctr_thms_abs))
    val add_post = Code_Preproc.map_post
      (fn ctxt => ctxt addsimps ctr_post)
    val del_post = Code_Preproc.map_post
      (fn ctxt => ctxt delsimps ctr_post)
  in
    Local_Theory.exit_global lthy10
    |> Laziness_Data.map (Symtab.update (type_name,
      {eagerT = eagerT, 
       lazyT = lazy_type,
       ctr = #const lazy_ctr_def,
       destr = #const lazy_sel_def,
       lazy_ctrs = map #const lazy_ctrs_def,
       case_lazy = #const lazy_case_def,
       active = true,
       activate = add_lazy_ctrs #> add_lazy_ctr_thms #> add_lazy_case_thms #> add_simps #> add_post,
       deactivate = add_eager_ctrs #> add_eager_case_thms #> del_simps #> del_post}))
    |> add_lazy_ctrs
    |> add_ctr_code (map (dest_Const o #const) lazy_ctrs_def) case_ctrs_thms
    |> add_code_eqs
    |> add_lazy_ctr_thms
    |> add_simps
    |> add_post
  end;

fun transform_code_eqs _ [] = NONE
  | transform_code_eqs ctxt eqs =
    let
      fun replace_ctr ctxt =
        let 
          val thy = Proof_Context.theory_of ctxt
          val table = Laziness_Data.get thy
        in fn (s1, s2) => case Symtab.lookup table s1 of
            NONE => false
          | SOME x => #active x andalso s2 <> (#ctr x |> dest_Const |> fst)
        end
      val thy = Proof_Context.theory_of ctxt
      val table = Laziness_Data.get thy
      fun num_consts_fun (_, T) =
        let
          val s = body_type T |> dest_Type |> fst
        in
          if Symtab.defined table s
          then Ctr_Sugar.ctr_sugar_of ctxt s |> the |> #ctrs |> length
          else Code.get_type thy s |> fst |> snd |> length
        end
      val eqs = map (apfst (Thm.transfer thy)) eqs;

      val ((code_eqs, nbe_eqs), pure) =
        ((case hd eqs |> fst |> Thm.prop_of of
            Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
              (map (apfst (fn x => x RS @{thm meta_eq_to_obj_eq})) eqs, true)
         | _ => (eqs, false))
        |> apfst (List.partition snd))
        handle THM _ => (([], eqs), false)
      val to_original_eq = if pure then map (apfst (fn x => x RS @{thm eq_reflection})) else I
    in
      case Case_Converter.to_case ctxt (Case_Converter.replace_by_type replace_ctr) num_consts_fun (map fst code_eqs) of
          NONE => NONE
        | SOME thms => SOME (nbe_eqs @ map (rpair true) thms |> to_original_eq)
    end

val activate_lazy_type = set_active_lazy_type true;
val deactivate_lazy_type = set_active_lazy_type false;
val activate_lazy_types = set_active_lazy_types true;
val deactivate_lazy_types = set_active_lazy_types false;

fun get_lazy_types thy = Symtab.dest (Laziness_Data.get thy) 

fun print_lazy_type thy (name, info : lazy_info) = 
  let
    val ctxt = Proof_Context.init_global thy
    fun pretty_ctr ctr = 
      let
        val argsT = dest_Const ctr |> snd |> binder_types
      in
        Pretty.block [
          Syntax.pretty_term ctxt ctr,
          Pretty.brk 1,
          Pretty.block (Pretty.separate "" (map (Pretty.quote o Syntax.pretty_typ ctxt) argsT))
        ]
      end
  in
    Pretty.block [
      Pretty.str (name ^ (if #active info then "" else " (inactive)") ^ ":"),
      Pretty.brk 1,
      Pretty.block [
        Syntax.pretty_typ ctxt (#eagerT info),
        Pretty.brk 1,
        Pretty.str "=",
        Pretty.brk 1,
        Syntax.pretty_term ctxt (#ctr info),
        Pretty.brk 1,
        Pretty.block [
          Pretty.str "(",
          Syntax.pretty_term ctxt (#destr info),
          Pretty.str ":",
          Pretty.brk 1,
          Syntax.pretty_typ ctxt (Type (\<^type_name>\<open>lazy\<close>, [#lazyT info])),
          Pretty.str ")"
        ]
      ],
      Pretty.fbrk,
      Pretty.keyword2 "and",
      Pretty.brk 1,
      Pretty.block ([
        Syntax.pretty_typ ctxt (#lazyT info),
        Pretty.brk 1,
        Pretty.str "=",
        Pretty.brk 1] @
        Pretty.separate " |" (map pretty_ctr (#lazy_ctrs info)) @ [
        Pretty.fbrk,
        Pretty.keyword2 "for",
        Pretty.brk 1, 
        Pretty.str "case:",
        Pretty.brk 1,
        Syntax.pretty_term ctxt (#case_lazy info)
      ])
    ]
  end;

fun print_lazy_types thy = 
  let
    fun cmp ((name1, _), (name2, _)) = string_ord (name1, name2)
    val infos = Laziness_Data.get thy |> Symtab.dest |> map (apfst Long_Name.base_name) |> sort cmp
  in
    Pretty.writeln_chunks (map (print_lazy_type thy) infos)
  end;


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_lazy_type\<close>
    "make a lazy copy of the datatype and activate substitution"
    (Parse.binding >> (fn b => Toplevel.theory (Binding.name_of b |> code_lazy_type)));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>activate_lazy_type\<close>
    "activate substitution on a specific (lazy) type"
    (Parse.binding >> (fn b => Toplevel.theory (Binding.name_of b |> activate_lazy_type)));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>deactivate_lazy_type\<close>
    "deactivate substitution on a specific (lazy) type"
    (Parse.binding >> (fn b => Toplevel.theory (Binding.name_of b |> deactivate_lazy_type)));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>activate_lazy_types\<close>
    "activate substitution on all (lazy) types"
    (pair (Toplevel.theory activate_lazy_types));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>deactivate_lazy_types\<close>
    "deactivate substitution on all (lazy) type"
    (pair (Toplevel.theory deactivate_lazy_types));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_lazy_types\<close>
    "print the types that have been declared as lazy and their substitution state"
    (pair (Toplevel.theory (tap print_lazy_types)));

end