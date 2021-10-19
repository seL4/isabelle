(*  Title:      HOL/Statespace/state_fun.ML
    Author:     Norbert Schirmer, TU Muenchen, 2007
    Author:     Norbert Schirmer, Apple, 2021
*)

signature STATE_FUN =
sig
  val lookupN : string
  val updateN : string

  val mk_constr : theory -> typ -> term
  val mk_destr : theory -> typ -> term

  val lookup_simproc : simproc
  val update_simproc : simproc
  val ex_lookup_eq_simproc : simproc
  val ex_lookup_ss : simpset
  val lazy_conj_simproc : simproc
  val string_eq_simp_tac : Proof.context -> int -> tactic

  val trace_data : Context.generic -> unit
end;

structure StateFun: STATE_FUN =
struct

val lookupN = \<^const_name>\<open>StateFun.lookup\<close>;
val updateN = \<^const_name>\<open>StateFun.update\<close>;

val sel_name = HOLogic.dest_string;

fun mk_name i t =
  (case try sel_name t of
    SOME name => name
  | NONE =>
      (case t of
        Free (x, _) => x
      | Const (x, _) => x
      | _ => "x" ^ string_of_int i));

local

val conj1_False = @{thm conj1_False};
val conj2_False = @{thm conj2_False};
val conj_True = @{thm conj_True};
val conj_cong = @{thm conj_cong};

fun isFalse (Const (\<^const_name>\<open>False\<close>, _)) = true
  | isFalse _ = false;

fun isTrue (Const (\<^const_name>\<open>True\<close>, _)) = true
  | isTrue _ = false;

in

val lazy_conj_simproc =
  Simplifier.make_simproc \<^context> "lazy_conj_simp"
   {lhss = [\<^term>\<open>P & Q\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.conj\<close>,_) $ P $ Q =>
          let
            val P_P' = Simplifier.rewrite ctxt (Thm.cterm_of ctxt P);
            val P' = P_P' |> Thm.prop_of |> Logic.dest_equals |> #2;
          in
            if isFalse P' then SOME (conj1_False OF [P_P'])
            else
              let
                val Q_Q' = Simplifier.rewrite ctxt (Thm.cterm_of ctxt Q);
                val Q' = Q_Q' |> Thm.prop_of |> Logic.dest_equals |> #2;
              in
                if isFalse Q' then SOME (conj2_False OF [Q_Q'])
                else if isTrue P' andalso isTrue Q' then SOME (conj_True OF [P_P', Q_Q'])
                else if P aconv P' andalso Q aconv Q' then NONE
                else SOME (conj_cong OF [P_P', Q_Q'])
              end
           end
      | _ => NONE)};

fun string_eq_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt
    addsimps @{thms list.inject list.distinct char.inject
      cong_exp_iff_simps simp_thms}
    addsimprocs [lazy_conj_simproc]
    |> Simplifier.add_cong @{thm block_conj_cong});

end;

val lookup_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context>
    addsimps (@{thms list.inject} @ @{thms char.inject}
      @ @{thms list.distinct} @ @{thms simp_thms}
      @ [@{thm StateFun.lookup_update_id_same}, @{thm StateFun.id_id_cancel},
        @{thm StateFun.lookup_update_same}, @{thm StateFun.lookup_update_other}])
    addsimprocs [lazy_conj_simproc]
    addSolver StateSpace.distinctNameSolver
    |> fold Simplifier.add_cong @{thms block_conj_cong});

val ex_lookup_ss =
  simpset_of (put_simpset HOL_ss \<^context> addsimps @{thms StateFun.ex_id});


structure Data = Generic_Data
(
  type T = simpset * simpset * bool;  (*lookup simpset, ex_lookup simpset, are simprocs installed*)
  val empty = (empty_ss, empty_ss, false);
  fun merge ((ss1, ex_ss1, b1), (ss2, ex_ss2, b2)) =
    (merge_ss (ss1, ss2), merge_ss (ex_ss1, ex_ss2), b1 orelse b2);
);

fun trace_data context =
  let
    val (lookup_ss, ex_ss, active) = Data.get context
    val pretty_ex_ss = Simplifier.pretty_simpset true (put_simpset ex_ss (Context.proof_of context)) 
    val pretty_lookup_ss = Simplifier.pretty_simpset true (put_simpset lookup_ss (Context.proof_of context)) 
  in
    tracing ("state_fun ex_ss: " ^ Pretty.string_of pretty_ex_ss ^ 
     "\n ================= \n lookup_ss: " ^ Pretty.string_of pretty_lookup_ss ^ "\n " ^ 
     "active: " ^ @{make_string} active)
  end

val _ = Theory.setup (Context.theory_map (Data.put (lookup_ss, ex_lookup_ss, false)));

val lookup_simproc =
  Simplifier.make_simproc \<^context> "lookup_simp"
   {lhss = [\<^term>\<open>lookup d n (update d' c m v s)\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of (Const (\<^const_name>\<open>StateFun.lookup\<close>, lT) $ destr $ n $
                   (s as Const (\<^const_name>\<open>StateFun.update\<close>, uT) $ _ $ _ $ _ $ _ $ _)) =>
        (let
          val (_::_::_::_::sT::_) = binder_types uT;
          val mi = Term.maxidx_of_term (Thm.term_of ct);
          fun mk_upds (Const (\<^const_name>\<open>StateFun.update\<close>, uT) $ d' $ c $ m $ v $ s) =
                let
                  val (_ :: _ :: _ :: fT :: _ :: _) = binder_types uT;
                  val vT = domain_type fT;
                  val (s', cnt) = mk_upds s;
                  val (v', cnt') =
                    (case v of
                      Const (\<^const_name>\<open>K_statefun\<close>, KT) $ v'' =>
                        (case v'' of
                          (Const (\<^const_name>\<open>StateFun.lookup\<close>, _) $
                            (d as (Const (\<^const_name>\<open>Fun.id\<close>, _))) $ n' $ _) =>
                              if d aconv c andalso n aconv m andalso m aconv n'
                              then (v,cnt) (* Keep value so that
                                              lookup_update_id_same can fire *)
                              else
                                (Const (\<^const_name>\<open>StateFun.K_statefun\<close>, KT) $
                                  Var (("v", cnt), vT), cnt + 1)
                        | _ =>
                          (Const (\<^const_name>\<open>StateFun.K_statefun\<close>, KT) $
                            Var (("v", cnt), vT), cnt + 1))
                     | _ => (v, cnt));
                in (Const (\<^const_name>\<open>StateFun.update\<close>, uT) $ d' $ c $ m $ v' $ s', cnt') end
            | mk_upds s = (Var (("s", mi + 1), sT), mi + 2);

          val ct =
            Thm.cterm_of ctxt
              (Const (\<^const_name>\<open>StateFun.lookup\<close>, lT) $ destr $ n $ fst (mk_upds s));
          val basic_ss = #1 (Data.get (Context.Proof ctxt));
          val ctxt' = ctxt |> Config.put simp_depth_limit 100 |> put_simpset basic_ss;
          val thm = Simplifier.rewrite ctxt' ct;
        in
          if (op aconv) (Logic.dest_equals (Thm.prop_of thm))
          then NONE
          else SOME thm
        end
        handle Option.Option => NONE)
      | _ => NONE)};


local

val meta_ext = @{thm StateFun.meta_ext};
val ss' =
  simpset_of (put_simpset HOL_ss \<^context> addsimps
    (@{thm StateFun.update_apply} :: @{thm Fun.o_apply} :: @{thms list.inject} @ @{thms char.inject}
      @ @{thms list.distinct})
    addsimprocs [lazy_conj_simproc, StateSpace.distinct_simproc]
    |> fold Simplifier.add_cong @{thms block_conj_cong});

in

val update_simproc =
  Simplifier.make_simproc \<^context> "update_simp"
   {lhss = [\<^term>\<open>update d c n v s\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>StateFun.update\<close>, uT) $ _ $ _ $ _ $ _ $ _ =>
          let
            val (_ :: _ :: _ :: _ :: sT :: _) = binder_types uT;
              (*"('v => 'a1) => ('a2 => 'v) => 'n => ('a1 => 'a2) => ('n => 'v) => ('n => 'v)"*)
            fun init_seed s = (Bound 0, Bound 0, [("s", sT)], [], false);

            fun mk_comp f fT g gT =
              let val T = domain_type fT --> range_type gT
              in (Const (\<^const_name>\<open>Fun.comp\<close>, gT --> fT --> T) $ g $ f, T) end;

            fun mk_comps fs = foldl1 (fn ((f, fT), (g, gT)) => mk_comp g gT f fT) fs;

            fun append n c cT f fT d dT comps =
              (case AList.lookup (op aconv) comps n of
                SOME gTs => AList.update (op aconv) (n, [(c, cT), (f, fT), (d, dT)] @ gTs) comps
              | NONE => AList.update (op aconv) (n, [(c, cT), (f, fT), (d, dT)]) comps);

            fun split_list (x :: xs) = let val (xs', y) = split_last xs in (x, xs', y) end
              | split_list _ = error "StateFun.split_list";

            fun merge_upds n comps =
              let val ((c, cT), fs, (d, dT)) = split_list (the (AList.lookup (op aconv) comps n))
              in ((c, cT), fst (mk_comps fs), (d, dT)) end;

               (* mk_updterm returns
                *  - (orig-term-skeleton,simplified-term-skeleton, vars, b)
                *     where boolean b tells if a simplification has occurred.
                      "orig-term-skeleton = simplified-term-skeleton" is
                *     the desired simplification rule.
                * The algorithm first walks down the updates to the seed-state while
                * memorising the updates in the already-table. While walking up the
                * updates again, the optimised term is constructed.
                *)
            fun mk_updterm already
                ((upd as Const (\<^const_name>\<open>StateFun.update\<close>, uT)) $ d $ c $ n $ v $ s) =
                  let
                    fun rest already = mk_updterm already;
                    val (dT :: cT :: nT :: vT :: sT :: _) = binder_types uT;
                      (*"('v => 'a1) => ('a2 => 'v) => 'n => ('a1 => 'a2) =>
                            ('n => 'v) => ('n => 'v)"*)
                  in
                    if member (op aconv) already n then
                      (case rest already s of
                        (trm, trm', vars, comps, _) =>
                          let
                            val i = length vars;
                            val kv = (mk_name i n, vT);
                            val kb = Bound i;
                            val comps' = append n c cT kb vT d dT comps;
                          in (upd $ d $ c $ n $ kb $ trm, trm', kv :: vars, comps',true) end)
                    else
                      (case rest (n :: already) s of
                        (trm, trm', vars, comps, b) =>
                          let
                            val i = length vars;
                            val kv = (mk_name i n, vT);
                            val kb = Bound i;
                            val comps' = append n c cT kb vT d dT comps;
                            val ((c', c'T), f', (d', d'T)) = merge_upds n comps';
                            val vT' = range_type d'T --> domain_type c'T;
                            val upd' =
                              Const (\<^const_name>\<open>StateFun.update\<close>,
                                d'T --> c'T --> nT --> vT' --> sT --> sT);
                          in
                            (upd $ d $ c $ n $ kb $ trm, upd' $ d' $ c' $ n $ f' $ trm', kv :: vars,
                              comps', b)
                          end)
                  end
              | mk_updterm _ t = init_seed t;

            val ctxt0 = Config.put simp_depth_limit 100 ctxt;
            val ctxt1 = put_simpset ss' ctxt0;
            val ctxt2 = put_simpset (#1 (Data.get (Context.Proof ctxt0))) ctxt0;
          in
            (case mk_updterm [] (Thm.term_of ct) of
              (trm, trm', vars, _, true) =>
                let
                  val eq1 =
                    Goal.prove ctxt0 [] []
                      (Logic.list_all (vars, Logic.mk_equals (trm, trm')))
                      (fn _ => resolve_tac ctxt0 [meta_ext] 1 THEN simp_tac ctxt1 1);
                  val eq2 = Simplifier.asm_full_rewrite ctxt2 (Thm.dest_equals_rhs (Thm.cprop_of eq1));
                in SOME (Thm.transitive eq1 eq2) end
            | _ => NONE)
          end
      | _ => NONE)};

end;


local

val swap_ex_eq = @{thm StateFun.swap_ex_eq};

fun is_selector thy T sel =
  let val (flds, more) = Record.get_recT_fields thy T
  in member (fn (s, (n, _)) => n = s) (more :: flds) sel end;

in

val ex_lookup_eq_simproc =
  Simplifier.make_simproc \<^context> "ex_lookup_eq_simproc"
   {lhss = [\<^term>\<open>Ex t\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val t = Thm.term_of ct;

        val ex_lookup_ss = #2 (Data.get (Context.Proof ctxt));
        val ctxt' = ctxt |> Config.put simp_depth_limit 100 |> put_simpset ex_lookup_ss;
        fun prove prop =
          Goal.prove_global thy [] [] prop
            (fn _ => Record.split_simp_tac ctxt [] (K ~1) 1 THEN simp_tac ctxt' 1);

        fun mkeq (swap, Teq, lT, lo, d, n, x, s) i =
          let
            val (_ :: nT :: _) = binder_types lT;
            (*  ('v => 'a) => 'n => ('n => 'v) => 'a *)
            val x' = if not (Term.is_dependent x) then Bound 1 else raise TERM ("", [x]);
            val n' = if not (Term.is_dependent n) then Bound 2 else raise TERM ("", [n]);
            val sel' = lo $ d $ n' $ s;
          in (Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $ sel' $ x', hd (binder_types Teq), nT, swap) end;

        fun dest_state (s as Bound 0) = s
          | dest_state (s as (Const (sel, sT) $ Bound 0)) =
              if is_selector thy (domain_type sT) sel then s
              else raise TERM ("StateFun.ex_lookup_eq_simproc: not a record slector", [s])
          | dest_state s = raise TERM ("StateFun.ex_lookup_eq_simproc: not a record slector", [s]);

        fun dest_sel_eq
              (Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $
                ((lo as (Const (\<^const_name>\<open>StateFun.lookup\<close>, lT))) $ d $ n $ s) $ X) =
              (false, Teq, lT, lo, d, n, X, dest_state s)
          | dest_sel_eq
              (Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $ X $
                ((lo as (Const (\<^const_name>\<open>StateFun.lookup\<close>, lT))) $ d $ n $ s)) =
              (true, Teq, lT, lo, d, n, X, dest_state s)
          | dest_sel_eq _ = raise TERM ("", []);
      in
        (case t of
          Const (\<^const_name>\<open>Ex\<close>, Tex) $ Abs (s, T, t) =>
            (let
              val (eq, eT, nT, swap) = mkeq (dest_sel_eq t) 0;
              val prop =
                Logic.list_all ([("n", nT), ("x", eT)],
                  Logic.mk_equals (Const (\<^const_name>\<open>Ex\<close>, Tex) $ Abs (s, T, eq), \<^term>\<open>True\<close>));
              val thm = Drule.export_without_context (prove prop);
              val thm' = if swap then swap_ex_eq OF [thm] else thm
            in SOME thm' end handle TERM _ => NONE)
        | _ => NONE)
      end handle Option.Option => NONE};

end;

val val_sfx = "V";
val val_prfx = "StateFun."
fun deco base_prfx s = val_prfx ^ (base_prfx ^ suffix val_sfx s);

fun mkUpper str =
  (case String.explode str of
    [] => ""
  | c::cs => String.implode (Char.toUpper c :: cs));

fun mkName (Type (T,args)) = implode (map mkName args) ^ mkUpper (Long_Name.base_name T)
  | mkName (TFree (x,_)) = mkUpper (Long_Name.base_name x)
  | mkName (TVar ((x,_),_)) = mkUpper (Long_Name.base_name x);

fun is_datatype thy = is_some o BNF_LFP_Compat.get_info thy [BNF_LFP_Compat.Keep_Nesting];

fun mk_map \<^type_name>\<open>List.list\<close> = Syntax.const \<^const_name>\<open>List.map\<close>
  | mk_map n = Syntax.const ("StateFun.map_" ^ Long_Name.base_name n);

fun gen_constr_destr comp prfx thy (Type (T, [])) =
      Syntax.const (deco prfx (mkUpper (Long_Name.base_name T)))
  | gen_constr_destr comp prfx thy (T as Type ("fun",_)) =
      let val (argTs, rangeT) = strip_type T;
      in
        comp
          (Syntax.const (deco prfx (implode (map mkName argTs) ^ "Fun")))
          (fold (fn x => fn y => x $ y)
            (replicate (length argTs) (Syntax.const "StateFun.map_fun"))
            (gen_constr_destr comp prfx thy rangeT))
      end
  | gen_constr_destr comp prfx thy (T' as Type (T, argTs)) =
      if is_datatype thy T
      then (* datatype args are recursively embedded into val *)
        (case argTs of
          [argT] =>
            comp
              ((Syntax.const (deco prfx (mkUpper (Long_Name.base_name T)))))
              ((mk_map T $ gen_constr_destr comp prfx thy argT))
        | _ => raise (TYPE ("StateFun.gen_constr_destr", [T'], [])))
      else (* type args are not recursively embedded into val *)
        Syntax.const (deco prfx (implode (map mkName argTs) ^ mkUpper (Long_Name.base_name T)))
  | gen_constr_destr thy _ _ T = raise (TYPE ("StateFun.gen_constr_destr", [T], []));

val mk_constr = gen_constr_destr (fn a => fn b => Syntax.const \<^const_name>\<open>Fun.comp\<close> $ a $ b) "";
val mk_destr = gen_constr_destr (fn a => fn b => Syntax.const \<^const_name>\<open>Fun.comp\<close> $ b $ a) "the_";

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>statefun_simp\<close>
      (Scan.succeed (Thm.declaration_attribute (fn thm => fn context =>
        let
          val ctxt = Context.proof_of context;
          val (lookup_ss, ex_lookup_ss, simprocs_active) = Data.get context;
          val (lookup_ss', ex_lookup_ss') =
            (case Thm.concl_of thm of
              (_ $ ((Const (\<^const_name>\<open>Ex\<close>, _) $ _))) =>
                (lookup_ss, simpset_map ctxt (Simplifier.add_simp thm) ex_lookup_ss)
            | _ =>
                (simpset_map ctxt (Simplifier.add_simp thm) lookup_ss, ex_lookup_ss));
          val activate_simprocs =
            if simprocs_active then I
            else Simplifier.map_ss (fn ctxt => ctxt addsimprocs [lookup_simproc, update_simproc]);
        in
          context
          |> activate_simprocs
          |> Data.put (lookup_ss', ex_lookup_ss', true)
        end)))
      "simplification in statespaces");

end;
