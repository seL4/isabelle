signature REIFY_TABLE =
sig

type table
val empty : table
val get_var : term -> table -> (int * table)
val get_term : int -> table -> term option

end

structure Reifytab: REIFY_TABLE =
struct
type table = (int * (term * int) list)

val empty = (0, [])

fun get_var t (max_var, tis) =
  (case AList.lookup Envir.aeconv tis t of
    SOME v => (v, (max_var, tis))
  | NONE => (max_var, (max_var + 1, (t, max_var) :: tis))
  )

fun get_term v (_, tis) = Library.find_first (fn (_, v2) => v = v2) tis
                          |> Option.map fst

end

signature LOGIC_SIGNATURE =
sig

val mk_Trueprop : term -> term
val dest_Trueprop : term -> term
val Trueprop_conv : conv -> conv
val Not : term
val conj : term
val disj : term

val notI : thm (* (P \<Longrightarrow> False) \<Longrightarrow> \<not> P *)
val ccontr : thm (* (\<not> P \<Longrightarrow> False) \<Longrightarrow> P *)
val conjI : thm (* P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q *)
val conjE : thm (* P \<and> Q \<Longrightarrow> (P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R *)
val disjE : thm (* P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R *)

val not_not_conv : conv (* \<not> (\<not> P) \<equiv> P *)
val de_Morgan_conj_conv : conv (* \<not> (P \<and> Q) \<equiv> \<not> P \<or> \<not> Q *)
val de_Morgan_disj_conv : conv (* \<not> (P \<or> Q) \<equiv> \<not> P \<and> \<not> Q *)
val conj_disj_distribL_conv : conv (* P \<and> (Q \<or> R) \<equiv> (P \<and> Q) \<or> (P \<and> R) *)
val conj_disj_distribR_conv : conv (* (Q \<or> R) \<and> P \<equiv> (Q \<and> P) \<or> (R \<and> P) *)

end

signature BASE_ORDER_TAC_BASE =
sig
  
val order_trace_cfg : bool Config.T
val order_split_limit_cfg : int Config.T

datatype order_kind = Order | Linorder

type order_literal = (bool * Order_Procedure.order_atom)

type order_ops = { eq : term, le : term, lt : term }

val map_order_ops : (term -> term) -> order_ops -> order_ops

type order_context = {
    kind : order_kind,
    ops : order_ops,
    thms : (string * thm) list, conv_thms : (string * thm) list
  }

end

structure Base_Order_Tac_Base : BASE_ORDER_TAC_BASE =
struct
  
(* Control tracing output of the solver. *)
val order_trace_cfg = Attrib.setup_config_bool @{binding "order_trace"} (K false)
(* In partial orders, literals of the form \<not> x < y will force the order solver to perform case
   distinctions, which leads to an exponential blowup of the runtime. The split limit controls
   the number of literals of this form that are passed to the solver. 
 *)
val order_split_limit_cfg = Attrib.setup_config_int @{binding "order_split_limit"} (K 8)

datatype order_kind = Order | Linorder

type order_literal = (bool * Order_Procedure.order_atom)

type order_ops = { eq : term, le : term, lt : term }

fun map_order_ops f {eq, le, lt} = {eq = f eq, le = f le, lt = f lt}

type order_context = {
    kind : order_kind,
    ops : order_ops,
    thms : (string * thm) list, conv_thms : (string * thm) list
  }

end

signature BASE_ORDER_TAC =
sig

include BASE_ORDER_TAC_BASE
 
type insert_prems_hook =
  order_kind -> order_ops -> Proof.context -> (thm * (bool * term * (term * term))) list
    -> thm list

val declare_insert_prems_hook :
  (binding * insert_prems_hook) -> local_theory -> local_theory

val insert_prems_hook_names : Proof.context -> binding list

val tac :
  (order_literal Order_Procedure.fm -> Order_Procedure.prf_trm option)
    -> order_context -> thm list
    -> Proof.context -> int -> tactic

end

functor Base_Order_Tac(
  structure Logic_Sig : LOGIC_SIGNATURE; val excluded_types : typ list) : BASE_ORDER_TAC =
struct

open Base_Order_Tac_Base
open Order_Procedure

fun expect _ (SOME x) = x
  | expect f NONE = f ()

fun list_curry0 f = (fn [] => f, 0)
fun list_curry1 f = (fn [x] => f x, 1)
fun list_curry2 f = (fn [x, y] => f x y, 2)

fun dereify_term consts reifytab t =
  let
    fun dereify_term' (App (t1, t2)) = (dereify_term' t1) $ (dereify_term' t2)
      | dereify_term' (Const s) =
          AList.lookup (op =) consts s
          |> expect (fn () => raise TERM ("Const " ^ s ^ " not in", map snd consts))
      | dereify_term' (Var v) = Reifytab.get_term (integer_of_int v) reifytab |> the
  in
    dereify_term' t
  end

fun dereify_order_fm (eq, le, lt) reifytab t =
  let
    val consts = [
      ("eq", eq), ("le", le), ("lt", lt),
      ("Not", Logic_Sig.Not), ("disj", Logic_Sig.disj), ("conj", Logic_Sig.conj)
      ]
  in
    dereify_term consts reifytab t
  end

fun strip_AppP t =
  let fun strip (AppP (f, s), ss) = strip (f, s::ss)
        | strip x = x
  in strip (t, []) end

fun replay_conv convs cvp =
  let
    val convs = convs @
      [("all_conv", list_curry0 Conv.all_conv)] @ 
      map (apsnd list_curry1) [
        ("atom_conv", I),
        ("neg_atom_conv", I),
        ("arg_conv", Conv.arg_conv)] @
      map (apsnd list_curry2) [
        ("combination_conv", Conv.combination_conv),
        ("then_conv", curry (op then_conv))]

    fun lookup_conv convs c = AList.lookup (op =) convs c
          |> expect (fn () => error ("Can't replay conversion: " ^ c))

    fun rp_conv t =
      (case strip_AppP t ||> map rp_conv of
        (PThm c, cvs) =>
          let val (conv, arity) = lookup_conv convs c
          in if arity = length cvs
            then conv cvs
            else error ("Expected " ^ Int.toString arity ^ " arguments for conversion " ^
                        c ^ " but got " ^ (length cvs |> Int.toString) ^ " arguments")
          end
      | _ => error "Unexpected constructor in conversion proof")
  in
    rp_conv cvp
  end

fun replay_prf_trm replay_conv dereify ctxt thmtab assmtab p =
  let
    fun replay_prf_trm' _ (PThm s) =
          AList.lookup (op =) thmtab s
          |> expect (fn () => error ("Cannot replay theorem: " ^ s))
      | replay_prf_trm' assmtab (Appt (p, t)) =
          replay_prf_trm' assmtab p
          |> Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (dereify t))]
      | replay_prf_trm' assmtab (AppP (p1, p2)) =
          apply2 (replay_prf_trm' assmtab) (p2, p1) |> op COMP
      | replay_prf_trm' assmtab (AbsP (reified_t, p)) =
          let
            val t = dereify reified_t
            val t_thm = Logic_Sig.mk_Trueprop t |> Thm.cterm_of ctxt |> Assumption.assume ctxt
            val rp = replay_prf_trm' (Termtab.update (Thm.prop_of t_thm, t_thm) assmtab) p
          in
            Thm.implies_intr (Thm.cprop_of t_thm) rp
          end
      | replay_prf_trm' assmtab (Bound reified_t) =
          let
            val t = dereify reified_t |> Logic_Sig.mk_Trueprop
          in
            Termtab.lookup assmtab t
            |> expect (fn () => raise TERM ("Assumption not found:", t::Termtab.keys assmtab))
          end
      | replay_prf_trm' assmtab (Conv (t, cp, p)) =
          let
            val thm = replay_prf_trm' assmtab (Bound t)
            val conv = Logic_Sig.Trueprop_conv (replay_conv cp)
            val conv_thm = Conv.fconv_rule conv thm
            val conv_term = Thm.prop_of conv_thm
          in
            replay_prf_trm' (Termtab.update (conv_term, conv_thm) assmtab) p
          end
  in
    replay_prf_trm' assmtab p
  end

fun replay_order_prf_trm ord_ops {thms = thms, conv_thms = conv_thms, ...} ctxt reifytab assmtab =
  let
    val thmtab = thms @ [
        ("conjE", Logic_Sig.conjE), ("conjI", Logic_Sig.conjI), ("disjE", Logic_Sig.disjE)
      ]
    val convs = map (apsnd list_curry0) (
      map (apsnd Conv.rewr_conv) conv_thms @
      [
        ("not_not_conv", Logic_Sig.not_not_conv),
        ("de_Morgan_conj_conv", Logic_Sig.de_Morgan_conj_conv),
        ("de_Morgan_disj_conv", Logic_Sig.de_Morgan_disj_conv),
        ("conj_disj_distribR_conv", Logic_Sig.conj_disj_distribR_conv),
        ("conj_disj_distribL_conv", Logic_Sig.conj_disj_distribL_conv)
      ])
    
    val dereify = dereify_order_fm ord_ops reifytab
  in
    replay_prf_trm (replay_conv convs) dereify ctxt thmtab assmtab
  end

fun strip_Not (nt $ t) = if nt = Logic_Sig.Not then t else nt $ t
  | strip_Not t = t

fun limit_not_less lt ctxt decomp_prems =
  let
    val trace = Config.get ctxt order_trace_cfg
    val limit = Config.get ctxt order_split_limit_cfg

    fun is_not_less_term t =
      case try (strip_Not o Logic_Sig.dest_Trueprop) t of
        SOME (binop $ _ $ _) => binop = lt
      | _ => false

    val not_less_prems = filter (is_not_less_term o Thm.prop_of o fst) decomp_prems
    val _ = if trace andalso length not_less_prems > limit
              then tracing "order split limit exceeded"
              else ()
  in
    filter_out (is_not_less_term o Thm.prop_of o fst) decomp_prems @
    take limit not_less_prems
  end

fun decomp {eq, le, lt} ctxt t =
  let
    fun decomp'' (binop $ t1 $ t2) =
          let
            fun is_excluded t = exists (fn ty => ty = fastype_of t) excluded_types

            open Order_Procedure
            val thy = Proof_Context.theory_of ctxt
            fun try_match pat = try (Pattern.match thy (pat, binop)) (Vartab.empty, Vartab.empty)
          in if is_excluded t1 then NONE
             else case (try_match eq, try_match le, try_match lt) of
                    (SOME env, _, _) => SOME ((true, EQ, (t1, t2)), env)
                  | (_, SOME env, _) => SOME ((true, LEQ, (t1, t2)), env)
                  | (_, _, SOME env) => SOME ((true, LESS, (t1, t2)), env)
                  | _ => NONE
          end
      | decomp'' _ = NONE

      fun decomp' (nt $ t) =
            if nt = Logic_Sig.Not
              then decomp'' t |> Option.map (fn ((b, c, p), e) => ((not b, c, p), e))
              else decomp'' (nt $ t)
        | decomp' t = decomp'' t
  in
    try Logic_Sig.dest_Trueprop t |> Option.mapPartial decomp'
  end

fun maximal_envs envs =
  let
    fun test_opt p (SOME x) = p x
      | test_opt _ NONE = false

    fun leq_env (tyenv1, tenv1) (tyenv2, tenv2) =
      Vartab.forall (fn (v, ty) =>
        Vartab.lookup tyenv2 v |> test_opt (fn ty2 => ty2 = ty)) tyenv1
      andalso
      Vartab.forall (fn (v, (ty, t)) =>
        Vartab.lookup tenv2 v |> test_opt (fn (ty2, t2) => ty2 = ty andalso t2 aconv t)) tenv1

    fun fold_env (i, env) es = fold_index (fn (i2, env2) => fn es =>
      if i = i2 then es else if leq_env env env2 then (i, i2) :: es else es) envs es
    
    val env_order = fold_index fold_env envs []

    val graph = fold_index (fn (i, env) => fn g => Int_Graph.new_node (i, env) g)
                           envs Int_Graph.empty
    val graph = fold Int_Graph.add_edge env_order graph

    val strong_conns = Int_Graph.strong_conn graph
    val maximals =
      filter (fn comp => length comp = length (Int_Graph.all_succs graph comp)) strong_conns
  in
    map (Int_Graph.all_preds graph) maximals
  end

fun partition_prems octxt ctxt prems =
  let
    fun these' _ [] = []
      | these' f (x :: xs) = case f x of NONE => these' f xs | SOME y => (x, y) :: these' f xs
    
    val (decomp_prems, envs) =
      these' (decomp (#ops octxt) ctxt o Thm.prop_of) prems
      |> map_split (fn (thm, (l, env)) => ((thm, l), env))
        
    val env_groups = maximal_envs envs
  in
    map (fn is => (map (nth decomp_prems) is, nth envs (hd is))) env_groups
  end

local
  fun pretty_term_list ctxt =
    Pretty.list "" "" o map (Syntax.pretty_term (Config.put show_types true ctxt))
  fun pretty_type_of ctxt t = Pretty.block
    [ Pretty.str "::", Pretty.brk 1
    , Pretty.quote (Syntax.pretty_typ ctxt (Term.fastype_of t)) ]
in
  fun pretty_order_kind (okind : order_kind) = Pretty.str (@{make_string} okind)
  fun pretty_order_ops ctxt ({eq, le, lt} : order_ops) =
    Pretty.block [pretty_term_list ctxt [eq, le, lt], Pretty.brk 1, pretty_type_of ctxt le]
end

type insert_prems_hook =
  order_kind -> order_ops -> Proof.context -> (thm * (bool * term * (term * term))) list
    -> thm list

structure Insert_Prems_Hook_Data = Generic_Data(
  type T = (binding * insert_prems_hook) list
  val empty = []
  val merge = Library.merge ((op =) o apply2 fst)
)

fun declare_insert_prems_hook (binding, hook) lthy =
  lthy |> Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
    (fn phi => fn context =>
      let
        val binding = Morphism.binding phi binding
      in
        context
        |> Insert_Prems_Hook_Data.map (Library.insert ((op =) o apply2 fst) (binding, hook))
      end)

val insert_prems_hook_names = Context.Proof #> Insert_Prems_Hook_Data.get #> map fst

fun eval_insert_prems_hook kind order_ops ctxt decomp_prems (hookN, hook : insert_prems_hook) = 
  let
    fun dereify_order_op' (EQ _) = #eq order_ops
      | dereify_order_op' (LEQ _) = #le order_ops
      | dereify_order_op' (LESS _) = #lt order_ops
    fun dereify_order_op oop = (~1, ~1) |> apply2 Int_of_integer |> oop |> dereify_order_op'
    val decomp_prems =
      decomp_prems
      |> map (apsnd (fn (b, oop, (t1, t2)) => (b, dereify_order_op oop, (t1, t2))))
    fun unzip (acc1, acc2) [] = (rev acc1, rev acc2)
      | unzip (acc1, acc2) ((thm, NONE) :: ps) = unzip (acc1, thm :: acc2) ps
      | unzip (acc1, acc2) ((thm, SOME dp) :: ps) = unzip ((thm, dp) :: acc1, acc2) ps
    val (decomp_extra_prems, invalid_extra_prems) =
      hook kind order_ops ctxt decomp_prems
      |> map (swap o ` (decomp order_ops ctxt o Thm.prop_of))
      |> unzip ([], [])

    val pretty_thm_list = Pretty.list "" "" o map (Thm.pretty_thm ctxt)
    fun pretty_trace () = 
      [ ("order kind:", pretty_order_kind kind)
      , ("order operators:", pretty_order_ops ctxt order_ops)
      , ("inserted premises:", pretty_thm_list (map fst decomp_extra_prems))
      , ("invalid premises:", pretty_thm_list invalid_extra_prems)
      ]
      |> map (fn (t, pp) => Pretty.block [Pretty.str t, Pretty.brk 1, pp])
      |> Pretty.big_list ("insert premises hook " ^ Pretty.string_of (Binding.pretty hookN) 
          ^ " called with the parameters")
    val trace = Config.get ctxt order_trace_cfg
    val _ = if trace then tracing (Pretty.string_of (pretty_trace ())) else ()
  in
    map (apsnd fst) decomp_extra_prems
  end
    
fun order_tac raw_order_proc octxt simp_prems =
  Subgoal.FOCUS (fn {prems=prems, context=ctxt, ...} =>
    let
      val trace = Config.get ctxt order_trace_cfg
      
      fun order_tac' ([], _) = no_tac
        | order_tac' (decomp_prems, env) =
          let
            val (order_ops as {eq, le, lt}) =
              #ops octxt |> map_order_ops (Envir.eta_contract o Envir.subst_term env)
              
            val insert_prems_hooks = Insert_Prems_Hook_Data.get (Context.Proof ctxt)
            val inserted_decomp_prems =
              insert_prems_hooks
              |> maps (eval_insert_prems_hook (#kind octxt) order_ops ctxt decomp_prems)

            val decomp_prems = decomp_prems @ inserted_decomp_prems
            val decomp_prems =
              case #kind octxt of
                Order => limit_not_less lt ctxt decomp_prems
              | _ => decomp_prems
    
            fun reify_prem (_, (b, ctor, (x, y))) (ps, reifytab) =
              (Reifytab.get_var x ##>> Reifytab.get_var y) reifytab
              |>> (fn vp => (b, ctor (apply2 Int_of_integer vp)) :: ps)
            val (reified_prems, reifytab) = fold_rev reify_prem decomp_prems ([], Reifytab.empty)

            val reified_prems_conj = foldl1 (fn (x, a) => And (x, a)) (map Atom reified_prems)
            val prems_conj_thm = map fst decomp_prems
                                 |> foldl1 (fn (x, a) => Logic_Sig.conjI OF [x, a])
                                 |> Conv.fconv_rule Thm.eta_conversion 
            val prems_conj = prems_conj_thm |> Thm.prop_of
            
            val proof = raw_order_proc reified_prems_conj

            val pretty_thm_list = Pretty.list "" "" o map (Thm.pretty_thm ctxt)
            fun pretty_trace () = 
              [ ("order kind:", pretty_order_kind (#kind octxt))
              , ("order operators:", pretty_order_ops ctxt order_ops)
              , ("premises:", pretty_thm_list prems)
              , ("selected premises:", pretty_thm_list (map fst decomp_prems))
              , ("reified premises:", Pretty.str (@{make_string} reified_prems))
              , ("contradiction:", Pretty.str (@{make_string} (Option.isSome proof)))
              ] 
              |> map (fn (t, pp) => Pretty.block [Pretty.str t, Pretty.brk 1, pp])
              |> Pretty.big_list "order solver called with the parameters"
            val _ = if trace then tracing (Pretty.string_of (pretty_trace ())) else ()

            val assmtab = Termtab.make [(prems_conj, prems_conj_thm)]
            val replay = replay_order_prf_trm (eq, le, lt) octxt ctxt reifytab assmtab
          in
            case proof of
              NONE => no_tac
            | SOME p => SOLVED' (resolve_tac ctxt [replay p]) 1
          end

      val prems = simp_prems @ prems
                  |> filter (fn p => null (Term.add_vars (Thm.prop_of p) []))
                  |> map (Conv.fconv_rule Thm.eta_conversion)
   in
    partition_prems octxt ctxt prems |> map order_tac' |> FIRST
   end)

val ad_absurdum_tac = SUBGOAL (fn (A, i) =>
  case try (Logic_Sig.dest_Trueprop o Logic.strip_assums_concl) A of
    SOME (nt $ _) =>
      if nt = Logic_Sig.Not
        then resolve0_tac [Logic_Sig.notI] i
        else resolve0_tac [Logic_Sig.ccontr] i
  | _ => resolve0_tac [Logic_Sig.ccontr] i)

fun tac raw_order_proc octxt simp_prems ctxt =
  ad_absurdum_tac THEN' order_tac raw_order_proc octxt simp_prems ctxt
  
end

functor Order_Tac(structure Base_Tac : BASE_ORDER_TAC) = struct

open Base_Tac

fun order_context_eq ({kind = kind1, ops = ops1, ...}, {kind = kind2, ops = ops2, ...}) =
  let
    fun ops_list ops = [#eq ops, #le ops, #lt ops]
  in
    kind1 = kind2 andalso eq_list (op aconv) (apply2 ops_list (ops1, ops2))
  end
val order_data_eq = order_context_eq o apply2 fst

structure Data = Generic_Data(
  type T = (order_context * (order_context -> thm list -> Proof.context -> int -> tactic)) list
  val empty = []
  fun merge data = Library.merge order_data_eq data
)

fun declare (octxt as {kind = kind, raw_proc = raw_proc, ...}) lthy =
  lthy |> Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
    (fn phi => fn context =>
      let
        val ops = map_order_ops (Morphism.term phi) (#ops octxt)
        val thms = map (fn (s, thm) => (s, Morphism.thm phi thm)) (#thms octxt)
        val conv_thms = map (fn (s, thm) => (s, Morphism.thm phi thm)) (#conv_thms octxt)
        val octxt' = {kind = kind, ops = ops, thms = thms, conv_thms = conv_thms}
      in
        context |> Data.map (Library.insert order_data_eq (octxt', raw_proc))
      end)

fun declare_order {
    ops = ops,
    thms = {
      trans = trans, (* x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z *)
      refl = refl, (* x \<le> x *)
      eqD1 = eqD1, (* x = y \<Longrightarrow> x \<le> y *)
      eqD2 = eqD2, (* x = y \<Longrightarrow> y \<le> x *)
      antisym = antisym, (* x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y *)
      contr = contr (* \<not> P \<Longrightarrow> P \<Longrightarrow> R *)
    },
    conv_thms = {
      less_le = less_le, (* x < y \<equiv> x \<le> y \<and> x \<noteq> y *)
      nless_le = nless_le (* \<not> a < b \<equiv> \<not> a \<le> b \<or> a = b *)
    }
  } =
  declare {
    kind = Order,
    ops = ops,
    thms = [("trans", trans), ("refl", refl), ("eqD1", eqD1), ("eqD2", eqD2),
            ("antisym", antisym), ("contr", contr)],
    conv_thms = [("less_le", less_le), ("nless_le", nless_le)],
    raw_proc = Base_Tac.tac Order_Procedure.po_contr_prf
   }                

fun declare_linorder {
    ops = ops,
    thms = {
      trans = trans, (* x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z *)
      refl = refl, (* x \<le> x *)
      eqD1 = eqD1, (* x = y \<Longrightarrow> x \<le> y *)
      eqD2 = eqD2, (* x = y \<Longrightarrow> y \<le> x *)
      antisym = antisym, (* x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y *)
      contr = contr (* \<not> P \<Longrightarrow> P \<Longrightarrow> R *)
    },
    conv_thms = {
      less_le = less_le, (* x < y \<equiv> x \<le> y \<and> x \<noteq> y *)
      nless_le = nless_le, (* \<not> x < y \<equiv> y \<le> x *)
      nle_le = nle_le (* \<not> a \<le> b \<equiv> b \<le> a \<and> b \<noteq> a *)
    }
  } =
  declare {
    kind = Linorder,
    ops = ops,
    thms = [("trans", trans), ("refl", refl), ("eqD1", eqD1), ("eqD2", eqD2),
            ("antisym", antisym), ("contr", contr)],
    conv_thms = [("less_le", less_le), ("nless_le", nless_le), ("nle_le", nle_le)],
    raw_proc = Base_Tac.tac Order_Procedure.lo_contr_prf
   }

(* Try to solve the goal by calling the order solver with each of the declared orders. *)      
fun tac simp_prems ctxt =
  let fun app_tac (octxt, tac0) = CHANGED o tac0 octxt simp_prems ctxt
  in FIRST' (map app_tac (Data.get (Context.Proof ctxt))) end

end