signature REIFY_TABLE =
sig
  type table
  val empty : table
  val get_var : term -> table -> (int * table)
  val get_term : int -> table -> term option
end

structure Reifytab: REIFY_TABLE =
struct
  type table = (int * int Termtab.table * term Inttab.table)
  
  val empty = (0, Termtab.empty, Inttab.empty)
  
  fun get_var t (tab as (max_var, termtab, inttab)) =
    (case Termtab.lookup termtab t of
      SOME v => (v, tab)
    | NONE => (max_var,
              (max_var + 1, Termtab.update (t, max_var) termtab, Inttab.update (max_var, t) inttab))
    )
  
  fun get_term v (_, _, inttab) = Inttab.lookup inttab v
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

(* Control tracing output of the solver. *)
val order_trace_cfg = Attrib.setup_config_bool @{binding "order_trace"} (K false)
(* In partial orders, literals of the form \<not> x < y will force the order solver to perform case
   distinctions, which leads to an exponential blowup of the runtime. The split limit controls
   the number of literals of this form that are passed to the solver. 
 *)
val order_split_limit_cfg = Attrib.setup_config_int @{binding "order_split_limit"} (K 8)

datatype order_kind = Order | Linorder

type order_literal = (bool * Order_Procedure.o_atom)

type order_context = {
    kind : order_kind,
    ops : term list, thms : (string * thm) list, conv_thms : (string * thm) list
  }

signature BASE_ORDER_TAC =
sig

  val tac :
        (order_literal Order_Procedure.fm -> Order_Procedure.prf_trm option)
        -> order_context -> thm list
        -> Proof.context -> int -> tactic
end

functor Base_Order_Tac(
  structure Logic_Sig : LOGIC_SIGNATURE; val excluded_types : typ list) : BASE_ORDER_TAC =
struct
  open Order_Procedure

  fun expect _ (SOME x) = x
    | expect f NONE = f ()

  fun matches_skeleton t s = t = Term.dummy orelse
    (case (t, s) of
      (t0 $ t1, s0 $ s1) => matches_skeleton t0 s0 andalso matches_skeleton t1 s1
    | _ => t aconv s)

  fun dest_binop t =
    let
      val binop_skel = Term.dummy $ Term.dummy $ Term.dummy
      val not_binop_skel = Logic_Sig.Not $ binop_skel
    in
      if matches_skeleton not_binop_skel t
        then (case t of (_ $ (t1 $ t2 $ t3)) => (false, (t1, t2, t3)))
        else if matches_skeleton binop_skel t
          then (case t of (t1 $ t2 $ t3) => (true, (t1, t2, t3)))
          else raise TERM ("Not a binop literal", [t])
    end

  fun find_term t = Library.find_first (fn (t', _) => t' aconv t)

  fun reify_order_atom (eq, le, lt) t reifytab =
    let
      val (b, (t0, t1, t2)) =
        (dest_binop t) handle TERM (_, _) => raise TERM ("Can't reify order literal", [t])
      val binops = [(eq, EQ), (le, LEQ), (lt, LESS)]
    in
      case find_term t0 binops of
        SOME (_, reified_bop) =>
          reifytab
          |> Reifytab.get_var t1 ||> Reifytab.get_var t2
          |> (fn (v1, (v2, vartab')) =>
               ((b, reified_bop (Int_of_integer v1, Int_of_integer v2)), vartab'))
          |>> Atom
      | NONE => raise TERM ("Can't reify order literal", [t])
    end

  fun reify consts reify_atom t reifytab =
    let
      fun reify' (t1 $ t2) reifytab =
            let
              val (t0, ts) = strip_comb (t1 $ t2)
              val consts_of_arity = filter (fn (_, (_, ar)) => length ts = ar) consts
            in
              (case find_term t0 consts_of_arity of
                SOME (_, (reified_op, _)) => fold_map reify' ts reifytab |>> reified_op
              | NONE => reify_atom (t1 $ t2) reifytab)
            end
        | reify' t reifytab = reify_atom t reifytab
    in
      reify' t reifytab
    end

  fun list_curry0 f = (fn [] => f, 0)
  fun list_curry1 f = (fn [x] => f x, 1)
  fun list_curry2 f = (fn [x, y] => f x y, 2)

  fun reify_order_conj ord_ops =
    let
      val consts = map (apsnd (list_curry2 o curry)) [(Logic_Sig.conj, And), (Logic_Sig.disj, Or)]
    in   
      reify consts (reify_order_atom ord_ops)
    end

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
            apply2 (replay_prf_trm' assmtab) (p2, p1) |> (op COMP)
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

  fun is_binop_term t =
    let
      fun is_included t = forall (curry (op <>) (t |> fastype_of |> domain_type)) excluded_types
    in
      (case dest_binop (Logic_Sig.dest_Trueprop t) of
        (_, (binop, t1, t2)) =>
          is_included binop andalso
          (* Exclude terms with schematic variables since the solver can't deal with them.
             More specifically, the solver uses Assumption.assume which does not allow schematic
             variables in the assumed cterm.
          *)
          Term.add_var_names (binop $ t1 $ t2) [] = []
      ) handle TERM (_, _) => false
    end

  fun partition_matches ctxt term_of pats ys =
    let
      val thy = Proof_Context.theory_of ctxt

      fun find_match t env =
        Library.get_first (try (fn pat => Pattern.match thy (pat, t) env)) pats
      
      fun filter_matches xs = fold (fn x => fn (mxs, nmxs, env) =>
        case find_match (term_of x) env of
          SOME env' => (x::mxs, nmxs, env')
        | NONE => (mxs, x::nmxs, env)) xs ([], [], (Vartab.empty, Vartab.empty))

      fun partition xs =
        case filter_matches xs of
          ([], _, _) => []
        | (mxs, nmxs, env) => (env, mxs) :: partition nmxs
    in
      partition ys
    end

  fun limit_not_less [_, _, lt] ctxt prems =
    let
      val thy = Proof_Context.theory_of ctxt
      val trace = Config.get ctxt order_trace_cfg
      val limit = Config.get ctxt order_split_limit_cfg

      fun is_not_less_term t =
        (case dest_binop (Logic_Sig.dest_Trueprop t) of
          (false, (t0, _, _)) => Pattern.matches thy (lt, t0)
        | _ => false)
        handle TERM _ => false

      val not_less_prems = filter (is_not_less_term o Thm.prop_of) prems
      val _ = if trace andalso length not_less_prems > limit
                then tracing "order split limit exceeded"
                else ()
     in
      filter_out (is_not_less_term o Thm.prop_of) prems @
      take limit not_less_prems
     end
      
  fun order_tac raw_order_proc octxt simp_prems =
    Subgoal.FOCUS (fn {prems=prems, context=ctxt, ...} =>
      let
        val trace = Config.get ctxt order_trace_cfg

        val binop_prems = filter (is_binop_term o Thm.prop_of) (prems @ simp_prems)
        val strip_binop = (fn (x, _, _) => x) o snd o dest_binop
        val binop_of = strip_binop o Logic_Sig.dest_Trueprop o Thm.prop_of

        (* Due to local_setup, the operators of the order may contain schematic term and type
           variables. We partition the premises according to distinct instances of those operators.
         *)
        val part_prems = partition_matches ctxt binop_of (#ops octxt) binop_prems
          |> (case #kind octxt of
                Order => map (fn (env, prems) =>
                          (env, limit_not_less (#ops octxt) ctxt prems))
              | _ => I)
              
        fun order_tac' (_, []) = no_tac
          | order_tac' (env, prems) =
            let
              val [eq, le, lt] = #ops octxt
              val subst_contract = Envir.eta_contract o Envir.subst_term env
              val ord_ops = (subst_contract eq,
                             subst_contract le,
                             subst_contract lt)
  
              val _ = if trace then @{print} (ord_ops, prems) else (ord_ops, prems)
  
              val prems_conj_thm = foldl1 (fn (x, a) => Logic_Sig.conjI OF [x, a]) prems
                |> Conv.fconv_rule Thm.eta_conversion 
              val prems_conj = prems_conj_thm |> Thm.prop_of
              val (reified_prems_conj, reifytab) =
                reify_order_conj ord_ops (Logic_Sig.dest_Trueprop prems_conj) Reifytab.empty
  
              val proof = raw_order_proc reified_prems_conj
  
              val assmtab = Termtab.make [(prems_conj, prems_conj_thm)]
              val replay = replay_order_prf_trm ord_ops octxt ctxt reifytab assmtab
            in
              case proof of
                NONE => no_tac
              | SOME p => SOLVED' (resolve_tac ctxt [replay p]) 1
            end
     in
      FIRST (map order_tac' part_prems)
     end)

  val ad_absurdum_tac = SUBGOAL (fn (A, i) =>
      case try (Logic_Sig.dest_Trueprop o Logic.strip_assums_concl) A of
        SOME (nt $ _) =>
          if nt = Logic_Sig.Not
            then resolve0_tac [Logic_Sig.notI] i
            else resolve0_tac [Logic_Sig.ccontr] i
      | SOME _ => resolve0_tac [Logic_Sig.ccontr] i
      | NONE => resolve0_tac [Logic_Sig.ccontr] i)

  fun tac raw_order_proc octxt simp_prems ctxt =
      EVERY' [
          ad_absurdum_tac,
          CONVERSION Thm.eta_conversion,
          order_tac raw_order_proc octxt simp_prems ctxt
        ]
  
end

functor Order_Tac(structure Base_Tac : BASE_ORDER_TAC) = struct

  fun order_context_eq ({kind = kind1, ops = ops1, ...}, {kind = kind2, ops = ops2, ...}) =
    kind1 = kind2 andalso eq_list (op aconv) (ops1, ops2)

  fun order_data_eq (x, y) = order_context_eq (fst x, fst y)
  
  structure Data = Generic_Data(
    type T = (order_context * (order_context -> thm list -> Proof.context -> int -> tactic)) list
    val empty = []
    val extend = I
    fun merge data = Library.merge order_data_eq data
  )

  fun declare (octxt as {kind = kind, raw_proc = raw_proc, ...}) lthy =
    lthy |> Local_Theory.declaration {syntax = false, pervasive = false} (fn phi => fn context =>
      let
        val ops = map (Morphism.term phi) (#ops octxt)
        val thms = map (fn (s, thm) => (s, Morphism.thm phi thm)) (#thms octxt)
        val conv_thms = map (fn (s, thm) => (s, Morphism.thm phi thm)) (#conv_thms octxt)
        val octxt' = {kind = kind, ops = ops, thms = thms, conv_thms = conv_thms}
      in
        context |> Data.map (Library.insert order_data_eq (octxt', raw_proc))
      end)

  fun declare_order {
      ops = {eq = eq, le = le, lt = lt},
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
      ops = [eq, le, lt],
      thms = [("trans", trans), ("refl", refl), ("eqD1", eqD1), ("eqD2", eqD2),
              ("antisym", antisym), ("contr", contr)],
      conv_thms = [("less_le", less_le), ("nless_le", nless_le)],
      raw_proc = Base_Tac.tac Order_Procedure.po_contr_prf
     }                

  fun declare_linorder {
      ops = {eq = eq, le = le, lt = lt},
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
      ops = [eq, le, lt],
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
