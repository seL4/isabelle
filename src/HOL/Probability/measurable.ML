(*  Title:      HOL/Probability/measurable.ML
    Author:     Johannes Hölzl <hoelzl@in.tum.de>

Measurability prover.
*)

signature MEASURABLE = 
sig
  datatype level = Concrete | Generic

  val add_app : thm -> Context.generic -> Context.generic
  val add_dest : thm -> Context.generic -> Context.generic
  val add_thm : bool * level -> thm -> Context.generic -> Context.generic

  val measurable_tac : Proof.context -> thm list -> tactic

  val simproc : Proof.context -> cterm -> thm option

  val get : level -> Proof.context -> thm list
  val get_all : Proof.context -> thm list

  val update : (thm Item_Net.T -> thm Item_Net.T) -> level -> Context.generic -> Context.generic

end ;

structure Measurable : MEASURABLE =
struct

datatype level = Concrete | Generic;

structure Data = Generic_Data
(
  type T = {
    concrete_thms : thm Item_Net.T,
    generic_thms : thm Item_Net.T,
    dest_thms : thm Item_Net.T,
    app_thms : thm Item_Net.T }
  val empty = {
    concrete_thms = Thm.full_rules,
    generic_thms = Thm.full_rules,
    dest_thms = Thm.full_rules,
    app_thms = Thm.full_rules};
  val extend = I;
  fun merge ({concrete_thms = ct1, generic_thms = gt1, dest_thms = dt1, app_thms = at1 },
      {concrete_thms = ct2, generic_thms = gt2, dest_thms = dt2, app_thms = at2 }) = {
    concrete_thms = Item_Net.merge (ct1, ct2),
    generic_thms = Item_Net.merge (gt1, gt2),
    dest_thms = Item_Net.merge (dt1, dt2),
    app_thms = Item_Net.merge (at1, at2) };
);

val debug =
  Attrib.setup_config_bool @{binding measurable_debug} (K false)

val backtrack =
  Attrib.setup_config_int @{binding measurable_backtrack} (K 20)

val split =
  Attrib.setup_config_bool @{binding measurable_split} (K true)

fun TAKE n tac = Seq.take n o tac

fun get lv =
  rev o Item_Net.content o (case lv of Concrete => #concrete_thms | Generic => #generic_thms) o
  Data.get o Context.Proof;

fun get_all ctxt = get Concrete ctxt @ get Generic ctxt;

fun map_data f1 f2 f3 f4
  {generic_thms = t1,    concrete_thms = t2,    dest_thms = t3,    app_thms = t4} =
  {generic_thms = f1 t1, concrete_thms = f2 t2, dest_thms = f3 t3, app_thms = f4 t4 }

fun map_concrete_thms f = map_data f I I I
fun map_generic_thms f = map_data I f I I
fun map_dest_thms f = map_data I I f I
fun map_app_thms f = map_data I I I f

fun update f lv = Data.map (case lv of Concrete => map_concrete_thms f | Generic => map_generic_thms f);
fun add thms' = update (fold Item_Net.update thms');

val get_dest = Item_Net.content o #dest_thms o Data.get;
val add_dest = Data.map o map_dest_thms o Item_Net.update;

val get_app = Item_Net.content o #app_thms o Data.get;
val add_app = Data.map o map_app_thms o Item_Net.update;

fun is_too_generic thm =
  let 
    val concl = concl_of thm
    val concl' = HOLogic.dest_Trueprop concl handle TERM _ => concl
  in is_Var (head_of concl') end

fun import_theorem ctxt thm = if is_too_generic thm then [] else
  [thm] @ map_filter (try (fn th' => thm RS th')) (get_dest ctxt);

fun add_thm (raw, lv) thm ctxt = add (if raw then [thm] else import_theorem ctxt thm) lv ctxt;

fun debug_tac ctxt msg f = if Config.get ctxt debug then print_tac ctxt (msg ()) THEN f else f

fun nth_hol_goal thm i =
  HOLogic.dest_Trueprop (Logic.strip_imp_concl (strip_all_body (nth (prems_of thm) (i - 1))))

fun dest_measurable_fun t =
  (case t of
    (Const (@{const_name "Set.member"}, _) $ f $ (Const (@{const_name "measurable"}, _) $ _ $ _)) => f
  | _ => raise (TERM ("not a measurability predicate", [t])))

fun is_cond_formula n thm = if length (prems_of thm) < n then false else
  (case nth_hol_goal thm n of
    (Const (@{const_name "Set.member"}, _) $ _ $ (Const (@{const_name "sets"}, _) $ _)) => false
  | (Const (@{const_name "Set.member"}, _) $ _ $ (Const (@{const_name "measurable"}, _) $ _ $ _)) => false
  | _ => true)
  handle TERM _ => true;

fun indep (Bound i) t b = i < b orelse t <= i
  | indep (f $ t) top bot = indep f top bot andalso indep t top bot
  | indep (Abs (_,_,t)) top bot = indep t (top + 1) (bot + 1)
  | indep _ _ _ = true;

fun cnt_prefixes ctxt (Abs (n, T, t)) = let
      fun is_countable t = Type.of_sort (Proof_Context.tsig_of ctxt) (t, @{sort countable})
      fun cnt_walk (Abs (ns, T, t)) Ts =
          map (fn (t', t'') => (Abs (ns, T, t'), t'')) (cnt_walk t (T::Ts))
        | cnt_walk (f $ g) Ts = let
            val n = length Ts - 1
          in
            map (fn (f', t) => (f' $ g, t)) (cnt_walk f Ts) @
            map (fn (g', t) => (f $ g', t)) (cnt_walk g Ts) @
            (if is_countable (type_of1 (Ts, g)) andalso loose_bvar1 (g, n)
                andalso indep g n 0 andalso g <> Bound n
              then [(f $ Bound (n + 1), incr_boundvars (~ n) g)]
              else [])
          end
        | cnt_walk _ _ = []
    in map (fn (t1, t2) => let
        val T1 = type_of1 ([T], t2)
        val T2 = type_of1 ([T], t)
      in ([SOME (Abs (n, T1, Abs (n, T, t1))), NONE, NONE, SOME (Abs (n, T, t2))],
        [SOME T1, SOME T, SOME T2])
      end) (cnt_walk t [T])
    end
  | cnt_prefixes _ _ = []

val split_countable_tac =
  Subgoal.FOCUS (fn {context = ctxt, ...} => SUBGOAL (fn (t, i) =>
    let
      val f = dest_measurable_fun (HOLogic.dest_Trueprop t)
      fun cert f = map (Option.map (f (Proof_Context.theory_of ctxt)))
      fun inst t (ts, Ts) = Drule.instantiate' (cert ctyp_of Ts) (cert cterm_of ts) t
      val cps = cnt_prefixes ctxt f |> map (inst @{thm measurable_compose_countable})
    in if null cps then no_tac else debug_tac ctxt (K "split countable fun") (resolve_tac cps i) end
    handle TERM _ => no_tac) 1)

fun measurable_tac' ctxt facts =
  let
    val imported_thms =
      (maps (import_theorem (Context.Proof ctxt) o Simplifier.norm_hhf ctxt) facts) @ get_all ctxt

    fun debug_facts msg () =
      msg ^ " + " ^ Pretty.str_of (Pretty.list "[" "]"
        (map (Syntax.pretty_term ctxt o prop_of) (maps (import_theorem (Context.Proof ctxt)) facts)));

    val splitter = if Config.get ctxt split then split_countable_tac ctxt else K no_tac

    val split_app_tac =
      Subgoal.FOCUS (fn {context = ctxt, ...} => SUBGOAL (fn (t, i) =>
        let
          fun app_prefixes (Abs (n, T, (f $ g))) = let
                val ps = (if not (loose_bvar1 (g, 0)) then [(f, g)] else [])
              in map (fn (f, c) => (Abs (n, T, f), c, T, type_of c, type_of1 ([T], f $ c))) ps end
            | app_prefixes _ = []

          fun dest_app (Abs (_, T, t as ((f $ Bound 0) $ c))) = (f, c, T, type_of c, type_of1 ([T], t))
            | dest_app t = raise (TERM ("not a measurability predicate of an application", [t]))
          val thy = Proof_Context.theory_of ctxt
          val tunify = Sign.typ_unify thy
          val thms = map
              (fn thm => (thm, dest_app (dest_measurable_fun (HOLogic.dest_Trueprop (concl_of thm)))))
              (get_app (Context.Proof ctxt))
          fun cert f = map (fn (t, t') => (f thy t, f thy t'))
          fun inst (f, c, T, Tc, Tf) (thm, (thmf, thmc, thmT, thmTc, thmTf)) =
            let
              val inst =
                (Vartab.empty, ~1)
                |> tunify (T, thmT)
                |> tunify (Tf, thmTf)
                |> tunify (Tc, thmTc)
                |> Vartab.dest o fst
              val subst = subst_TVars (map (apsnd snd) inst)
            in
              Thm.instantiate (cert ctyp_of (map (fn (n, (s, T)) => (TVar (n, s), T)) inst),
                cert cterm_of [(subst thmf, f), (subst thmc, c)]) thm
            end
          val cps = map_product inst (app_prefixes (dest_measurable_fun (HOLogic.dest_Trueprop t))) thms
        in if null cps then no_tac
            else debug_tac ctxt (K ("split app fun")) (resolve_tac cps i)
              ORELSE debug_tac ctxt (fn () => "FAILED") no_tac end
        handle TERM t => debug_tac ctxt (fn () => "TERM " ^ fst t ^ Pretty.str_of (Pretty.list "[" "]" (map (Syntax.pretty_term ctxt) (snd t)))) no_tac
        handle Type.TUNIFY => debug_tac ctxt (fn () => "TUNIFY") no_tac) 1)

    fun REPEAT_cnt f n st = ((f n THEN REPEAT_cnt f (n + 1)) ORELSE all_tac) st

    val depth_measurable_tac = REPEAT_cnt (fn n =>
       (COND (is_cond_formula 1)
        (debug_tac ctxt (K ("simp " ^ string_of_int n)) (SOLVED' (asm_full_simp_tac ctxt) 1))
        ((debug_tac ctxt (K ("single " ^ string_of_int n)) (resolve_tac imported_thms 1)) APPEND
          (split_app_tac ctxt 1) APPEND
          (splitter 1)))) 0

  in debug_tac ctxt (debug_facts "start") depth_measurable_tac end;

fun measurable_tac ctxt facts =
  TAKE (Config.get ctxt backtrack) (measurable_tac' ctxt facts);

fun simproc ctxt redex =
  let
    val t = HOLogic.mk_Trueprop (term_of redex);
    fun tac {context = ctxt, prems = _ } =
      SOLVE (measurable_tac' ctxt (Simplifier.prems_of ctxt));
  in try (fn () => Goal.prove ctxt [] [] t tac RS @{thm Eq_TrueI}) () end;

end

