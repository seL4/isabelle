(*  Title:      HOL/Analysis/measurable.ML
    Author:     Johannes Hölzl <hoelzl@in.tum.de>

Measurability prover.
*)

signature MEASURABLE = 
sig
  type preprocessor = thm -> Proof.context -> (thm list * Proof.context)

  datatype level = Concrete | Generic

  val dest_thm_attr : attribute context_parser
  val cong_thm_attr : attribute context_parser
  val measurable_thm_attr : bool * (bool * level) -> attribute

  val add_del_cong_thm : bool -> thm -> Context.generic -> Context.generic ;

  val get_all : Context.generic -> thm list
  val get_dest : Context.generic -> thm list
  val get_cong : Context.generic -> thm list

  val measurable_tac : Proof.context -> thm list -> tactic

  val simproc : Proof.context -> cterm -> thm option

  val add_preprocessor : string -> preprocessor -> Context.generic -> Context.generic
  val del_preprocessor : string -> Context.generic -> Context.generic
  val add_local_cong : thm -> Proof.context -> Proof.context

  val prepare_facts : Proof.context -> thm list -> (thm list * Proof.context)
end ;

structure Measurable : MEASURABLE =
struct

type preprocessor = thm -> Proof.context -> (thm list * Proof.context)

datatype level = Concrete | Generic;

fun eq_measurable_thms ((th1, d1), (th2, d2)) = 
  d1 = d2 andalso Thm.eq_thm_prop (th1, th2) ;

fun merge_dups (xs:(string * preprocessor) list) ys =
  xs @ (filter (fn (name, _) => is_none (find_first (fn (name', _) => name' = name) xs)) ys) 

structure Data = Generic_Data
(
  type T = {
    measurable_thms : (thm * (bool * level)) Item_Net.T,
    dest_thms : thm Item_Net.T,
    cong_thms : thm Item_Net.T,
    preprocessors : (string * preprocessor) list }
  val empty: T = {
    measurable_thms = Item_Net.init eq_measurable_thms (single o Thm.prop_of o fst),
    dest_thms = Thm.full_rules,
    cong_thms = Thm.full_rules,
    preprocessors = [] };
  val extend = I;
  fun merge ({measurable_thms = t1, dest_thms = dt1, cong_thms = ct1, preprocessors = i1 },
      {measurable_thms = t2, dest_thms = dt2, cong_thms = ct2, preprocessors = i2 }) : T = {
    measurable_thms = Item_Net.merge (t1, t2),
    dest_thms = Item_Net.merge (dt1, dt2),
    cong_thms = Item_Net.merge (ct1, ct2),
    preprocessors = merge_dups i1 i2 
    };
);

val debug =
  Attrib.setup_config_bool \<^binding>\<open>measurable_debug\<close> (K false)

val split =
  Attrib.setup_config_bool \<^binding>\<open>measurable_split\<close> (K true)

fun map_data f1 f2 f3 f4
  {measurable_thms = t1,    dest_thms = t2,    cong_thms = t3,    preprocessors = t4 } =
  {measurable_thms = f1 t1, dest_thms = f2 t2, cong_thms = f3 t3, preprocessors = f4 t4}

fun map_measurable_thms f = map_data f I I I
fun map_dest_thms f = map_data I f I I
fun map_cong_thms f = map_data I I f I
fun map_preprocessors f = map_data I I I f

fun generic_add_del map : attribute context_parser =
  Scan.lift
    (Args.add >> K Item_Net.update || Args.del >> K Item_Net.remove || Scan.succeed Item_Net.update) >>
    (fn f => Thm.declaration_attribute (Data.map o map o f))

val dest_thm_attr = generic_add_del map_dest_thms

val cong_thm_attr = generic_add_del map_cong_thms

fun del_thm th net =
  let
    val thms = net |> Item_Net.content |> filter (fn (th', _) => Thm.eq_thm (th, th'))
  in fold Item_Net.remove thms net end ;

fun measurable_thm_attr (do_add, d) = Thm.declaration_attribute
  (Data.map o map_measurable_thms o (if do_add then Item_Net.update o rpair d else del_thm))

val get_dest = Item_Net.content o #dest_thms o Data.get;

val get_cong = Item_Net.content o #cong_thms o Data.get;
val add_cong = Data.map o map_cong_thms o Item_Net.update;
val del_cong = Data.map o map_cong_thms o Item_Net.remove;
fun add_del_cong_thm true = add_cong
  | add_del_cong_thm false = del_cong

fun add_preprocessor name f = Data.map (map_preprocessors (fn xs => xs @ [(name, f)]))
fun del_preprocessor name = Data.map (map_preprocessors (filter (fn (n, _) => n <> name)))
val add_local_cong = Context.proof_map o add_cong

val get_preprocessors = Context.Proof #> Data.get #> #preprocessors ;

fun is_too_generic thm =
  let 
    val concl = Thm.concl_of thm
    val concl' = HOLogic.dest_Trueprop concl handle TERM _ => concl
  in is_Var (head_of concl') end

val get_thms = Data.get #> #measurable_thms #> Item_Net.content ;

val get_all = get_thms #> map fst ;

fun debug_tac ctxt msg f =
  if Config.get ctxt debug then print_tac ctxt (msg ()) THEN f else f

fun nth_hol_goal thm i =
  HOLogic.dest_Trueprop (Logic.strip_imp_concl (strip_all_body (nth (Thm.prems_of thm) (i - 1))))

fun dest_measurable_fun t =
  (case t of
    (Const (\<^const_name>\<open>Set.member\<close>, _) $ f $ (Const (\<^const_name>\<open>measurable\<close>, _) $ _ $ _)) => f
  | _ => raise (TERM ("not a measurability predicate", [t])))

fun not_measurable_prop n thm =
  if length (Thm.prems_of thm) < n then false
  else
    (case nth_hol_goal thm n of
      (Const (\<^const_name>\<open>Set.member\<close>, _) $ _ $ (Const (\<^const_name>\<open>sets\<close>, _) $ _)) => false
    | (Const (\<^const_name>\<open>Set.member\<close>, _) $ _ $ (Const (\<^const_name>\<open>measurable\<close>, _) $ _ $ _)) => false
    | _ => true)
    handle TERM _ => true;

fun indep (Bound i) t b = i < b orelse t <= i
  | indep (f $ t) top bot = indep f top bot andalso indep t top bot
  | indep (Abs (_,_,t)) top bot = indep t (top + 1) (bot + 1)
  | indep _ _ _ = true;

fun cnt_prefixes ctxt (Abs (n, T, t)) =
    let
      fun is_countable ty = Sign.of_sort (Proof_Context.theory_of ctxt) (ty, \<^sort>\<open>countable\<close>)
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

fun apply_dests thm dests =
  let
    fun apply thm th' =
      let
        val th'' = thm RS th'
      in [th''] @ loop th'' end
      handle (THM _) => []
    and loop thm =
      flat (map (apply thm) dests)
  in
    [thm] @ ([thm RS @{thm measurable_compose_rev}] handle (THM _) => []) @ loop thm
  end

fun prepare_facts ctxt facts = 
  let
    val dests = get_dest (Context.Proof ctxt)
    fun prep_dest thm =
      (if is_too_generic thm then [] else apply_dests thm dests) ;
    val preprocessors = (("std", prep_dest #> pair) :: get_preprocessors ctxt) ;
    fun preprocess_thm (thm, raw) =
      if raw then pair [thm] else fold_map (fn (_, proc) => proc thm) preprocessors #>> flat
    
    fun sel lv (th, (raw, lv')) = if lv = lv' then SOME (th, raw) else NONE ;
    fun get lv = ctxt |> Context.Proof |> get_thms |> rev |> map_filter (sel lv) ;
    val pre_thms = map (Simplifier.norm_hhf ctxt #> rpair false) facts @ get Concrete @ get Generic

    val (thms, ctxt) = fold_map preprocess_thm pre_thms ctxt |>> flat
  in (thms, ctxt) end

fun measurable_tac ctxt facts =
  let
    fun debug_fact msg thm () =
      msg ^ " " ^ Pretty.unformatted_string_of (Syntax.pretty_term ctxt (Thm.prop_of thm))

    fun IF' c t i = COND (c i) (t i) no_tac

    fun r_tac msg =
      if Config.get ctxt debug
      then FIRST' o
        map (fn thm => resolve_tac ctxt [thm]
          THEN' K (debug_tac ctxt (debug_fact (msg ^ " resolved using") thm) all_tac))
      else resolve_tac ctxt

    val elem_congI = @{lemma "A = B \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A" by simp}

    val (thms, ctxt) = prepare_facts ctxt facts

    fun is_sets_eq (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
          (Const (\<^const_name>\<open>sets\<close>, _) $ _) $
          (Const (\<^const_name>\<open>sets\<close>, _) $ _)) = true
      | is_sets_eq (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
          (Const (\<^const_name>\<open>measurable\<close>, _) $ _ $ _) $
          (Const (\<^const_name>\<open>measurable\<close>, _) $ _ $ _)) = true
      | is_sets_eq _ = false

    val cong_thms = get_cong (Context.Proof ctxt) @
      filter (fn thm => Thm.concl_of thm |> HOLogic.dest_Trueprop |> is_sets_eq handle TERM _ => false) facts

    fun sets_cong_tac i =
      Subgoal.FOCUS (fn {context = ctxt', prems = prems, ...} => (
        let
          val ctxt'' = Simplifier.add_prems prems ctxt'
        in
          r_tac "cong intro" [elem_congI]
          THEN' SOLVED' (fn i => REPEAT_DETERM (
              ((r_tac "cong solve" (cong_thms @ [@{thm refl}])
                ORELSE' IF' (fn i => fn thm => Thm.nprems_of thm > i)
                  (SOLVED' (asm_full_simp_tac ctxt''))) i)))
        end) 1) ctxt i
        THEN flexflex_tac ctxt

    val simp_solver_tac = 
      IF' not_measurable_prop (debug_tac ctxt (K "simp ") o SOLVED' (asm_full_simp_tac ctxt))

    val split_countable_tac =
      Subgoal.FOCUS (fn {context = ctxt, ...} => SUBGOAL (fn (t, i) =>
        let
          val f = dest_measurable_fun (HOLogic.dest_Trueprop t)
          fun inst (ts, Ts) =
            Thm.instantiate'
              (map (Option.map (Thm.ctyp_of ctxt)) Ts)
              (map (Option.map (Thm.cterm_of ctxt)) ts)
              @{thm measurable_compose_countable}
        in r_tac "case_prod countable" (cnt_prefixes ctxt f |> map inst) i end
        handle TERM _ => no_tac) 1)

    val splitter = if Config.get ctxt split then split_countable_tac ctxt else K no_tac

    val single_step_tac =
      simp_solver_tac
      ORELSE' r_tac "step" thms
      ORELSE' splitter
      ORELSE' (CHANGED o sets_cong_tac)
      ORELSE' (K (debug_tac ctxt (K "backtrack") no_tac))

  in debug_tac ctxt (K "start") (REPEAT (single_step_tac 1)) end;

fun simproc ctxt redex =
  let
    val t = HOLogic.mk_Trueprop (Thm.term_of redex);
    fun tac {context = ctxt, prems = _ } =
      SOLVE (measurable_tac ctxt (Simplifier.prems_of ctxt));
  in \<^try>\<open>Goal.prove ctxt [] [] t tac RS @{thm Eq_TrueI}\<close> end;

end

