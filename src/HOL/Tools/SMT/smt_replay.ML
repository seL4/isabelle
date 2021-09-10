(*  Title:      HOL/Tools/SMT/smt_replay.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Mathias Fleury, MPII

Shared library for parsing and replay.
*)

signature SMT_REPLAY =
sig
  (*theorem nets*)
  val thm_net_of: ('a -> thm) -> 'a list -> 'a Net.net
  val net_instances: (int * thm) Net.net -> cterm -> (int * thm) list

  (*proof combinators*)
  val under_assumption: (thm -> thm) -> cterm -> thm
  val discharge: thm -> thm -> thm

  (*a faster COMP*)
  type compose_data = cterm list * (cterm -> cterm list) * thm
  val precompose: (cterm -> cterm list) -> thm -> compose_data
  val precompose2: (cterm -> cterm * cterm) -> thm -> compose_data
  val compose: compose_data -> thm -> thm

  (*simpset*)
  val add_simproc: Simplifier.simproc -> Context.generic -> Context.generic
  val make_simpset: Proof.context -> thm list -> simpset

  (*assertion*)
  val add_asserted:  ('a * ('b * thm) -> 'c -> 'c) ->
    'c -> ('d -> 'a * 'e * term * 'b) -> ('e -> bool) -> Proof.context -> thm list ->
    (int * thm) list -> 'd list -> Proof.context ->
    ((int * ('a * thm)) list * thm list) * (Proof.context * 'c)
  
  (*statistics*)
  val pretty_statistics: string -> int -> int list Symtab.table -> Pretty.T
  val intermediate_statistics: Proof.context -> Timing.start -> int -> int -> unit

  (*theorem transformation*)
  val varify: Proof.context -> thm -> thm
  val params_of: term -> (string * typ) list

  (*spy*)
  val spying: bool -> Proof.context -> (unit -> string) -> string -> unit
  val print_stats: (string * int list) list -> string
end;

structure SMT_Replay : SMT_REPLAY =
struct

(* theorem nets *)

fun thm_net_of f xthms =
  let fun insert xthm = Net.insert_term (K false) (Thm.prop_of (f xthm), xthm)
  in fold insert xthms Net.empty end

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

local
  fun instances_from_net match f net ct =
    let
      val lookup = if match then Net.match_term else Net.unify_term
      val xthms = lookup net (Thm.term_of ct)
      fun select ct = map_filter (f (maybe_instantiate ct)) xthms
      fun select' ct =
        let val thm = Thm.trivial ct
        in map_filter (f (try (fn rule => rule COMP thm))) xthms end
    in (case select ct of [] => select' ct | xthms' => xthms') end
in

fun net_instances net =
  instances_from_net false (fn f => fn (i, thm) => Option.map (pair i) (f thm))
    net

end


(* proof combinators *)

fun under_assumption f ct =
  let val ct' = SMT_Util.mk_cprop ct in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun discharge p pq = Thm.implies_elim pq p


(* a faster COMP *)

type compose_data = cterm list * (cterm -> cterm list) * thm

fun list2 (x, y) = [x, y]

fun precompose f rule : compose_data = (f (Thm.cprem_of rule 1), f, rule)
fun precompose2 f rule : compose_data = precompose (list2 o f) rule

fun compose (cvs, f, rule) thm =
  discharge thm
    (Thm.instantiate
      (TVars.empty, Vars.make (map (dest_Var o Thm.term_of) cvs ~~ f (Thm.cprop_of thm))) rule)


(* simpset *)

local
  val antisym_le1 = mk_meta_eq @{thm order_class.antisym_conv}
  val antisym_le2 = mk_meta_eq @{thm order_class.antisym_conv2}
  val antisym_less1 = mk_meta_eq @{thm order_class.antisym_conv1}
  val antisym_less2 = mk_meta_eq @{thm linorder_class.antisym_conv3}

  fun eq_prop t thm = HOLogic.mk_Trueprop t aconv Thm.prop_of thm
  fun dest_binop ((c as Const _) $ t $ u) = (c, t, u)
    | dest_binop t = raise TERM ("dest_binop", [t])

  fun prove_antisym_le ctxt ct =
    let
      val (le, r, s) = dest_binop (Thm.term_of ct)
      val less = Const (\<^const_name>\<open>less\<close>, Term.fastype_of le)
      val prems = Simplifier.prems_of ctxt
    in
      (case find_first (eq_prop (le $ s $ r)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ r $ s))) prems
          |> Option.map (fn thm => thm RS antisym_less1)
      | SOME thm => SOME (thm RS antisym_le1))
    end
    handle THM _ => NONE

  fun prove_antisym_less ctxt ct =
    let
      val (less, r, s) = dest_binop (HOLogic.dest_not (Thm.term_of ct))
      val le = Const (\<^const_name>\<open>less_eq\<close>, Term.fastype_of less)
      val prems = Simplifier.prems_of ctxt
    in
      (case find_first (eq_prop (le $ r $ s)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ s $ r))) prems
          |> Option.map (fn thm => thm RS antisym_less2)
      | SOME thm => SOME (thm RS antisym_le2))
  end
  handle THM _ => NONE

  val basic_simpset =
    simpset_of (put_simpset HOL_ss \<^context>
      addsimps @{thms field_simps times_divide_eq_right times_divide_eq_left arith_special
        arith_simps rel_simps array_rules z3div_def z3mod_def NO_MATCH_def}
      addsimprocs [\<^simproc>\<open>numeral_divmod\<close>,
        Simplifier.make_simproc \<^context> "fast_int_arith"
         {lhss = [\<^term>\<open>(m::int) < n\<close>, \<^term>\<open>(m::int) \<le> n\<close>, \<^term>\<open>(m::int) = n\<close>],
          proc = K Lin_Arith.simproc},
        Simplifier.make_simproc \<^context> "antisym_le"
         {lhss = [\<^term>\<open>(x::'a::order) \<le> y\<close>],
          proc = K prove_antisym_le},
        Simplifier.make_simproc \<^context> "antisym_less"
         {lhss = [\<^term>\<open>\<not> (x::'a::linorder) < y\<close>],
          proc = K prove_antisym_less}])

  structure Simpset = Generic_Data
  (
    type T = simpset
    val empty = basic_simpset
    val extend = I
    val merge = Simplifier.merge_ss
  )
in

fun add_simproc simproc context =
  Simpset.map (simpset_map (Context.proof_of context)
    (fn ctxt => ctxt addsimprocs [simproc])) context

fun make_simpset ctxt rules =
  simpset_of (put_simpset (Simpset.get (Context.Proof ctxt)) ctxt addsimps rules)

end

local
  val remove_trigger = mk_meta_eq @{thm trigger_def}
  val remove_fun_app = mk_meta_eq @{thm fun_app_def}

  fun rewrite_conv _ [] = Conv.all_conv
    | rewrite_conv ctxt eqs = Simplifier.full_rewrite (empty_simpset ctxt addsimps eqs)

  val rewrite_true_rule = @{lemma "True \<equiv> \<not> False" by simp}
  val prep_rules = [@{thm Let_def}, remove_trigger, remove_fun_app, rewrite_true_rule]

  fun rewrite _ [] = I
    | rewrite ctxt eqs = Conv.fconv_rule (rewrite_conv ctxt eqs)

  fun lookup_assm assms_net ct =
    net_instances assms_net ct
    |> map (fn ithm as (_, thm) => (ithm, Thm.cprop_of thm aconvc ct))
in

fun add_asserted tab_update tab_empty p_extract cond outer_ctxt rewrite_rules assms steps ctxt0 =
  let
    val eqs = map (rewrite ctxt0 [rewrite_true_rule]) rewrite_rules
    val eqs' = union Thm.eq_thm eqs prep_rules

    val assms_net =
      assms
      |> map (apsnd (rewrite ctxt0 eqs'))
      |> map (apsnd (Conv.fconv_rule Thm.eta_conversion))
      |> thm_net_of snd

    fun revert_conv ctxt = rewrite_conv ctxt eqs' then_conv Thm.eta_conversion

    fun assume thm ctxt =
      let
        val ct = Thm.cprem_of thm 1
        val (thm', ctxt') = yield_singleton Assumption.add_assumes ct ctxt
      in (thm' RS thm, ctxt') end

    fun add1 id fixes thm1 ((i, th), exact) ((iidths, thms), (ctxt, ptab)) =
      let
        val (thm, ctxt') = if exact then (Thm.implies_elim thm1 th, ctxt) else assume thm1 ctxt
        val thms' = if exact then thms else th :: thms
      in (((i, (id, th)) :: iidths, thms'), (ctxt', tab_update (id, (fixes, thm)) ptab)) end

    fun add step
        (cx as ((iidths, thms), (ctxt, ptab))) =
      let val (id, rule, concl, fixes) = p_extract step in
        if (*Z3_Proof.is_assumption rule andalso rule <> Z3_Proof.Hypothesis*) cond rule then
          let
            val ct = Thm.cterm_of ctxt concl
            val thm1 = Thm.trivial ct |> Conv.fconv_rule (Conv.arg1_conv (revert_conv outer_ctxt))
            val thm2 = singleton (Variable.export ctxt outer_ctxt) thm1
          in
            (case lookup_assm assms_net (Thm.cprem_of thm2 1) of
              [] =>
                let val (thm, ctxt') = assume thm1 ctxt
                in ((iidths, thms), (ctxt', tab_update (id, (fixes, thm)) ptab)) end
            | ithms => fold (add1 id fixes thm1) ithms cx)
          end
        else
          cx
      end
  in fold add steps (([], []), (ctxt0, tab_empty)) end

end

fun params_of t = Term.strip_qnt_vars \<^const_name>\<open>Pure.all\<close> t

fun varify ctxt thm =
  let
    val maxidx = Thm.maxidx_of thm + 1
    val vs = params_of (Thm.prop_of thm)
    val vars = map_index (fn (i, (n, T)) => Var ((n, i + maxidx), T)) vs
  in Drule.forall_elim_list (map (Thm.cterm_of ctxt) vars) thm end

fun intermediate_statistics ctxt start total =
  SMT_Config.statistics_msg ctxt (fn current =>
    "Reconstructed " ^ string_of_int current ^ " of " ^ string_of_int total ^ " steps in " ^
    string_of_int (Time.toMilliseconds (#elapsed (Timing.result start))) ^ " ms")

fun pretty_statistics solver total stats =
  let
    val stats = Symtab.map (K (map (fn i => curry Int.div i 1000000))) stats
    fun mean_of is =
      let
        val len = length is
        val mid = len div 2
      in if len mod 2 = 0 then (nth is (mid - 1) + nth is mid) div 2 else nth is mid end
    fun pretty_item name p = Pretty.item (Pretty.separate ":" [Pretty.str name, p])
    fun pretty (name, milliseconds) = (Pretty.block (Pretty.str (name ^": ")  :: Pretty.separate "," [
      Pretty.str (string_of_int (length milliseconds) ^ " occurrences") ,
      Pretty.str (string_of_int (mean_of milliseconds) ^ " ms mean time"),
      Pretty.str (string_of_int (fold Integer.max milliseconds 0) ^ " ms maximum time"),
      Pretty.str (string_of_int (fold Integer.add milliseconds 0) ^ " ms total time")]))
  in
    Pretty.big_list (solver ^ " proof reconstruction statistics:") (
      pretty_item "total time" (Pretty.str (string_of_int total ^ " ms")) ::
      map pretty (Symtab.dest stats))
  end

fun timestamp_format time =
  Date.fmt "%Y-%m-%d %H:%M:%S." (Date.fromTimeLocal time) ^
  (StringCvt.padLeft #"0" 3 (string_of_int (Time.toMilliseconds time - 1000 * Time.toSeconds time)))

fun print_stats stats =
  let
    fun print_list xs = fold (fn x => fn msg => msg ^ string_of_int x ^ ",") xs ""
  in
    fold (fn (x,y) => fn msg => msg ^ x ^ ": " ^ print_list y ^ "\n") stats ""
  end

fun spying false _ _ _ = ()
  | spying true ctxt f filename =
    let
      val message = f ()
      val thy = Context.theory_long_name ((Context.theory_of o Context.Proof) ctxt)
      val spying_version = "1"
    in
      File.append (Path.explode ("$ISABELLE_HOME_USER/" ^ filename))
        (spying_version ^ "; " ^ thy ^ "; " ^ (timestamp_format (Time.now ())) ^ ";\n" ^ message ^ "\n")
    end

end;
