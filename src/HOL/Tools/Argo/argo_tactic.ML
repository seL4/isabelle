(*  Title:      HOL/Tools/Argo/argo_tactic.ML
    Author:     Sascha Boehme

HOL method and tactic for the Argo solver.
*)

signature ARGO_TACTIC =
sig
  val trace: string Config.T
  val timeout: real Config.T

  (* extending the tactic *)
  type trans_context =
    Name.context * Argo_Expr.typ Typtab.table * (string * Argo_Expr.typ) Termtab.table
  type ('a, 'b) trans = 'a -> trans_context -> 'b * trans_context
  type ('a, 'b) trans' = 'a -> trans_context -> ('b * trans_context) option
  type extension = {
    trans_type: (typ, Argo_Expr.typ) trans -> (typ, Argo_Expr.typ) trans',
    trans_term: (term, Argo_Expr.expr) trans -> (term, Argo_Expr.expr) trans',
    term_of: (Argo_Expr.expr -> term) -> Argo_Expr.expr -> term option,
    replay_rewr: Proof.context -> Argo_Proof.rewrite -> conv,
    replay: (Argo_Expr.expr -> cterm) -> Proof.context -> Argo_Proof.rule -> thm list -> thm option}
  val add_extension: extension -> theory -> theory

  (* proof utilities *)
  val discharges: thm -> thm list -> thm list
  val flatten_conv: conv -> thm -> conv

  (* interface to the tactic as well as the underlying checker and prover *)
  datatype result = Satisfiable of term -> bool option | Unsatisfiable
  val check: term list -> Proof.context -> result * Proof.context
  val prove: thm list -> Proof.context -> thm option * Proof.context
  val argo_tac: Proof.context -> thm list -> int -> tactic
end

structure Argo_Tactic: ARGO_TACTIC =
struct

(* readable fresh names for terms *)

fun fresh_name n = Name.variant (case Long_Name.base_name n of "" => "x" | n' => n')

fun fresh_type_name (Type (n, _)) = fresh_name n
  | fresh_type_name (TFree (n, _)) = fresh_name n
  | fresh_type_name (TVar ((n, i), _)) = fresh_name (n ^ "." ^ string_of_int i)

fun fresh_term_name (Const (n, _)) = fresh_name n
  | fresh_term_name (Free (n, _)) = fresh_name n
  | fresh_term_name (Var ((n, i), _)) = fresh_name (n ^ "." ^ string_of_int i)
  | fresh_term_name _ = fresh_name ""


(* tracing *)

datatype mode = None | Basic | Full

fun string_of_mode None = "none"
  | string_of_mode Basic = "basic"
  | string_of_mode Full = "full"

fun requires_mode None = []
  | requires_mode Basic = [Basic, Full]
  | requires_mode Full = [Full]

val trace = Attrib.setup_config_string \<^binding>\<open>argo_trace\<close> (K (string_of_mode None))

fun allows_mode ctxt = exists (equal (Config.get ctxt trace) o string_of_mode) o requires_mode

fun output mode ctxt msg = if allows_mode ctxt mode then Output.tracing ("Argo: " ^ msg) else ()
val tracing = output Basic
val full_tracing = output Full

fun with_mode mode ctxt f = if allows_mode ctxt mode then f ctxt else ()
val with_tracing = with_mode Basic
val with_full_tracing = with_mode Full


(* timeout *)

val timeout = Attrib.setup_config_real \<^binding>\<open>argo_timeout\<close> (K 10.0)

val timeout_seconds = seconds o Config.apply timeout

fun with_timeout ctxt f x = Timeout.apply (timeout_seconds ctxt) f x


(* extending the tactic *)

type trans_context =
  Name.context * Argo_Expr.typ Typtab.table * (string * Argo_Expr.typ) Termtab.table

type ('a, 'b) trans = 'a -> trans_context -> 'b * trans_context
type ('a, 'b) trans' = 'a -> trans_context -> ('b * trans_context) option

type extension = {
  trans_type: (typ, Argo_Expr.typ) trans -> (typ, Argo_Expr.typ) trans',
  trans_term: (term, Argo_Expr.expr) trans -> (term, Argo_Expr.expr) trans',
  term_of: (Argo_Expr.expr -> term) -> Argo_Expr.expr -> term option,
  replay_rewr: Proof.context -> Argo_Proof.rewrite -> conv,
  replay: (Argo_Expr.expr -> cterm) -> Proof.context -> Argo_Proof.rule -> thm list -> thm option}

fun eq_extension ((serial1, _), (serial2, _)) = (serial1 = serial2)

structure Extensions = Theory_Data
(
  type T = (serial * extension) list
  val empty = []
  val extend = I
  val merge = merge eq_extension 
)

fun add_extension ext = Extensions.map (insert eq_extension (serial (), ext))
fun get_extensions ctxt = Extensions.get (Proof_Context.theory_of ctxt)
fun apply_first ctxt f = get_first (fn (_, e) => f e) (get_extensions ctxt)

fun ext_trans sel ctxt f x tcx = apply_first ctxt (fn ext => sel ext f x tcx)

val ext_trans_type = ext_trans (fn {trans_type, ...}: extension => trans_type)
val ext_trans_term = ext_trans (fn {trans_term, ...}: extension => trans_term)

fun ext_term_of ctxt f e = apply_first ctxt (fn {term_of, ...}: extension => term_of f e)

fun ext_replay_rewr ctxt r = 
  get_extensions ctxt
  |> map (fn (_, {replay_rewr, ...}: extension) => replay_rewr ctxt r)
  |> Conv.first_conv

fun ext_replay cprop_of ctxt rule prems =
  (case apply_first ctxt (fn {replay, ...}: extension => replay cprop_of ctxt rule prems) of
    SOME thm => thm
  | NONE => raise THM ("failed to replay " ^ quote (Argo_Proof.string_of_rule rule), 0, []))


(* translating input terms *)

fun add_new_type T (names, types, terms) =
  let
    val (n, names') = fresh_type_name T names
    val ty = Argo_Expr.Type n
  in (ty, (names', Typtab.update (T, ty) types, terms)) end

fun add_type T (tcx as (_, types, _)) =
  (case Typtab.lookup types T of
    SOME ty => (ty, tcx)
  | NONE => add_new_type T tcx)

fun trans_type _ \<^typ>\<open>HOL.bool\<close> = pair Argo_Expr.Bool
  | trans_type ctxt (Type (\<^type_name>\<open>fun\<close>, [T1, T2])) =
      trans_type ctxt T1 ##>> trans_type ctxt T2 #>> Argo_Expr.Func
  | trans_type ctxt T = (fn tcx =>
      (case ext_trans_type ctxt (trans_type ctxt) T tcx of
        SOME result => result
      | NONE => add_type T tcx))

fun add_new_term ctxt t T tcx =
  let
    val (ty, (names, types, terms)) = trans_type ctxt T tcx
    val (n, names') = fresh_term_name t names
    val c = (n, ty)
  in (Argo_Expr.mk_con c, (names', types, Termtab.update (t, c) terms)) end

fun add_term ctxt t (tcx as (_, _, terms)) =
  (case Termtab.lookup terms t of
    SOME c => (Argo_Expr.mk_con c, tcx)
  | NONE => add_new_term ctxt t (Term.fastype_of t) tcx)

fun mk_eq \<^typ>\<open>HOL.bool\<close> = Argo_Expr.mk_iff
  | mk_eq _ = Argo_Expr.mk_eq

fun trans_term _ \<^const>\<open>HOL.True\<close> = pair Argo_Expr.true_expr
  | trans_term _ \<^const>\<open>HOL.False\<close> = pair Argo_Expr.false_expr
  | trans_term ctxt (\<^const>\<open>HOL.Not\<close> $ t) = trans_term ctxt t #>> Argo_Expr.mk_not
  | trans_term ctxt (\<^const>\<open>HOL.conj\<close> $ t1 $ t2) =
      trans_term ctxt t1 ##>> trans_term ctxt t2 #>> uncurry Argo_Expr.mk_and2
  | trans_term ctxt (\<^const>\<open>HOL.disj\<close> $ t1 $ t2) =
      trans_term ctxt t1 ##>> trans_term ctxt t2 #>> uncurry Argo_Expr.mk_or2
  | trans_term ctxt (\<^const>\<open>HOL.implies\<close> $ t1 $ t2) =
      trans_term ctxt t1 ##>> trans_term ctxt t2 #>> uncurry Argo_Expr.mk_imp
  | trans_term ctxt (Const (\<^const_name>\<open>HOL.If\<close>, _) $ t1 $ t2 $ t3) =
      trans_term ctxt t1 ##>> trans_term ctxt t2 ##>> trans_term ctxt t3 #>>
      (fn ((u1, u2), u3) => Argo_Expr.mk_ite u1 u2 u3)
  | trans_term ctxt (Const (\<^const_name>\<open>HOL.eq\<close>, T) $ t1 $ t2) =
      trans_term ctxt t1 ##>> trans_term ctxt t2 #>> uncurry (mk_eq (Term.domain_type T))
  | trans_term ctxt (t as (t1 $ t2)) = (fn tcx =>
      (case ext_trans_term ctxt (trans_term ctxt) t tcx of
        SOME result => result
      | NONE => tcx |> trans_term ctxt t1 ||>> trans_term ctxt t2 |>> uncurry Argo_Expr.mk_app))
  | trans_term ctxt t = (fn tcx =>
      (case ext_trans_term ctxt (trans_term ctxt) t tcx of
        SOME result => result
      | NONE => add_term ctxt t tcx))

fun translate ctxt prop = trans_term ctxt (HOLogic.dest_Trueprop prop)


(* invoking the solver *)

type data = {
  names: Name.context,
  types: Argo_Expr.typ Typtab.table,
  terms: (string * Argo_Expr.typ) Termtab.table,
  argo: Argo_Solver.context}

fun mk_data names types terms argo: data = {names=names, types=types, terms=terms, argo=argo}
val empty_data = mk_data Name.context Typtab.empty Termtab.empty Argo_Solver.context

structure Solver_Data = Proof_Data
(
  type T = data option
  fun init _ = SOME empty_data
)

datatype ('m, 'p) solver_result = Model of 'm | Proof of 'p

fun raw_solve es argo = Model (Argo_Solver.assert es argo)
  handle Argo_Proof.UNSAT proof => Proof proof

fun value_of terms model t =
  (case Termtab.lookup terms t of
    SOME c => model c
  | _ => NONE)

fun trace_props props ctxt =
  tracing ctxt (Pretty.string_of (Pretty.big_list "using these propositions:"
    (map (Syntax.pretty_term ctxt) props)))

fun trace_result ctxt ({elapsed, ...}: Timing.timing) msg =
  tracing ctxt ("found a " ^ msg ^ " in " ^ string_of_int (Time.toMilliseconds elapsed) ^ " ms")

fun solve props ctxt =
  (case Solver_Data.get ctxt of
    NONE => error "bad Argo solver context"
  | SOME {names, types, terms, argo} =>
      let
        val _ = with_tracing ctxt (trace_props props)
        val (es, (names', types', terms')) = fold_map (translate ctxt) props (names, types, terms)
        val _ = tracing ctxt "starting the prover"
      in
        (case Timing.timing (raw_solve es) argo of
          (time, Proof proof) =>
            let val _ = trace_result ctxt time "proof"
            in (Proof (terms', proof), Solver_Data.put NONE ctxt) end
        | (time, Model argo') =>
            let
              val _ = trace_result ctxt time "model"
              val model = value_of terms' (Argo_Solver.model_of argo')
            in (Model model, Solver_Data.put (SOME (mk_data names' types' terms' argo')) ctxt) end)
      end)


(* reverse translation *)

structure Contab = Table(type key = string * Argo_Expr.typ val ord = Argo_Expr.con_ord)

fun mk_nary f ts = uncurry (fold_rev (curry f)) (split_last ts)

fun mk_nary' d _ [] = d
  | mk_nary' _ f ts = mk_nary f ts

fun mk_ite t1 t2 t3 =
  let
    val T = Term.fastype_of t2
    val ite = Const (\<^const_name>\<open>HOL.If\<close>, [\<^typ>\<open>HOL.bool\<close>, T, T] ---> T)
  in ite $ t1 $ t2 $ t3 end

fun term_of _ (Argo_Expr.E (Argo_Expr.True, _)) = \<^const>\<open>HOL.True\<close>
  | term_of _ (Argo_Expr.E (Argo_Expr.False, _)) = \<^const>\<open>HOL.False\<close>
  | term_of cx (Argo_Expr.E (Argo_Expr.Not, [e])) = HOLogic.mk_not (term_of cx e)
  | term_of cx (Argo_Expr.E (Argo_Expr.And, es)) =
      mk_nary' \<^const>\<open>HOL.True\<close> HOLogic.mk_conj (map (term_of cx) es)
  | term_of cx (Argo_Expr.E (Argo_Expr.Or, es)) =
      mk_nary' \<^const>\<open>HOL.False\<close> HOLogic.mk_disj (map (term_of cx) es)
  | term_of cx (Argo_Expr.E (Argo_Expr.Imp, [e1, e2])) =
      HOLogic.mk_imp (term_of cx e1, term_of cx e2)
  | term_of cx (Argo_Expr.E (Argo_Expr.Iff, [e1, e2])) =
      HOLogic.mk_eq (term_of cx e1, term_of cx e2)
  | term_of cx (Argo_Expr.E (Argo_Expr.Ite, [e1, e2, e3])) =
      mk_ite (term_of cx e1) (term_of cx e2) (term_of cx e3)
  | term_of cx (Argo_Expr.E (Argo_Expr.Eq, [e1, e2])) =
      HOLogic.mk_eq (term_of cx e1, term_of cx e2)
  | term_of cx (Argo_Expr.E (Argo_Expr.App, [e1, e2])) =
      term_of cx e1 $ term_of cx e2
  | term_of (_, cons) (Argo_Expr.E (Argo_Expr.Con (c as (n, _)), _)) =
      (case Contab.lookup cons c of
        SOME t => t
      | NONE => error ("Unexpected expression named " ^ quote n))
  | term_of (cx as (ctxt, _)) e =
      (case ext_term_of ctxt (term_of cx) e of
        SOME t => t
      | NONE => raise Fail "bad expression")

fun as_prop ct = Thm.apply \<^cterm>\<open>HOL.Trueprop\<close> ct

fun cterm_of ctxt cons e = Thm.cterm_of ctxt (term_of (ctxt, cons) e)
fun cprop_of ctxt cons e = as_prop (cterm_of ctxt cons e)


(* generic proof tools *)

fun discharge thm rule = thm INCR_COMP rule
fun discharge2 thm1 thm2 rule = discharge thm2 (discharge thm1 rule)
fun discharges thm rules = [thm] RL rules

fun under_assumption f ct =
  let val cprop = as_prop ct
  in Thm.implies_intr cprop (f (Thm.assume cprop)) end

fun instantiate cv ct = Thm.instantiate ([], [(Term.dest_Var (Thm.term_of cv), ct)])


(* proof replay for tautologies *)

fun prove_taut ctxt ns t = Goal.prove ctxt ns [] (HOLogic.mk_Trueprop t)
  (fn {context, ...} => HEADGOAL (Classical.fast_tac context))

fun with_frees ctxt n mk =
  let
    val ns = map (fn i => "P" ^ string_of_int i) (0 upto (n - 1))
    val ts = map (Free o rpair \<^typ>\<open>bool\<close>) ns
    val t = mk_nary HOLogic.mk_disj (mk ts)
  in prove_taut ctxt ns t end

fun taut_and1_term ts = mk_nary HOLogic.mk_conj ts :: map HOLogic.mk_not ts
fun taut_and2_term i ts = [HOLogic.mk_not (mk_nary HOLogic.mk_conj ts), nth ts i]
fun taut_or1_term i ts = [mk_nary HOLogic.mk_disj ts, HOLogic.mk_not (nth ts i)]
fun taut_or2_term ts = HOLogic.mk_not (mk_nary HOLogic.mk_disj ts) :: ts

val iff_1_taut = @{lemma "P = Q \<or> P \<or> Q" by fast}
val iff_2_taut = @{lemma "P = Q \<or> (\<not>P) \<or> (\<not>Q)" by fast}
val iff_3_taut = @{lemma "\<not>(P = Q) \<or> (\<not>P) \<or> Q" by fast}
val iff_4_taut = @{lemma "\<not>(P = Q) \<or> P \<or> (\<not>Q)" by fast}
val ite_then_taut = @{lemma "\<not>P \<or> (if P then t else u) = t" by auto}
val ite_else_taut = @{lemma "P \<or> (if P then t else u) = u" by auto}

fun taut_rule_of ctxt (Argo_Proof.Taut_And_1 n) = with_frees ctxt n taut_and1_term
  | taut_rule_of ctxt (Argo_Proof.Taut_And_2 (i, n)) = with_frees ctxt n (taut_and2_term i)
  | taut_rule_of ctxt (Argo_Proof.Taut_Or_1 (i, n)) = with_frees ctxt n (taut_or1_term i)
  | taut_rule_of ctxt (Argo_Proof.Taut_Or_2 n) = with_frees ctxt n taut_or2_term
  | taut_rule_of _ Argo_Proof.Taut_Iff_1 = iff_1_taut
  | taut_rule_of _ Argo_Proof.Taut_Iff_2 = iff_2_taut
  | taut_rule_of _ Argo_Proof.Taut_Iff_3 = iff_3_taut
  | taut_rule_of _ Argo_Proof.Taut_Iff_4 = iff_4_taut
  | taut_rule_of _ Argo_Proof.Taut_Ite_Then = ite_then_taut
  | taut_rule_of _ Argo_Proof.Taut_Ite_Else = ite_else_taut

fun replay_taut ctxt k ct =
  let val rule = taut_rule_of ctxt k
  in Thm.instantiate (Thm.match (Thm.cprop_of rule, ct)) rule end


(* proof replay for conjunct extraction *)

fun replay_conjunct 0 1 thm = thm
  | replay_conjunct 0 _ thm = discharge thm @{thm conjunct1}
  | replay_conjunct 1 2 thm = discharge thm @{thm conjunct2}
  | replay_conjunct i n thm = replay_conjunct (i - 1) (n - 1) (discharge thm @{thm conjunct2})


(* proof replay for rewrite steps *)

fun mk_rewr thm = thm RS @{thm eq_reflection}

fun not_nary_conv rule i ct =
  if i > 1 then (Conv.rewr_conv rule then_conv Conv.arg_conv (not_nary_conv rule (i - 1))) ct
  else Conv.all_conv ct

val flatten_and_thm = @{lemma "(P1 \<and> P2) \<and> P3 \<equiv> P1 \<and> P2 \<and> P3" by simp}
val flatten_or_thm = @{lemma "(P1 \<or> P2) \<or> P3 \<equiv> P1 \<or> P2 \<or> P3" by simp}

fun flatten_conv cv rule ct = (
  Conv.try_conv (Conv.arg_conv cv) then_conv
  Conv.try_conv (Conv.rewr_conv rule then_conv cv)) ct

fun flat_conj_conv ct =
  (case Thm.term_of ct of
    \<^const>\<open>HOL.conj\<close> $ _ $ _ => flatten_conv flat_conj_conv flatten_and_thm ct
  | _ => Conv.all_conv ct)

fun flat_disj_conv ct =
  (case Thm.term_of ct of
    \<^const>\<open>HOL.disj\<close> $ _ $ _ => flatten_conv flat_disj_conv flatten_or_thm ct
  | _ => Conv.all_conv ct)

fun explode rule1 rule2 thm =
  explode rule1 rule2 (thm RS rule1) @ explode rule1 rule2 (thm RS rule2) handle THM _ => [thm]
val explode_conj = explode @{thm conjunct1} @{thm conjunct2}
val explode_ndis = explode @{lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>P" by auto} @{lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>Q" by auto}

fun pick_false i thms = nth thms i

fun pick_dual rule (i1, i2) thms =
  rule OF [nth thms i1, nth thms i2] handle THM _ => rule OF [nth thms i2, nth thms i1]
val pick_dual_conj = pick_dual @{lemma "\<not>P \<Longrightarrow> P \<Longrightarrow> False" by auto}
val pick_dual_ndis = pick_dual @{lemma "\<not>P \<Longrightarrow> P \<Longrightarrow> \<not>True" by auto}

fun join thm0 rule is thms =
  let
    val l = length thms
    val thms' = fold (fn i => cons (if 0 <= i andalso i < l then nth thms i else thm0)) is []
  in fold (fn thm => fn thm' => discharge2 thm thm' rule) (tl thms') (hd thms') end

val join_conj = join @{lemma "True" by auto} @{lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q" by auto}
val join_ndis = join @{lemma "\<not>False" by auto} @{lemma "\<not>P \<Longrightarrow> \<not>Q \<Longrightarrow> \<not>(P \<or> Q)" by auto}

val false_thm = @{lemma "False \<Longrightarrow> P" by auto}
val ntrue_thm = @{lemma "\<not>True \<Longrightarrow> P" by auto}
val iff_conj_thm = @{lemma "(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> P = Q" by auto}
val iff_ndis_thm = @{lemma "(\<not>P \<Longrightarrow> \<not>Q) \<Longrightarrow> (\<not>Q \<Longrightarrow> \<not>P) \<Longrightarrow> P = Q" by auto}

fun iff_intro rule lf rf ct =
  let
    val lhs = under_assumption lf ct
    val rhs = rf (Thm.dest_arg (snd (Thm.dest_implies (Thm.cprop_of lhs))))
  in mk_rewr (discharge2 lhs rhs rule) end

fun with_conj f g ct = iff_intro iff_conj_thm (f o explode_conj) g ct
fun with_ndis f g ct = iff_intro iff_ndis_thm (f o explode_ndis) g (Thm.apply \<^cterm>\<open>HOL.Not\<close> ct)

fun swap_indices n iss = map (fn i => find_index (fn is => member (op =) is i) iss) (0 upto (n - 1))
fun sort_nary w f g (n, iss) = w (f (map hd iss)) (under_assumption (f (swap_indices n iss) o g))
val sort_conj = sort_nary with_conj join_conj explode_conj
val sort_ndis = sort_nary with_ndis join_ndis explode_ndis 

val not_true_thm = mk_rewr @{lemma "(\<not>True) = False" by auto}
val not_false_thm = mk_rewr @{lemma "(\<not>False) = True" by auto}
val not_not_thm = mk_rewr @{lemma "(\<not>\<not>P) = P" by auto}
val not_and_thm = mk_rewr @{lemma "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)" by auto}
val not_or_thm = mk_rewr @{lemma "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)" by auto}
val not_iff_thms = map mk_rewr
  @{lemma "(\<not>((\<not>P) = Q)) = (P = Q)" "(\<not>(P = (\<not>Q))) = (P = Q)" "(\<not>(P = Q)) = ((\<not>P) = Q)" by auto}
val iff_true_thms = map mk_rewr @{lemma "(True = P) = P" "(P = True) = P" by auto}
val iff_false_thms = map mk_rewr @{lemma "(False = P) = (\<not>P)" "(P = False) = (\<not>P)" by auto}
val iff_not_not_thm = mk_rewr @{lemma "((\<not>P) = (\<not>Q)) = (P = Q)" by auto}
val iff_refl_thm = mk_rewr @{lemma "(P = P) = True" by auto}
val iff_symm_thm = mk_rewr @{lemma "(P = Q) = (Q = P)" by auto}
val iff_dual_thms = map mk_rewr @{lemma "(P = (\<not>P)) = False" "((\<not>P) = P) = False" by auto}
val imp_thm = mk_rewr @{lemma "(P \<longrightarrow> Q) = (\<not>P \<or> Q)" by auto}
val ite_prop_thm = mk_rewr @{lemma "(If P Q R) = ((\<not>P \<or> Q) \<and> (P \<or> R) \<and> (Q \<or> R))" by auto}
val ite_true_thm = mk_rewr @{lemma "(If True t u) = t" by auto}
val ite_false_thm = mk_rewr @{lemma "(If False t u) = u" by auto}
val ite_eq_thm = mk_rewr @{lemma "(If P t t) = t" by auto}
val eq_refl_thm = mk_rewr @{lemma "(t = t) = True" by auto}
val eq_symm_thm = mk_rewr @{lemma "(t1 = t2) = (t2 = t1)" by auto}

fun replay_rewr _ Argo_Proof.Rewr_Not_True = Conv.rewr_conv not_true_thm
  | replay_rewr _ Argo_Proof.Rewr_Not_False = Conv.rewr_conv not_false_thm
  | replay_rewr _ Argo_Proof.Rewr_Not_Not = Conv.rewr_conv not_not_thm
  | replay_rewr _ (Argo_Proof.Rewr_Not_And i) = not_nary_conv not_and_thm i
  | replay_rewr _ (Argo_Proof.Rewr_Not_Or i) = not_nary_conv not_or_thm i
  | replay_rewr _ Argo_Proof.Rewr_Not_Iff = Conv.rewrs_conv not_iff_thms
  | replay_rewr _ (Argo_Proof.Rewr_And_False i) = with_conj (pick_false i) (K false_thm)
  | replay_rewr _ (Argo_Proof.Rewr_And_Dual ip) = with_conj (pick_dual_conj ip) (K false_thm)
  | replay_rewr _ (Argo_Proof.Rewr_And_Sort is) = flat_conj_conv then_conv sort_conj is
  | replay_rewr _ (Argo_Proof.Rewr_Or_True i) = with_ndis (pick_false i) (K ntrue_thm)
  | replay_rewr _ (Argo_Proof.Rewr_Or_Dual ip) = with_ndis (pick_dual_ndis ip) (K ntrue_thm)
  | replay_rewr _ (Argo_Proof.Rewr_Or_Sort is) = flat_disj_conv then_conv sort_ndis is
  | replay_rewr _ Argo_Proof.Rewr_Iff_True = Conv.rewrs_conv iff_true_thms
  | replay_rewr _ Argo_Proof.Rewr_Iff_False = Conv.rewrs_conv iff_false_thms
  | replay_rewr _ Argo_Proof.Rewr_Iff_Not_Not = Conv.rewr_conv iff_not_not_thm
  | replay_rewr _ Argo_Proof.Rewr_Iff_Refl = Conv.rewr_conv iff_refl_thm
  | replay_rewr _ Argo_Proof.Rewr_Iff_Symm = Conv.rewr_conv iff_symm_thm
  | replay_rewr _ Argo_Proof.Rewr_Iff_Dual  = Conv.rewrs_conv iff_dual_thms
  | replay_rewr _ Argo_Proof.Rewr_Imp = Conv.rewr_conv imp_thm
  | replay_rewr _ Argo_Proof.Rewr_Ite_Prop = Conv.rewr_conv ite_prop_thm
  | replay_rewr _ Argo_Proof.Rewr_Ite_True = Conv.rewr_conv ite_true_thm
  | replay_rewr _ Argo_Proof.Rewr_Ite_False = Conv.rewr_conv ite_false_thm
  | replay_rewr _ Argo_Proof.Rewr_Ite_Eq = Conv.rewr_conv ite_eq_thm
  | replay_rewr _ Argo_Proof.Rewr_Eq_Refl = Conv.rewr_conv eq_refl_thm
  | replay_rewr _ Argo_Proof.Rewr_Eq_Symm = Conv.rewr_conv eq_symm_thm
  | replay_rewr ctxt r = ext_replay_rewr ctxt r

fun binop_conv cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2

fun replay_conv _ Argo_Proof.Keep_Conv ct = Conv.all_conv ct
  | replay_conv ctxt (Argo_Proof.Then_Conv (c1, c2)) ct = 
      (replay_conv ctxt c1 then_conv replay_conv ctxt c2) ct
  | replay_conv ctxt (Argo_Proof.Args_Conv (Argo_Expr.App, [c1, c2])) ct =
      Conv.combination_conv (replay_conv ctxt c1) (replay_conv ctxt c2) ct
  | replay_conv ctxt (Argo_Proof.Args_Conv (_, cs)) ct = replay_args_conv ctxt cs ct
  | replay_conv ctxt (Argo_Proof.Rewr_Conv r) ct = replay_rewr ctxt r ct

and replay_args_conv _ [] ct = Conv.all_conv ct
  | replay_args_conv ctxt [c] ct = Conv.arg_conv (replay_conv ctxt c) ct
  | replay_args_conv ctxt [c1, c2] ct = binop_conv (replay_conv ctxt c1) (replay_conv ctxt c2) ct
  | replay_args_conv ctxt (c :: cs) ct =
      (case Term.head_of (Thm.term_of ct) of
        Const (\<^const_name>\<open>HOL.If\<close>, _) =>
          let val (cs', c') = split_last cs
          in Conv.combination_conv (replay_args_conv ctxt (c :: cs')) (replay_conv ctxt c') ct end
      | _ => binop_conv (replay_conv ctxt c) (replay_args_conv ctxt cs) ct)

fun replay_rewrite ctxt c thm = Conv.fconv_rule (HOLogic.Trueprop_conv (replay_conv ctxt c)) thm


(* proof replay for clauses *)

val prep_clause_rule = @{lemma "P \<Longrightarrow> \<not>P \<Longrightarrow> False" by fast}
val extract_lit_rule = @{lemma "(\<not>(P \<or> Q) \<Longrightarrow> False) \<Longrightarrow> \<not>P \<Longrightarrow> \<not>Q \<Longrightarrow> False" by fast}

fun add_lit i thm lits =
  let val ct = Thm.cprem_of thm 1
  in (Thm.implies_elim thm (Thm.assume ct), (i, ct) :: lits) end

fun extract_lits [] _ = error "Bad clause"
  | extract_lits [i] (thm, lits) = add_lit i thm lits
  | extract_lits (i :: is) (thm, lits) =
      extract_lits is (add_lit i (discharge thm extract_lit_rule) lits)

fun lit_ord ((l1, _), (l2, _)) = int_ord (abs l1, abs l2)

fun replay_with_lits [] thm lits = (thm, lits)
  | replay_with_lits is thm lits =
      extract_lits is (discharge thm prep_clause_rule, lits)
      ||> Ord_List.make lit_ord

fun replay_clause is thm = replay_with_lits is thm []


(* proof replay for unit resolution *)

val unit_rule = @{lemma "(P \<Longrightarrow> False) \<Longrightarrow> (\<not>P \<Longrightarrow> False) \<Longrightarrow> False" by fast}
val unit_rule_var = Thm.dest_arg (Thm.dest_arg1 (Thm.cprem_of unit_rule 1))
val bogus_ct = \<^cterm>\<open>HOL.True\<close>

fun replay_unit_res lit (pthm, plits) (nthm, nlits) =
  let
    val plit = the (AList.lookup (op =) plits lit)
    val nlit = the (AList.lookup (op =) nlits (~lit))
    val prune = Ord_List.remove lit_ord (lit, bogus_ct)
  in
    unit_rule
    |> instantiate unit_rule_var (Thm.dest_arg plit)
    |> Thm.elim_implies (Thm.implies_intr plit pthm)
    |> Thm.elim_implies (Thm.implies_intr nlit nthm)
    |> rpair (Ord_List.union lit_ord (prune nlits) (prune plits))
  end


(* proof replay for hypothesis *)

val dneg_rule = @{lemma "\<not>\<not>P \<Longrightarrow> P" by auto}

fun replay_hyp i ct =
  if i < 0 then (Thm.assume ct, [(~i, ct)])
  else
    let val cu = as_prop (Thm.apply \<^cterm>\<open>HOL.Not\<close> (Thm.apply \<^cterm>\<open>HOL.Not\<close> (Thm.dest_arg ct)))
    in (discharge (Thm.assume cu) dneg_rule, [(~i, cu)]) end


(* proof replay for lemma *)

fun replay_lemma is (thm, lits) = replay_with_lits is thm lits


(* proof replay for reflexivity *)

val refl_rule = @{thm refl}
val refl_rule_var = Thm.dest_arg1 (Thm.dest_arg (Thm.cprop_of refl_rule))

fun replay_refl ct = Thm.instantiate (Thm.match (refl_rule_var, ct)) refl_rule


(* proof replay for symmetry *)

val symm_rules = @{lemma "a = b ==> b = a" "\<not>(a = b) \<Longrightarrow> \<not>(b = a)" by simp_all}

fun replay_symm thm = hd (discharges thm symm_rules)


(* proof replay for transitivity *)

val trans_rules = @{lemma
  "\<not>(a = b) \<Longrightarrow> b = c \<Longrightarrow> \<not>(a = c)"
  "a = b \<Longrightarrow> \<not>(b = c) \<Longrightarrow> \<not>(a = c)"
  "a = b \<Longrightarrow> b = c ==> a = c"
  by simp_all}

fun replay_trans thm1 thm2 = hd (discharges thm2 (discharges thm1 trans_rules))


(* proof replay for congruence *)

fun replay_cong thm1 thm2 = discharge thm2 (discharge thm1 @{thm cong})


(* proof replay for substitution *)

val subst_rule1 = @{lemma "\<not>(p a) \<Longrightarrow> p = q \<Longrightarrow> a = b \<Longrightarrow> \<not>(q b)" by simp}
val subst_rule2 = @{lemma "p a \<Longrightarrow> p = q \<Longrightarrow> a = b \<Longrightarrow> q b" by simp}

fun replay_subst thm1 thm2 thm3 =
  subst_rule1 OF [thm1, thm2, thm3] handle THM _ => subst_rule2 OF [thm1, thm2, thm3]


(* proof replay *)

structure Thm_Cache = Table(type key = Argo_Proof.proof_id val ord = Argo_Proof.proof_id_ord)

val unclausify_rule1 = @{lemma "(\<not>P \<Longrightarrow> False) \<Longrightarrow> P" by auto}
val unclausify_rule2 = @{lemma "(P \<Longrightarrow> False) \<Longrightarrow> \<not>P" by auto}

fun unclausify (thm, lits) ls =
  (case (Thm.prop_of thm, lits) of
    (\<^const>\<open>HOL.Trueprop\<close> $ \<^const>\<open>HOL.False\<close>, [(_, ct)]) =>
      let val thm = Thm.implies_intr ct thm
      in (discharge thm unclausify_rule1 handle THM _ => discharge thm unclausify_rule2, ls) end
  | _ => (thm, Ord_List.union lit_ord lits ls))

fun with_thms f tps = fold_map unclausify tps [] |>> f

fun bad_premises () = raise Fail "bad number of premises"
fun with_thms1 f = with_thms (fn [thm] => f thm | _ => bad_premises ())
fun with_thms2 f = with_thms (fn [thm1, thm2] => f thm1 thm2 | _ => bad_premises ())
fun with_thms3 f = with_thms (fn [thm1, thm2, thm3] => f thm1 thm2 thm3 | _ => bad_premises ())

fun replay_rule (ctxt, cons, facts) prems rule =
  (case rule of
    Argo_Proof.Axiom i => (nth facts i, [])
  | Argo_Proof.Taut (k, concl) => (replay_taut ctxt k (cprop_of ctxt cons concl), [])
  | Argo_Proof.Conjunct (i, n) => with_thms1 (replay_conjunct i n) prems
  | Argo_Proof.Rewrite c => with_thms1 (replay_rewrite ctxt c) prems
  | Argo_Proof.Clause is => replay_clause is (fst (hd prems))
  | Argo_Proof.Unit_Res i => replay_unit_res i (hd prems) (hd (tl prems))
  | Argo_Proof.Hyp (i, concl) => replay_hyp i (cprop_of ctxt cons concl)
  | Argo_Proof.Lemma is => replay_lemma is (hd prems)
  | Argo_Proof.Refl concl => (replay_refl (cterm_of ctxt cons concl), [])
  | Argo_Proof.Symm => with_thms1 replay_symm prems
  | Argo_Proof.Trans => with_thms2 replay_trans prems
  | Argo_Proof.Cong => with_thms2 replay_cong prems
  | Argo_Proof.Subst => with_thms3 replay_subst prems
  | _ => with_thms (ext_replay (cprop_of ctxt cons) ctxt rule) prems)

fun with_cache f proof thm_cache =
  (case Thm_Cache.lookup thm_cache (Argo_Proof.id_of proof) of
    SOME thm => (thm, thm_cache)
  | NONE =>
      let val (thm, thm_cache') = f proof thm_cache
      in (thm, Thm_Cache.update (Argo_Proof.id_of proof, thm) thm_cache') end)

fun trace_step ctxt proof_id rule proofs = with_full_tracing ctxt (fn ctxt' =>
  let
    val id = Argo_Proof.string_of_proof_id proof_id
    val ids = map (Argo_Proof.string_of_proof_id o Argo_Proof.id_of) proofs
    val rule_string = Argo_Proof.string_of_rule rule
  in full_tracing ctxt' ("  " ^ id ^ " <- " ^ space_implode " " ids ^ " . " ^ rule_string) end)

fun replay_bottom_up (env as (ctxt, _, _)) proof thm_cache =
  let
    val (proof_id, rule, proofs) = Argo_Proof.dest proof
    val (prems, thm_cache) = fold_map (with_cache (replay_bottom_up env)) proofs thm_cache
    val _ = trace_step ctxt proof_id rule proofs
  in (replay_rule env prems rule, thm_cache) end

fun replay_proof env proof = with_cache (replay_bottom_up env) proof Thm_Cache.empty

fun replay ctxt terms facts proof =
  let
    val env = (ctxt, Termtab.fold (Contab.update o swap) terms Contab.empty, facts)
    val _ = tracing ctxt "replaying the proof"
    val ({elapsed=t, ...}, ((thm, _), _)) = Timing.timing (replay_proof env) proof
    val _ = tracing ctxt ("replayed the proof in " ^ string_of_int (Time.toMilliseconds t) ^ " ms")
  in thm end


(* normalizing goals *)

fun instantiate_elim_rule thm =
  let val ct = Drule.strip_imp_concl (Thm.cprop_of thm)
  in
    (case Thm.term_of ct of
      \<^const>\<open>HOL.Trueprop\<close> $ Var (_, \<^typ>\<open>HOL.bool\<close>) =>
        instantiate (Thm.dest_arg ct) \<^cterm>\<open>HOL.False\<close> thm
    | Var _ => instantiate ct \<^cprop>\<open>HOL.False\<close> thm
    | _ => thm)
  end

fun atomize_conv ctxt ct =
  (case Thm.term_of ct of
    \<^const>\<open>HOL.Trueprop\<close> $ _ => Conv.all_conv
  | \<^const>\<open>Pure.imp\<close> $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_imp}
  | Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_eq}
  | Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
      Conv.binder_conv (atomize_conv o snd) ctxt then_conv
      Conv.rewr_conv @{thm atomize_all}
  | _ => Conv.all_conv) ct

fun normalize ctxt thm =
  thm
  |> instantiate_elim_rule
  |> Conv.fconv_rule (Thm.beta_conversion true then_conv Thm.eta_conversion)
  |> Thm.forall_intr_vars
  |> Conv.fconv_rule (atomize_conv ctxt)


(* prover, tactic and method *)

datatype result = Satisfiable of term -> bool option | Unsatisfiable

fun check props ctxt =
  (case solve props ctxt of
    (Proof _, ctxt') => (Unsatisfiable, ctxt')
  | (Model model, ctxt') => (Satisfiable model, ctxt'))

fun prove thms ctxt =
  let val thms' = map (normalize ctxt) thms
  in
    (case solve (map Thm.prop_of thms') ctxt of
      (Model _, ctxt') => (NONE, ctxt')
    | (Proof (terms, proof), ctxt') => (SOME (replay ctxt' terms thms' proof), ctxt'))
  end

fun argo_tac ctxt thms =
  CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1
    (Conv.try_conv (Conv.rewr_conv @{thm atomize_eq})))) ctxt)
  THEN' Tactic.resolve_tac ctxt [@{thm ccontr}]
  THEN' Subgoal.FOCUS (fn {context, prems, ...} =>
    (case with_timeout context (prove (thms @ prems)) context of
      (SOME thm, _) => Tactic.resolve_tac context [thm] 1
    | (NONE, _) => Tactical.no_tac)) ctxt

val _ =
  Theory.setup (Method.setup \<^binding>\<open>argo\<close>
    (Scan.optional Attrib.thms [] >>
      (fn thms => fn ctxt => METHOD (fn facts =>
        HEADGOAL (argo_tac ctxt (thms @ facts)))))
    "Applies the Argo prover")

end
