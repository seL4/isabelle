(*  Title:      HOL/Hoare/hoare_tac.ML
    ID:         $Id$
    Author:     Leonor Prensa Nieto & Tobias Nipkow

Derivation of the proof rules and, most importantly, the VCG tactic.
*)

(*** The tactics ***)

(*****************************************************************************)
(** The function Mset makes the theorem                                     **)
(** "?Mset <= {(x1,...,xn). ?P (x1,...,xn)} ==> ?Mset <= {s. ?P s}",        **)
(** where (x1,...,xn) are the variables of the particular program we are    **)
(** working on at the moment of the call                                    **)
(*****************************************************************************)

local open HOLogic in

(** maps (%x1 ... xn. t) to [x1,...,xn] **)
fun abs2list (Const ("split",_) $ (Abs(x,T,t))) = Free (x, T)::abs2list t
  | abs2list (Abs(x,T,t)) = [Free (x, T)]
  | abs2list _ = [];

(** maps {(x1,...,xn). t} to [x1,...,xn] **)
fun mk_vars (Const ("Collect",_) $ T) = abs2list T
  | mk_vars _ = [];

(** abstraction of body over a tuple formed from a list of free variables.
Types are also built **)
fun mk_abstupleC []     body = absfree ("x", unitT, body)
  | mk_abstupleC (v::w) body = let val (n,T) = dest_Free v
                               in if w=[] then absfree (n, T, body)
        else let val z  = mk_abstupleC w body;
                 val T2 = case z of Abs(_,T,_) => T
                        | Const (_, Type (_,[_, Type (_,[T,_])])) $ _ => T;
       in Const ("split", (T --> T2 --> boolT) --> mk_prodT (T,T2) --> boolT)
          $ absfree (n, T, z) end end;

(** maps [x1,...,xn] to (x1,...,xn) and types**)
fun mk_bodyC []      = HOLogic.unit
  | mk_bodyC (x::xs) = if xs=[] then x
               else let val (n, T) = dest_Free x ;
                        val z = mk_bodyC xs;
                        val T2 = case z of Free(_, T) => T
                                         | Const ("Pair", Type ("fun", [_, Type
                                            ("fun", [_, T])])) $ _ $ _ => T;
                 in Const ("Pair", [T, T2] ---> mk_prodT (T, T2)) $ x $ z end;

(** maps a subgoal of the form:
        VARS x1 ... xn {._.} _ {._.} or to [x1,...,xn]**)
fun get_vars c =
  let
    val d = Logic.strip_assums_concl c;
    val Const _ $ pre $ _ $ _ = dest_Trueprop d;
  in mk_vars pre end;

fun mk_CollectC trm =
  let val T as Type ("fun",[t,_]) = fastype_of trm
  in Collect_const t $ trm end;

fun inclt ty = Const (@{const_name HOL.less_eq}, [ty,ty] ---> boolT);


fun Mset ctxt prop =
  let
    val [(Mset, _), (P, _)] = Variable.variant_frees ctxt [] [("Mset", ()), ("P", ())];

    val vars = get_vars prop;
    val varsT = fastype_of (mk_bodyC vars);
    val big_Collect = mk_CollectC (mk_abstupleC vars (Free (P, varsT --> boolT) $ mk_bodyC vars));
    val small_Collect = mk_CollectC (Abs ("x", varsT, Free (P, varsT --> boolT) $ Bound 0));

    val MsetT = fastype_of big_Collect;
    fun Mset_incl t = mk_Trueprop (inclt MsetT $ Free (Mset, MsetT) $ t);
    val impl = Logic.mk_implies (Mset_incl big_Collect, Mset_incl small_Collect);
    val th = Goal.prove ctxt [Mset, P] [] impl (fn _ => blast_tac (claset_of ctxt) 1);
 in (vars, th) end;

end;


(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

(**Simp_tacs**)

val before_set2pred_simp_tac =
  (simp_tac (HOL_basic_ss addsimps [Collect_conj_eq RS sym, @{thm Compl_Collect}]));

val split_simp_tac = (simp_tac (HOL_basic_ss addsimps [split_conv]));

(*****************************************************************************)
(** set2pred_tac transforms sets inclusion into predicates implication,     **)
(** maintaining the original variable names.                                **)
(** Ex. "{x. x=0} <= {x. x <= 1}" -set2pred-> "x=0 --> x <= 1"              **)
(** Subgoals containing intersections (A Int B) or complement sets (-A)     **)
(** are first simplified by "before_set2pred_simp_tac", that returns only   **)
(** subgoals of the form "{x. P x} <= {x. Q x}", which are easily           **)
(** transformed.                                                            **)
(** This transformation may solve very easy subgoals due to a ligth         **)
(** simplification done by (split_all_tac)                                  **)
(*****************************************************************************)

fun set2pred_tac var_names = SUBGOAL (fn (goal, i) =>
  before_set2pred_simp_tac i THEN_MAYBE
  EVERY [
    rtac subsetI i,
    rtac CollectI i,
    dtac CollectD i,
    TRY (split_all_tac i) THEN_MAYBE
     (rename_tac var_names i THEN full_simp_tac (HOL_basic_ss addsimps [split_conv]) i)]);

(*****************************************************************************)
(** BasicSimpTac is called to simplify all verification conditions. It does **)
(** a light simplification by applying "mem_Collect_eq", then it calls      **)
(** MaxSimpTac, which solves subgoals of the form "A <= A",                 **)
(** and transforms any other into predicates, applying then                 **)
(** the tactic chosen by the user, which may solve the subgoal completely.  **)
(*****************************************************************************)

fun MaxSimpTac var_names tac = FIRST'[rtac subset_refl, set2pred_tac var_names THEN_MAYBE' tac];

fun BasicSimpTac var_names tac =
  simp_tac
    (HOL_basic_ss addsimps [mem_Collect_eq, split_conv] addsimprocs [record_simproc])
  THEN_MAYBE' MaxSimpTac var_names tac;


(** hoare_rule_tac **)

fun hoare_rule_tac (vars, Mlem) tac =
  let
    val var_names = map (fst o dest_Free) vars;
    fun wlp_tac i =
      rtac @{thm SeqRule} i THEN rule_tac false (i + 1)
    and rule_tac pre_cond i st = st |> (*abstraction over st prevents looping*)
      ((wlp_tac i THEN rule_tac pre_cond i)
        ORELSE
        (FIRST [
          rtac @{thm SkipRule} i,
          rtac @{thm AbortRule} i,
          EVERY [
            rtac @{thm BasicRule} i,
            rtac Mlem i,
            split_simp_tac i],
          EVERY [
            rtac @{thm CondRule} i,
            rule_tac false (i + 2),
            rule_tac false (i + 1)],
          EVERY [
            rtac @{thm WhileRule} i,
            BasicSimpTac var_names tac (i + 2),
            rule_tac true (i + 1)]]
         THEN (if pre_cond then BasicSimpTac var_names tac i else rtac subset_refl i)));
  in rule_tac end;


(** tac is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                       **)

fun hoare_tac ctxt (tac: int -> tactic) = SUBGOAL (fn (goal, i) =>
  SELECT_GOAL (hoare_rule_tac (Mset ctxt goal) tac true 1) i);

