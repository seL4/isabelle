(*  Title:      HOL/Tools/lin_arith.ML
    Author:     Tjark Weber and Tobias Nipkow, TU Muenchen

HOL setup for linear arithmetic (see Provers/Arith/fast_lin_arith.ML).
*)

signature LIN_ARITH =
sig
  val pre_tac: simpset -> int -> tactic
  val simple_tac: Proof.context -> int -> tactic
  val tac: Proof.context -> int -> tactic
  val simproc: simpset -> term -> thm option
  val add_inj_thms: thm list -> Context.generic -> Context.generic
  val add_lessD: thm -> Context.generic -> Context.generic
  val add_simps: thm list -> Context.generic -> Context.generic
  val add_simprocs: simproc list -> Context.generic -> Context.generic
  val add_inj_const: string * typ -> Context.generic -> Context.generic
  val add_discrete_type: string -> Context.generic -> Context.generic
  val set_number_of: (theory -> typ -> int -> cterm) -> Context.generic -> Context.generic
  val setup: Context.generic -> Context.generic
  val global_setup: theory -> theory
  val split_limit: int Config.T
  val neq_limit: int Config.T
  val verbose: bool Config.T
  val trace: bool Config.T
end;

structure Lin_Arith: LIN_ARITH =
struct

(* Parameters data for general linear arithmetic functor *)

structure LA_Logic: LIN_ARITH_LOGIC =
struct

val ccontr = ccontr;
val conjI = conjI;
val notI = notI;
val sym = sym;
val trueI = TrueI;
val not_lessD = @{thm linorder_not_less} RS iffD1;
val not_leD = @{thm linorder_not_le} RS iffD1;

fun mk_Eq thm = thm RS @{thm Eq_FalseI} handle THM _ => thm RS @{thm Eq_TrueI};

val mk_Trueprop = HOLogic.mk_Trueprop;

fun atomize thm = case Thm.prop_of thm of
    Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.conj}, _) $ _ $ _) =>
    atomize (thm RS conjunct1) @ atomize (thm RS conjunct2)
  | _ => [thm];

fun neg_prop ((TP as Const(@{const_name Trueprop}, _)) $ (Const (@{const_name Not}, _) $ t)) = TP $ t
  | neg_prop ((TP as Const(@{const_name Trueprop}, _)) $ t) = TP $ (HOLogic.Not $t)
  | neg_prop t = raise TERM ("neg_prop", [t]);

fun is_False thm =
  let val _ $ t = Thm.prop_of thm
  in t = @{term False} end;

fun is_nat t = (fastype_of1 t = HOLogic.natT);

fun mk_nat_thm thy t =
  let
    val cn = cterm_of thy (Var (("n", 0), HOLogic.natT))
    and ct = cterm_of thy t
  in Drule.instantiate_normalize ([], [(cn, ct)]) @{thm le0} end;

end;


(* arith context data *)

structure Lin_Arith_Data = Generic_Data
(
  type T = {splits: thm list,
            inj_consts: (string * typ) list,
            discrete: string list};
  val empty = {splits = [], inj_consts = [], discrete = []};
  val extend = I;
  fun merge
   ({splits = splits1, inj_consts = inj_consts1, discrete = discrete1},
    {splits = splits2, inj_consts = inj_consts2, discrete = discrete2}) : T =
   {splits = Thm.merge_thms (splits1, splits2),
    inj_consts = Library.merge (op =) (inj_consts1, inj_consts2),
    discrete = Library.merge (op =) (discrete1, discrete2)};
);

val get_arith_data = Lin_Arith_Data.get o Context.Proof;

fun add_split thm = Lin_Arith_Data.map (fn {splits, inj_consts, discrete} =>
  {splits = update Thm.eq_thm_prop thm splits,
   inj_consts = inj_consts, discrete = discrete});

fun add_discrete_type d = Lin_Arith_Data.map (fn {splits, inj_consts, discrete} =>
  {splits = splits, inj_consts = inj_consts,
   discrete = update (op =) d discrete});

fun add_inj_const c = Lin_Arith_Data.map (fn {splits, inj_consts, discrete} =>
  {splits = splits, inj_consts = update (op =) c inj_consts,
   discrete = discrete});

val split_limit = Attrib.setup_config_int @{binding linarith_split_limit} (K 9);
val neq_limit = Attrib.setup_config_int @{binding linarith_neq_limit} (K 9);
val verbose = Attrib.setup_config_bool @{binding linarith_verbose} (K true);
val trace = Attrib.setup_config_bool @{binding linarith_trace} (K false);


structure LA_Data =
struct

val neq_limit = neq_limit;
val verbose = verbose;
val trace = trace;


(* Decomposition of terms *)

(*internal representation of linear (in-)equations*)
type decomp =
  ((term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat * bool);

fun nT (Type ("fun", [N, _])) = (N = HOLogic.natT)
  | nT _                      = false;

fun add_atom (t : term) (m : Rat.rat) (p : (term * Rat.rat) list, i : Rat.rat) :
             (term * Rat.rat) list * Rat.rat =
  case AList.lookup Pattern.aeconv p t of
      NONE   => ((t, m) :: p, i)
    | SOME n => (AList.update Pattern.aeconv (t, Rat.add n m) p, i);

(* decompose nested multiplications, bracketing them to the right and combining
   all their coefficients

   inj_consts: list of constants to be ignored when encountered
               (e.g. arithmetic type conversions that preserve value)

   m: multiplicity associated with the entire product

   returns either (SOME term, associated multiplicity) or (NONE, constant)
*)
fun demult (inj_consts : (string * typ) list) : term * Rat.rat -> term option * Rat.rat =
let
  fun demult ((mC as Const (@{const_name Groups.times}, _)) $ s $ t, m) =
      (case s of Const (@{const_name Groups.times}, _) $ s1 $ s2 =>
        (* bracketing to the right: '(s1 * s2) * t' becomes 's1 * (s2 * t)' *)
        demult (mC $ s1 $ (mC $ s2 $ t), m)
      | _ =>
        (* product 's * t', where either factor can be 'NONE' *)
        (case demult (s, m) of
          (SOME s', m') =>
            (case demult (t, m') of
              (SOME t', m'') => (SOME (mC $ s' $ t'), m'')
            | (NONE,    m'') => (SOME s', m''))
        | (NONE,    m') => demult (t, m')))
    | demult ((mC as Const (@{const_name Fields.divide}, _)) $ s $ t, m) =
      (* FIXME: Shouldn't we simplify nested quotients, e.g. '(s/t)/u' could
         become 's/(t*u)', and '(s*t)/u' could become 's*(t/u)' ?   Note that
         if we choose to do so here, the simpset used by arith must be able to
         perform the same simplifications. *)
      (* FIXME: Currently we treat the numerator as atomic unless the
         denominator can be reduced to a numeric constant.  It might be better
         to demult the numerator in any case, and invent a new term of the form
         '1 / t' if the numerator can be reduced, but the denominator cannot. *)
      (* FIXME: Currently we even treat the whole fraction as atomic unless the
         denominator can be reduced to a numeric constant.  It might be better
         to use the partially reduced denominator (i.e. 's / (2*t)' could be
         demult'ed to 's / t' with multiplicity .5).   This would require a
         very simple change only below, but it breaks existing proofs. *)
      (* quotient 's / t', where the denominator t can be NONE *)
      (* Note: will raise Rat.DIVZERO iff m' is Rat.zero *)
      (case demult (t, Rat.one) of
        (SOME _, _) => (SOME (mC $ s $ t), m)
      | (NONE,  m') => apsnd (Rat.mult (Rat.inv m')) (demult (s, m)))
    (* terms that evaluate to numeric constants *)
    | demult (Const (@{const_name Groups.uminus}, _) $ t, m) = demult (t, Rat.neg m)
    | demult (Const (@{const_name Groups.zero}, _), m) = (NONE, Rat.zero)
    | demult (Const (@{const_name Groups.one}, _), m) = (NONE, m)
    (*Warning: in rare cases number_of encloses a non-numeral,
      in which case dest_numeral raises TERM; hence all the handles below.
      Same for Suc-terms that turn out not to be numerals -
      although the simplifier should eliminate those anyway ...*)
    | demult (t as Const ("Int.number_class.number_of", _) $ n, m) =
      ((NONE, Rat.mult m (Rat.rat_of_int (HOLogic.dest_numeral n)))
        handle TERM _ => (SOME t, m))
    | demult (t as Const (@{const_name Suc}, _) $ _, m) =
      ((NONE, Rat.mult m (Rat.rat_of_int (HOLogic.dest_nat t)))
        handle TERM _ => (SOME t, m))
    (* injection constants are ignored *)
    | demult (t as Const f $ x, m) =
      if member (op =) inj_consts f then demult (x, m) else (SOME t, m)
    (* everything else is considered atomic *)
    | demult (atom, m) = (SOME atom, m)
in demult end;

fun decomp0 (inj_consts : (string * typ) list) (rel : string, lhs : term, rhs : term) :
            ((term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat) option =
let
  (* Turns a term 'all' and associated multiplicity 'm' into a list 'p' of
     summands and associated multiplicities, plus a constant 'i' (with implicit
     multiplicity 1) *)
  fun poly (Const (@{const_name Groups.plus}, _) $ s $ t,
        m : Rat.rat, pi : (term * Rat.rat) list * Rat.rat) = poly (s, m, poly (t, m, pi))
    | poly (all as Const (@{const_name Groups.minus}, T) $ s $ t, m, pi) =
        if nT T then add_atom all m pi else poly (s, m, poly (t, Rat.neg m, pi))
    | poly (all as Const (@{const_name Groups.uminus}, T) $ t, m, pi) =
        if nT T then add_atom all m pi else poly (t, Rat.neg m, pi)
    | poly (Const (@{const_name Groups.zero}, _), _, pi) =
        pi
    | poly (Const (@{const_name Groups.one}, _), m, (p, i)) =
        (p, Rat.add i m)
    | poly (Const (@{const_name Suc}, _) $ t, m, (p, i)) =
        poly (t, m, (p, Rat.add i m))
    | poly (all as Const (@{const_name Groups.times}, _) $ _ $ _, m, pi as (p, i)) =
        (case demult inj_consts (all, m) of
           (NONE,   m') => (p, Rat.add i m')
         | (SOME u, m') => add_atom u m' pi)
    | poly (all as Const (@{const_name Fields.divide}, _) $ _ $ _, m, pi as (p, i)) =
        (case demult inj_consts (all, m) of
           (NONE,   m') => (p, Rat.add i m')
         | (SOME u, m') => add_atom u m' pi)
    | poly (all as Const ("Int.number_class.number_of", Type(_,[_,T])) $ t, m, pi as (p, i)) =
        (let val k = HOLogic.dest_numeral t
            val k2 = if k < 0 andalso T = HOLogic.natT then 0 else k
        in (p, Rat.add i (Rat.mult m (Rat.rat_of_int k2))) end
        handle TERM _ => add_atom all m pi)
    | poly (all as Const f $ x, m, pi) =
        if member (op =) inj_consts f then poly (x, m, pi) else add_atom all m pi
    | poly (all, m, pi) =
        add_atom all m pi
  val (p, i) = poly (lhs, Rat.one, ([], Rat.zero))
  val (q, j) = poly (rhs, Rat.one, ([], Rat.zero))
in
  case rel of
    @{const_name Orderings.less}    => SOME (p, i, "<", q, j)
  | @{const_name Orderings.less_eq} => SOME (p, i, "<=", q, j)
  | @{const_name HOL.eq}            => SOME (p, i, "=", q, j)
  | _                   => NONE
end handle Rat.DIVZERO => NONE;

fun of_lin_arith_sort thy U =
  Sign.of_sort thy (U, @{sort Rings.linordered_idom});

fun allows_lin_arith thy (discrete : string list) (U as Type (D, [])) : bool * bool =
      if of_lin_arith_sort thy U then (true, member (op =) discrete D)
      else if member (op =) discrete D then (true, true) else (false, false)
  | allows_lin_arith sg discrete U = (of_lin_arith_sort sg U, false);

fun decomp_typecheck (thy, discrete, inj_consts) (T : typ, xxx) : decomp option =
  case T of
    Type ("fun", [U, _]) =>
      (case allows_lin_arith thy discrete U of
        (true, d) =>
          (case decomp0 inj_consts xxx of
            NONE                   => NONE
          | SOME (p, i, rel, q, j) => SOME (p, i, rel, q, j, d))
      | (false, _) =>
          NONE)
  | _ => NONE;

fun negate (SOME (x, i, rel, y, j, d)) = SOME (x, i, "~" ^ rel, y, j, d)
  | negate NONE                        = NONE;

fun decomp_negation data
  ((Const (@{const_name Trueprop}, _)) $ (Const (rel, T) $ lhs $ rhs)) : decomp option =
      decomp_typecheck data (T, (rel, lhs, rhs))
  | decomp_negation data ((Const (@{const_name Trueprop}, _)) $
  (Const (@{const_name Not}, _) $ (Const (rel, T) $ lhs $ rhs))) =
      negate (decomp_typecheck data (T, (rel, lhs, rhs)))
  | decomp_negation data _ =
      NONE;

fun decomp ctxt : term -> decomp option =
  let
    val thy = Proof_Context.theory_of ctxt
    val {discrete, inj_consts, ...} = get_arith_data ctxt
  in decomp_negation (thy, discrete, inj_consts) end;

fun domain_is_nat (_ $ (Const (_, T) $ _ $ _)) = nT T
  | domain_is_nat (_ $ (Const (@{const_name Not}, _) $ (Const (_, T) $ _ $ _))) = nT T
  | domain_is_nat _ = false;


(*---------------------------------------------------------------------------*)
(* the following code performs splitting of certain constants (e.g., min,    *)
(* max) in a linear arithmetic problem; similar to what split_tac later does *)
(* to the proof state                                                        *)
(*---------------------------------------------------------------------------*)

(* checks if splitting with 'thm' is implemented                             *)

fun is_split_thm ctxt thm =
  (case concl_of thm of _ $ (_ $ (_ $ lhs) $ _) =>
    (* Trueprop $ ((op =) $ (?P $ lhs) $ rhs) *)
    (case head_of lhs of
      Const (a, _) =>
        member (op =)
         [@{const_name Orderings.max},
          @{const_name Orderings.min},
          @{const_name Groups.abs},
          @{const_name Groups.minus},
          "Int.nat" (*DYNAMIC BINDING!*),
          "Divides.div_class.mod" (*DYNAMIC BINDING!*),
          "Divides.div_class.div" (*DYNAMIC BINDING!*)] a
    | _ =>
      (warning ("Lin. Arith.: wrong format for split rule " ^ Display.string_of_thm ctxt thm);
        false))
  | _ =>
    (warning ("Lin. Arith.: wrong format for split rule " ^ Display.string_of_thm ctxt thm);
      false));

(* substitute new for occurrences of old in a term, incrementing bound       *)
(* variables as needed when substituting inside an abstraction               *)

fun subst_term ([] : (term * term) list) (t : term) = t
  | subst_term pairs                     t          =
      (case AList.lookup Pattern.aeconv pairs t of
        SOME new =>
          new
      | NONE     =>
          (case t of Abs (a, T, body) =>
            let val pairs' = map (pairself (incr_boundvars 1)) pairs
            in  Abs (a, T, subst_term pairs' body)  end
          | t1 $ t2                   =>
            subst_term pairs t1 $ subst_term pairs t2
          | _ => t));

(* approximates the effect of one application of split_tac (followed by NNF  *)
(* normalization) on the subgoal represented by '(Ts, terms)'; returns a     *)
(* list of new subgoals (each again represented by a typ list for bound      *)
(* variables and a term list for premises), or NONE if split_tac would fail  *)
(* on the subgoal                                                            *)

(* FIXME: currently only the effect of certain split theorems is reproduced  *)
(*        (which is why we need 'is_split_thm').  A more canonical           *)
(*        implementation should analyze the right-hand side of the split     *)
(*        theorem that can be applied, and modify the subgoal accordingly.   *)
(*        Or even better, the splitter should be extended to provide         *)
(*        splitting on terms as well as splitting on theorems (where the     *)
(*        former can have a faster implementation as it does not need to be  *)
(*        proof-producing).                                                  *)

fun split_once_items ctxt (Ts : typ list, terms : term list) :
                     (typ list * term list) list option =
let
  val thy = Proof_Context.theory_of ctxt
  (* takes a list  [t1, ..., tn]  to the term                                *)
  (*   tn' --> ... --> t1' --> False  ,                                      *)
  (* where ti' = HOLogic.dest_Trueprop ti                                    *)
  fun REPEAT_DETERM_etac_rev_mp tms =
    fold (curry HOLogic.mk_imp) (map HOLogic.dest_Trueprop tms)
      @{term False}
  val split_thms  = filter (is_split_thm ctxt) (#splits (get_arith_data ctxt))
  val cmap        = Splitter.cmap_of_split_thms split_thms
  val goal_tm     = REPEAT_DETERM_etac_rev_mp terms
  val splits      = Splitter.split_posns cmap thy Ts goal_tm
  val split_limit = Config.get ctxt split_limit
in
  if length splits > split_limit then (
    tracing ("linarith_split_limit exceeded (current value is " ^
      string_of_int split_limit ^ ")");
    NONE
  ) else case splits of
    [] =>
    (* split_tac would fail: no possible split *)
    NONE
  | (_, _::_, _, _, _) :: _ =>
    (* disallow a split that involves non-locally bound variables (except    *)
    (* when bound by outermost meta-quantifiers)                             *)
    NONE
  | (_, [], _, split_type, split_term) :: _ =>
    (* ignore all but the first possible split                               *)
    (case strip_comb split_term of
    (* ?P (max ?i ?j) = ((?i <= ?j --> ?P ?j) & (~ ?i <= ?j --> ?P ?i)) *)
      (Const (@{const_name Orderings.max}, _), [t1, t2]) =>
      let
        val rev_terms     = rev terms
        val terms1        = map (subst_term [(split_term, t1)]) rev_terms
        val terms2        = map (subst_term [(split_term, t2)]) rev_terms
        val t1_leq_t2     = Const (@{const_name Orderings.less_eq},
                                    split_type --> split_type --> HOLogic.boolT) $ t1 $ t2
        val not_t1_leq_t2 = HOLogic.Not $ t1_leq_t2
        val not_false     = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1      = (HOLogic.mk_Trueprop t1_leq_t2) :: terms2 @ [not_false]
        val subgoal2      = (HOLogic.mk_Trueprop not_t1_leq_t2) :: terms1 @ [not_false]
      in
        SOME [(Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P (min ?i ?j) = ((?i <= ?j --> ?P ?i) & (~ ?i <= ?j --> ?P ?j)) *)
    | (Const (@{const_name Orderings.min}, _), [t1, t2]) =>
      let
        val rev_terms     = rev terms
        val terms1        = map (subst_term [(split_term, t1)]) rev_terms
        val terms2        = map (subst_term [(split_term, t2)]) rev_terms
        val t1_leq_t2     = Const (@{const_name Orderings.less_eq},
                                    split_type --> split_type --> HOLogic.boolT) $ t1 $ t2
        val not_t1_leq_t2 = HOLogic.Not $ t1_leq_t2
        val not_false     = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1      = (HOLogic.mk_Trueprop t1_leq_t2) :: terms1 @ [not_false]
        val subgoal2      = (HOLogic.mk_Trueprop not_t1_leq_t2) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P (abs ?a) = ((0 <= ?a --> ?P ?a) & (?a < 0 --> ?P (- ?a))) *)
    | (Const (@{const_name Groups.abs}, _), [t1]) =>
      let
        val rev_terms   = rev terms
        val terms1      = map (subst_term [(split_term, t1)]) rev_terms
        val terms2      = map (subst_term [(split_term, Const (@{const_name Groups.uminus},
                            split_type --> split_type) $ t1)]) rev_terms
        val zero        = Const (@{const_name Groups.zero}, split_type)
        val zero_leq_t1 = Const (@{const_name Orderings.less_eq},
                            split_type --> split_type --> HOLogic.boolT) $ zero $ t1
        val t1_lt_zero  = Const (@{const_name Orderings.less},
                            split_type --> split_type --> HOLogic.boolT) $ t1 $ zero
        val not_false   = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1    = (HOLogic.mk_Trueprop zero_leq_t1) :: terms1 @ [not_false]
        val subgoal2    = (HOLogic.mk_Trueprop t1_lt_zero) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P (?a - ?b) = ((?a < ?b --> ?P 0) & (ALL d. ?a = ?b + d --> ?P d)) *)
    | (Const (@{const_name Groups.minus}, _), [t1, t2]) =>
      let
        (* "d" in the above theorem becomes a new bound variable after NNF   *)
        (* transformation, therefore some adjustment of indices is necessary *)
        val rev_terms       = rev terms
        val zero            = Const (@{const_name Groups.zero}, split_type)
        val d               = Bound 0
        val terms1          = map (subst_term [(split_term, zero)]) rev_terms
        val terms2          = map (subst_term [(incr_boundvars 1 split_term, d)])
                                (map (incr_boundvars 1) rev_terms)
        val t1'             = incr_boundvars 1 t1
        val t2'             = incr_boundvars 1 t2
        val t1_lt_t2        = Const (@{const_name Orderings.less},
                                split_type --> split_type --> HOLogic.boolT) $ t1 $ t2
        val t1_eq_t2_plus_d = Const (@{const_name HOL.eq}, split_type --> split_type --> HOLogic.boolT) $ t1' $
                                (Const (@{const_name Groups.plus},
                                  split_type --> split_type --> split_type) $ t2' $ d)
        val not_false       = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1        = (HOLogic.mk_Trueprop t1_lt_t2) :: terms1 @ [not_false]
        val subgoal2        = (HOLogic.mk_Trueprop t1_eq_t2_plus_d) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: Ts, subgoal2)]
      end
    (* ?P (nat ?i) = ((ALL n. ?i = of_nat n --> ?P n) & (?i < 0 --> ?P 0)) *)
    | (Const ("Int.nat", _), [t1]) =>
      let
        val rev_terms   = rev terms
        val zero_int    = Const (@{const_name Groups.zero}, HOLogic.intT)
        val zero_nat    = Const (@{const_name Groups.zero}, HOLogic.natT)
        val n           = Bound 0
        val terms1      = map (subst_term [(incr_boundvars 1 split_term, n)])
                            (map (incr_boundvars 1) rev_terms)
        val terms2      = map (subst_term [(split_term, zero_nat)]) rev_terms
        val t1'         = incr_boundvars 1 t1
        val t1_eq_nat_n = Const (@{const_name HOL.eq}, HOLogic.intT --> HOLogic.intT --> HOLogic.boolT) $ t1' $
                            (Const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT) $ n)
        val t1_lt_zero  = Const (@{const_name Orderings.less},
                            HOLogic.intT --> HOLogic.intT --> HOLogic.boolT) $ t1 $ zero_int
        val not_false   = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1    = (HOLogic.mk_Trueprop t1_eq_nat_n) :: terms1 @ [not_false]
        val subgoal2    = (HOLogic.mk_Trueprop t1_lt_zero) :: terms2 @ [not_false]
      in
        SOME [(HOLogic.natT :: Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P ((?n::nat) mod (number_of ?k)) =
         ((number_of ?k = 0 --> ?P ?n) & (~ (number_of ?k = 0) -->
           (ALL i j. j < number_of ?k --> ?n = number_of ?k * i + j --> ?P j))) *)
    | (Const ("Divides.div_class.mod", Type ("fun", [@{typ nat}, _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name Groups.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, t1)]) rev_terms
        val terms2                  = map (subst_term [(incr_boundvars 2 split_term, j)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val t2_neq_zero             = HOLogic.mk_not (Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero)
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const (@{const_name HOL.eq}, split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name Groups.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name Groups.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop
                                        [t2_neq_zero, j_lt_t2, t1_eq_t2_times_i_plus_j])
                                          @ terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: split_type :: Ts, subgoal2)]
      end
    (* ?P ((?n::nat) div (number_of ?k)) =
         ((number_of ?k = 0 --> ?P 0) & (~ (number_of ?k = 0) -->
           (ALL i j. j < number_of ?k --> ?n = number_of ?k * i + j --> ?P i))) *)
    | (Const ("Divides.div_class.div", Type ("fun", [@{typ nat}, _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name Groups.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, zero)]) rev_terms
        val terms2                  = map (subst_term [(incr_boundvars 2 split_term, i)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val t2_neq_zero             = HOLogic.mk_not (Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero)
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const (@{const_name HOL.eq}, split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name Groups.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name Groups.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop
                                        [t2_neq_zero, j_lt_t2, t1_eq_t2_times_i_plus_j])
                                          @ terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: split_type :: Ts, subgoal2)]
      end
    (* ?P ((?n::int) mod (number_of ?k)) =
         ((number_of ?k = 0 --> ?P ?n) &
          (0 < number_of ?k -->
            (ALL i j.
              0 <= j & j < number_of ?k & ?n = number_of ?k * i + j --> ?P j)) &
          (number_of ?k < 0 -->
            (ALL i j.
              number_of ?k < j & j <= 0 & ?n = number_of ?k * i + j --> ?P j))) *)
    | (Const ("Divides.div_class.mod",
        Type ("fun", [Type ("Int.int", []), _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name Groups.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, t1)]) rev_terms
        val terms2_3                = map (subst_term [(incr_boundvars 2 split_term, j)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val zero_lt_t2              = Const (@{const_name Orderings.less},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ t2'
        val t2_lt_zero              = Const (@{const_name Orderings.less},
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero
        val zero_leq_j              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ j
        val j_leq_zero              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ j $ zero
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t2_lt_j                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ t2' $ j
        val t1_eq_t2_times_i_plus_j = Const (@{const_name HOL.eq}, split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name Groups.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name Groups.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop [zero_lt_t2, zero_leq_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_lt_t2, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val subgoal3                = (map HOLogic.mk_Trueprop [t2_lt_zero, t2_lt_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_leq_zero, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val Ts'                     = split_type :: split_type :: Ts
      in
        SOME [(Ts, subgoal1), (Ts', subgoal2), (Ts', subgoal3)]
      end
    (* ?P ((?n::int) div (number_of ?k)) =
         ((number_of ?k = 0 --> ?P 0) &
          (0 < number_of ?k -->
            (ALL i j.
              0 <= j & j < number_of ?k & ?n = number_of ?k * i + j --> ?P i)) &
          (number_of ?k < 0 -->
            (ALL i j.
              number_of ?k < j & j <= 0 & ?n = number_of ?k * i + j --> ?P i))) *)
    | (Const ("Divides.div_class.div",
        Type ("fun", [Type ("Int.int", []), _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name Groups.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, zero)]) rev_terms
        val terms2_3                = map (subst_term [(incr_boundvars 2 split_term, i)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const (@{const_name HOL.eq},
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val zero_lt_t2              = Const (@{const_name Orderings.less},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ t2'
        val t2_lt_zero              = Const (@{const_name Orderings.less},
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero
        val zero_leq_j              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ j
        val j_leq_zero              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ j $ zero
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t2_lt_j                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ t2' $ j
        val t1_eq_t2_times_i_plus_j = Const (@{const_name HOL.eq}, split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name Groups.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name Groups.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ @{term False})
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop [zero_lt_t2, zero_leq_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_lt_t2, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val subgoal3                = (map HOLogic.mk_Trueprop [t2_lt_zero, t2_lt_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_leq_zero, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val Ts'                     = split_type :: split_type :: Ts
      in
        SOME [(Ts, subgoal1), (Ts', subgoal2), (Ts', subgoal3)]
      end
    (* this will only happen if a split theorem can be applied for which no  *)
    (* code exists above -- in which case either the split theorem should be *)
    (* implemented above, or 'is_split_thm' should be modified to filter it  *)
    (* out                                                                   *)
    | (t, ts) => (
      warning ("Lin. Arith.: split rule for " ^ Syntax.string_of_term ctxt t ^
        " (with " ^ string_of_int (length ts) ^
        " argument(s)) not implemented; proof reconstruction is likely to fail");
      NONE
    ))
end;  (* split_once_items *)

(* remove terms that do not satisfy 'p'; change the order of the remaining   *)
(* terms in the same way as filter_prems_tac does                            *)

fun filter_prems_tac_items (p : term -> bool) (terms : term list) : term list =
  let
    fun filter_prems t (left, right) =
      if p t then (left, right @ [t]) else (left @ right, [])
    val (left, right) = fold filter_prems terms ([], [])
  in
    right @ left
  end;

(* return true iff TRY (etac notE) THEN eq_assume_tac would succeed on a     *)
(* subgoal that has 'terms' as premises                                      *)

fun negated_term_occurs_positively (terms : term list) : bool =
  List.exists
    (fn (Trueprop $ (Const (@{const_name Not}, _) $ t)) =>
      member Pattern.aeconv terms (Trueprop $ t)
      | _ => false)
    terms;

fun pre_decomp ctxt (Ts : typ list, terms : term list) : (typ list * term list) list =
  let
    (* repeatedly split (including newly emerging subgoals) until no further   *)
    (* splitting is possible                                                   *)
    fun split_loop ([] : (typ list * term list) list) = ([] : (typ list * term list) list)
      | split_loop (subgoal::subgoals) =
          (case split_once_items ctxt subgoal of
            SOME new_subgoals => split_loop (new_subgoals @ subgoals)
          | NONE => subgoal :: split_loop subgoals)
    fun is_relevant t  = is_some (decomp ctxt t)
    (* filter_prems_tac is_relevant: *)
    val relevant_terms = filter_prems_tac_items is_relevant terms
    (* split_tac, NNF normalization: *)
    val split_goals = split_loop [(Ts, relevant_terms)]
    (* necessary because split_once_tac may normalize terms: *)
    val beta_eta_norm = map (apsnd (map (Envir.eta_contract o Envir.beta_norm)))
      split_goals
    (* TRY (etac notE) THEN eq_assume_tac: *)
    val result = filter_out (negated_term_occurs_positively o snd) beta_eta_norm
  in
    result
  end;

(* takes the i-th subgoal  [| A1; ...; An |] ==> B  to                       *)
(* An --> ... --> A1 --> B,  performs splitting with the given 'split_thms'  *)
(* (resulting in a different subgoal P), takes  P  to  ~P ==> False,         *)
(* performs NNF-normalization of ~P, and eliminates conjunctions,            *)
(* disjunctions and existential quantifiers from the premises, possibly (in  *)
(* the case of disjunctions) resulting in several new subgoals, each of the  *)
(* general form  [| Q1; ...; Qm |] ==> False.  Fails if more than            *)
(* !split_limit splits are possible.                              *)

local
  val nnf_simpset =
    (empty_ss
      |> Simplifier.set_mkeqTrue mk_eq_True
      |> Simplifier.set_mksimps (mksimps mksimps_pairs))
    addsimps [@{thm imp_conv_disj}, @{thm iff_conv_conj_imp}, @{thm de_Morgan_disj},
      @{thm de_Morgan_conj}, not_all, not_ex, not_not]
  fun prem_nnf_tac ss = full_simp_tac (Simplifier.inherit_context ss nnf_simpset)
in

fun split_once_tac ss split_thms =
  let
    val ctxt = Simplifier.the_context ss
    val thy = Proof_Context.theory_of ctxt
    val cond_split_tac = SUBGOAL (fn (subgoal, i) =>
      let
        val Ts = rev (map snd (Logic.strip_params subgoal))
        val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal)
        val cmap = Splitter.cmap_of_split_thms split_thms
        val splits = Splitter.split_posns cmap thy Ts concl
      in
        if null splits orelse length splits > Config.get ctxt split_limit then
          no_tac
        else if null (#2 (hd splits)) then
          split_tac split_thms i
        else
          (* disallow a split that involves non-locally bound variables      *)
          (* (except when bound by outermost meta-quantifiers)               *)
          no_tac
      end)
  in
    EVERY' [
      REPEAT_DETERM o etac rev_mp,
      cond_split_tac,
      rtac ccontr,
      prem_nnf_tac ss,
      TRY o REPEAT_ALL_NEW (DETERM o (eresolve_tac [conjE, exE] ORELSE' etac disjE))
    ]
  end;

end;  (* local *)

(* remove irrelevant premises, then split the i-th subgoal (and all new      *)
(* subgoals) by using 'split_once_tac' repeatedly.  Beta-eta-normalize new   *)
(* subgoals and finally attempt to solve them by finding an immediate        *)
(* contradiction (i.e., a term and its negation) in their premises.          *)

fun pre_tac ss i =
  let
    val ctxt = Simplifier.the_context ss;
    val split_thms = filter (is_split_thm ctxt) (#splits (get_arith_data ctxt))
    fun is_relevant t = is_some (decomp ctxt t)
  in
    DETERM (
      TRY (filter_prems_tac is_relevant i)
        THEN (
          (TRY o REPEAT_ALL_NEW (split_once_tac ss split_thms))
            THEN_ALL_NEW
              (CONVERSION Drule.beta_eta_conversion
                THEN'
              (TRY o (etac notE THEN' eq_assume_tac)))
        ) i
    )
  end;

end;  (* LA_Data *)


val pre_tac = LA_Data.pre_tac;

structure Fast_Arith = Fast_Lin_Arith(structure LA_Logic = LA_Logic and LA_Data = LA_Data);

val add_inj_thms = Fast_Arith.add_inj_thms;
val add_lessD = Fast_Arith.add_lessD;
val add_simps = Fast_Arith.add_simps;
val add_simprocs = Fast_Arith.add_simprocs;
val set_number_of = Fast_Arith.set_number_of;

fun simple_tac ctxt = Fast_Arith.lin_arith_tac ctxt false;
val lin_arith_tac = Fast_Arith.lin_arith_tac;

(* reduce contradictory <= to False.
   Most of the work is done by the cancel tactics. *)

val init_arith_data =
  Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, number_of, ...} =>
   {add_mono_thms = @{thms add_mono_thms_linordered_semiring} @
      @{thms add_mono_thms_linordered_field} @ add_mono_thms,
    mult_mono_thms = @{thm mult_strict_left_mono} :: @{thm mult_left_mono} ::
      @{lemma "a = b ==> c*a = c*b" by (rule arg_cong)} :: mult_mono_thms,
    inj_thms = inj_thms,
    lessD = lessD @ [@{thm "Suc_leI"}],
    neqE = [@{thm linorder_neqE_nat}, @{thm linorder_neqE_linordered_idom}],
    simpset = HOL_basic_ss
      addsimps @{thms ring_distribs}
      addsimps [@{thm if_True}, @{thm if_False}]
      addsimps
       [@{thm add_0_left},
        @{thm add_0_right},
        @{thm "Zero_not_Suc"}, @{thm "Suc_not_Zero"}, @{thm "le_0_eq"}, @{thm "One_nat_def"},
        @{thm "order_less_irrefl"}, @{thm "zero_neq_one"}, @{thm "zero_less_one"},
        @{thm "zero_le_one"}, @{thm "zero_neq_one"} RS not_sym, @{thm "not_one_le_zero"},
        @{thm "not_one_less_zero"}]
      addsimprocs [@{simproc abel_cancel_sum}, @{simproc abel_cancel_relation}]
       (*abel_cancel helps it work in abstract algebraic domains*)
      addsimprocs Nat_Arith.nat_cancel_sums_add
      |> Simplifier.add_cong @{thm if_weak_cong},
    number_of = number_of}) #>
  add_discrete_type @{type_name nat};

fun add_arith_facts ss =
  Simplifier.add_prems (Arith_Data.get_arith_facts (Simplifier.the_context ss)) ss;

val simproc = add_arith_facts #> Fast_Arith.lin_arith_simproc;


(* generic refutation procedure *)

(* parameters:

   test: term -> bool
   tests if a term is at all relevant to the refutation proof;
   if not, then it can be discarded. Can improve performance,
   esp. if disjunctions can be discarded (no case distinction needed!).

   prep_tac: int -> tactic
   A preparation tactic to be applied to the goal once all relevant premises
   have been moved to the conclusion.

   ref_tac: int -> tactic
   the actual refutation tactic. Should be able to deal with goals
   [| A1; ...; An |] ==> False
   where the Ai are atomic, i.e. no top-level &, | or EX
*)

local
  val nnf_simpset =
    (empty_ss
      |> Simplifier.set_mkeqTrue mk_eq_True
      |> Simplifier.set_mksimps (mksimps mksimps_pairs))
    addsimps [@{thm imp_conv_disj}, @{thm iff_conv_conj_imp}, @{thm de_Morgan_disj},
      @{thm de_Morgan_conj}, @{thm not_all}, @{thm not_ex}, @{thm not_not}];
  fun prem_nnf_tac i st =
    full_simp_tac (Simplifier.global_context (Thm.theory_of_thm st) nnf_simpset) i st;
in

fun refute_tac test prep_tac ref_tac =
  let val refute_prems_tac =
        REPEAT_DETERM
              (eresolve_tac [@{thm conjE}, @{thm exE}] 1 ORELSE
               filter_prems_tac test 1 ORELSE
               etac @{thm disjE} 1) THEN
        (DETERM (etac @{thm notE} 1 THEN eq_assume_tac 1) ORELSE
         ref_tac 1);
  in EVERY'[TRY o filter_prems_tac test,
            REPEAT_DETERM o etac @{thm rev_mp}, prep_tac, rtac @{thm ccontr}, prem_nnf_tac,
            SELECT_GOAL (DEPTH_SOLVE refute_prems_tac)]
  end;

end;


(* arith proof method *)

local

fun raw_tac ctxt ex =
  (* FIXME: K true should be replaced by a sensible test (perhaps "is_some o
     decomp sg"? -- but note that the test is applied to terms already before
     they are split/normalized) to speed things up in case there are lots of
     irrelevant terms involved; elimination of min/max can be optimized:
     (max m n + k <= r) = (m+k <= r & n+k <= r)
     (l <= min m n + k) = (l <= m+k & l <= n+k)
  *)
  refute_tac (K true)
    (* Splitting is also done inside simple_tac, but not completely --    *)
    (* split_tac may use split theorems that have not been implemented in *)
    (* simple_tac (cf. pre_decomp and split_once_items above), and        *)
    (* split_limit may trigger.                                           *)
    (* Therefore splitting outside of simple_tac may allow us to prove    *)
    (* some goals that simple_tac alone would fail on.                    *)
    (REPEAT_DETERM o split_tac (#splits (get_arith_data ctxt)))
    (lin_arith_tac ctxt ex);

in

fun gen_tac ex ctxt = FIRST' [simple_tac ctxt,
  Object_Logic.full_atomize_tac THEN' (REPEAT_DETERM o rtac impI) THEN' raw_tac ctxt ex];

val tac = gen_tac true;

end;


(* context setup *)

val setup =
  init_arith_data #>
  Simplifier.map_ss (fn ss => ss
    addSolver (mk_solver "lin_arith" (add_arith_facts #> Fast_Arith.cut_lin_arith_tac)));

val global_setup =
  Attrib.setup @{binding arith_split} (Scan.succeed (Thm.declaration_attribute add_split))
    "declaration of split rules for arithmetic procedure" #>
  Method.setup @{binding linarith}
    (Scan.succeed (fn ctxt =>
      METHOD (fn facts =>
        HEADGOAL (Method.insert_tac (Arith_Data.get_arith_facts ctxt @ facts)
          THEN' tac ctxt)))) "linear arithmetic" #>
  Arith_Data.add_tactic "linear arithmetic" gen_tac;

end;
