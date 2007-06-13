(*  Title:      HOL/arith_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, Stefan Berghofer and Tobias Nipkow

Various arithmetic proof procedures.
*)

(*---------------------------------------------------------------------------*)
(* 1. Cancellation of common terms                                           *)
(*---------------------------------------------------------------------------*)

structure NatArithUtils =
struct

(** abstract syntax of structure nat: 0, Suc, + **)

(* mk_sum, mk_norm_sum *)

val mk_plus = HOLogic.mk_binop @{const_name HOL.plus};

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*normal form of sums: Suc (... (Suc (a + (b + ...))))*)
fun mk_norm_sum ts =
  let val (ones, sums) = List.partition (equal HOLogic.Suc_zero) ts in
    funpow (length ones) HOLogic.mk_Suc (mk_sum sums)
  end;

(* dest_sum *)

val dest_plus = HOLogic.dest_bin @{const_name HOL.plus} HOLogic.natT;

fun dest_sum tm =
  if HOLogic.is_zero tm then []
  else
    (case try HOLogic.dest_Suc tm of
      SOME t => HOLogic.Suc_zero :: dest_sum t
    | NONE =>
        (case try dest_plus tm of
          SOME (t, u) => dest_sum t @ dest_sum u
        | NONE => [tm]));

(** generic proof tools **)

(* prove conversions *)

fun prove_conv expand_tac norm_tac ss tu =  (* FIXME avoid standard *)
  mk_meta_eq (standard (Goal.prove (Simplifier.the_context ss) [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ss]))));


(* rewriting *)

fun simp_all_tac rules =
  let val ss0 = HOL_ss addsimps rules
  in fn ss => ALLGOALS (simp_tac (Simplifier.inherit_context ss ss0)) end;

fun prep_simproc (name, pats, proc) =
  Simplifier.simproc (the_context ()) name pats proc;

end;  (* NatArithUtils *)


signature ARITH_DATA =
sig
  val nat_cancel_sums_add: simproc list
  val nat_cancel_sums: simproc list
end;


structure ArithData: ARITH_DATA =
struct

open NatArithUtils;

(** cancel common summands **)

structure Sum =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac1 = simp_all_tac [@{thm "add_Suc"}, @{thm "add_Suc_right"},
    @{thm "add_0"}, @{thm "add_0_right"}];
  val norm_tac2 = simp_all_tac @{thms add_ac};
  fun norm_tac ss = norm_tac1 ss THEN norm_tac2 ss;
end;

fun gen_uncancel_tac rule ct =
  rtac (instantiate' [] [NONE, SOME ct] (rule RS @{thm subst_equals})) 1;

(* nat eq *)

structure EqCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel"};
end);

(* nat less *)

structure LessCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less};
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel_less"};
end);

(* nat le *)

structure LeCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less_eq};
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel_le"};
end);

(* nat diff *)

structure DiffCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binop @{const_name HOL.minus};
  val dest_bal = HOLogic.dest_bin @{const_name HOL.minus} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "diff_cancel"};
end);

(** prepare nat_cancel simprocs **)

val nat_cancel_sums_add = map prep_simproc
  [("nateq_cancel_sums",
     ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", "m = Suc n"],
     K EqCancelSums.proc),
   ("natless_cancel_sums",
     ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n", "m < Suc n"],
     K LessCancelSums.proc),
   ("natle_cancel_sums",
     ["(l::nat) + m <= n", "(l::nat) <= m + n", "Suc m <= n", "m <= Suc n"],
     K LeCancelSums.proc)];

val nat_cancel_sums = nat_cancel_sums_add @
  [prep_simproc ("natdiff_cancel_sums",
    ["((l::nat) + m) - n", "(l::nat) - (m + n)", "Suc m - n", "m - Suc n"],
    K DiffCancelSums.proc)];

end;  (* ArithData *)

open ArithData;


(*---------------------------------------------------------------------------*)
(* 2. Linear arithmetic                                                      *)
(*---------------------------------------------------------------------------*)

(* Parameters data for general linear arithmetic functor *)

structure LA_Logic: LIN_ARITH_LOGIC =
struct

val ccontr = ccontr;
val conjI = conjI;
val notI = notI;
val sym = sym;
val not_lessD = @{thm linorder_not_less} RS iffD1;
val not_leD = @{thm linorder_not_le} RS iffD1;
val le0 = thm "le0";

fun mk_Eq thm = (thm RS Eq_FalseI) handle THM _ => (thm RS Eq_TrueI);

val mk_Trueprop = HOLogic.mk_Trueprop;

fun atomize thm = case #prop(rep_thm thm) of
    Const("Trueprop",_) $ (Const("op &",_) $ _ $ _) =>
    atomize(thm RS conjunct1) @ atomize(thm RS conjunct2)
  | _ => [thm];

fun neg_prop ((TP as Const("Trueprop",_)) $ (Const("Not",_) $ t)) = TP $ t
  | neg_prop ((TP as Const("Trueprop",_)) $ t) = TP $ (HOLogic.Not $t)
  | neg_prop t = raise TERM ("neg_prop", [t]);

fun is_False thm =
  let val _ $ t = #prop(rep_thm thm)
  in t = Const("False",HOLogic.boolT) end;

fun is_nat(t) = fastype_of1 t = HOLogic.natT;

fun mk_nat_thm sg t =
  let val ct = cterm_of sg t  and cn = cterm_of sg (Var(("n",0),HOLogic.natT))
  in instantiate ([],[(cn,ct)]) le0 end;

end;  (* LA_Logic *)


(* arith theory data *)

datatype arithtactic = ArithTactic of {name: string, tactic: int -> tactic, id: stamp};

fun mk_arith_tactic name tactic = ArithTactic {name = name, tactic = tactic, id = stamp ()};

fun eq_arith_tactic (ArithTactic {id = id1, ...}, ArithTactic {id = id2, ...}) = (id1 = id2);

structure ArithTheoryData = TheoryDataFun
(
  type T = {splits: thm list,
            inj_consts: (string * typ) list,
            discrete: string list,
            tactics: arithtactic list};
  val empty = {splits = [], inj_consts = [], discrete = [], tactics = []};
  val copy = I;
  val extend = I;
  fun merge _ ({splits= splits1, inj_consts= inj_consts1, discrete= discrete1, tactics= tactics1},
             {splits= splits2, inj_consts= inj_consts2, discrete= discrete2, tactics= tactics2}) =
   {splits = Library.merge Thm.eq_thm_prop (splits1, splits2),
    inj_consts = Library.merge (op =) (inj_consts1, inj_consts2),
    discrete = Library.merge (op =) (discrete1, discrete2),
    tactics = Library.merge eq_arith_tactic (tactics1, tactics2)};
);

val arith_split_add = Thm.declaration_attribute (fn thm =>
  Context.mapping (ArithTheoryData.map (fn {splits,inj_consts,discrete,tactics} =>
    {splits= insert Thm.eq_thm_prop thm splits, inj_consts= inj_consts, discrete= discrete, tactics= tactics})) I);

fun arith_discrete d = ArithTheoryData.map (fn {splits,inj_consts,discrete,tactics} =>
  {splits = splits, inj_consts = inj_consts, discrete = insert (op =) d discrete, tactics= tactics});

fun arith_inj_const c = ArithTheoryData.map (fn {splits,inj_consts,discrete,tactics} =>
  {splits = splits, inj_consts = insert (op =) c inj_consts, discrete = discrete, tactics= tactics});

fun arith_tactic_add tac = ArithTheoryData.map (fn {splits,inj_consts,discrete,tactics} =>
  {splits= splits, inj_consts= inj_consts, discrete= discrete, tactics= insert eq_arith_tactic tac tactics});


signature HOL_LIN_ARITH_DATA =
sig
  include LIN_ARITH_DATA
  val fast_arith_split_limit : int ref
end;

structure LA_Data_Ref: HOL_LIN_ARITH_DATA =
struct

(* internal representation of linear (in-)equations *)
type decompT = ((term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat * bool);

(* Decomposition of terms *)

fun nT (Type ("fun", [N, _])) = (N = HOLogic.natT)
  | nT _                      = false;

fun add_atom (t : term) (m : Rat.rat) (p : (term * Rat.rat) list, i : Rat.rat) :
             (term * Rat.rat) list * Rat.rat =
  case AList.lookup (op =) p t of NONE   => ((t, m) :: p, i)
                                | SOME n => (AList.update (op =) (t, Rat.add n m) p, i);

exception Zero;

fun rat_of_term (numt, dent) =
  let
    val num = HOLogic.dest_numeral numt
    val den = HOLogic.dest_numeral dent
  in
    if den = 0 then raise Zero else Rat.rat_of_quotient (num, den)
  end;

(* Warning: in rare cases number_of encloses a non-numeral,
   in which case dest_numeral raises TERM; hence all the handles below.
   Same for Suc-terms that turn out not to be numerals -
   although the simplifier should eliminate those anyway ...
*)
fun number_of_Sucs (Const ("Suc", _) $ n) : int =
      number_of_Sucs n + 1
  | number_of_Sucs t =
      if HOLogic.is_zero t then 0 else raise TERM ("number_of_Sucs", []);

(* decompose nested multiplications, bracketing them to the right and combining
   all their coefficients
*)
fun demult (inj_consts : (string * typ) list) : term * Rat.rat -> term option * Rat.rat =
let
  fun demult ((mC as Const (@{const_name HOL.times}, _)) $ s $ t, m) = (
    (case s of
      Const ("Numeral.number_class.number_of", _) $ n =>
        demult (t, Rat.mult m (Rat.rat_of_int (HOLogic.dest_numeral n)))
    | Const (@{const_name HOL.uminus}, _) $ (Const ("Numeral.number_class.number_of", _) $ n) =>
        demult (t, Rat.mult m (Rat.rat_of_int (~(HOLogic.dest_numeral n))))
    | Const (@{const_name Suc}, _) $ _ =>
        demult (t, Rat.mult m (Rat.rat_of_int (HOLogic.dest_nat s)))
    | Const (@{const_name HOL.times}, _) $ s1 $ s2 =>
        demult (mC $ s1 $ (mC $ s2 $ t), m)
    | Const (@{const_name HOL.divide}, _) $ numt $ (Const ("Numeral.number_class.number_of", _) $ dent) =>
        let
          val den = HOLogic.dest_numeral dent
        in
          if den = 0 then
            raise Zero
          else
            demult (mC $ numt $ t, Rat.mult m (Rat.inv (Rat.rat_of_int den)))
        end
    | _ =>
        atomult (mC, s, t, m)
    ) handle TERM _ => atomult (mC, s, t, m)
  )
    | demult (atom as Const(@{const_name HOL.divide}, _) $ t $ (Const ("Numeral.number_class.number_of", _) $ dent), m) =
      (let
        val den = HOLogic.dest_numeral dent
      in
        if den = 0 then
          raise Zero
        else
          demult (t, Rat.mult m (Rat.inv (Rat.rat_of_int den)))
      end
        handle TERM _ => (SOME atom, m))
    | demult (Const (@{const_name HOL.zero}, _), m) = (NONE, Rat.zero)
    | demult (Const (@{const_name HOL.one}, _), m) = (NONE, m)
    | demult (t as Const ("Numeral.number_class.number_of", _) $ n, m) =
        ((NONE, Rat.mult m (Rat.rat_of_int (HOLogic.dest_numeral n)))
          handle TERM _ => (SOME t, m))
    | demult (Const (@{const_name HOL.uminus}, _) $ t, m) = demult (t, Rat.neg m)
    | demult (t as Const f $ x, m) =
        (if member (op =) inj_consts f then SOME x else SOME t, m)
    | demult (atom, m) = (SOME atom, m)
and
  atomult (mC, atom, t, m) = (
    case demult (t, m) of (NONE, m')    => (SOME atom, m')
                        | (SOME t', m') => (SOME (mC $ atom $ t'), m')
  )
in demult end;

fun decomp0 (inj_consts : (string * typ) list) (rel : string, lhs : term, rhs : term) :
            ((term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat) option =
let
  (* Turn term into list of summand * multiplicity plus a constant *)
  fun poly (Const (@{const_name HOL.plus}, _) $ s $ t, m : Rat.rat, pi : (term * Rat.rat) list * Rat.rat) =
        poly (s, m, poly (t, m, pi))
    | poly (all as Const (@{const_name HOL.minus}, T) $ s $ t, m, pi) =
        if nT T then add_atom all m pi else poly (s, m, poly (t, Rat.neg m, pi))
    | poly (all as Const (@{const_name HOL.uminus}, T) $ t, m, pi) =
        if nT T then add_atom all m pi else poly (t, Rat.neg m, pi)
    | poly (Const (@{const_name HOL.zero}, _), _, pi) =
        pi
    | poly (Const (@{const_name HOL.one}, _), m, (p, i)) =
        (p, Rat.add i m)
    | poly (Const (@{const_name Suc}, _) $ t, m, (p, i)) =
        poly (t, m, (p, Rat.add i m))
    | poly (all as Const (@{const_name HOL.times}, _) $ _ $ _, m, pi as (p, i)) =
        (case demult inj_consts (all, m) of
           (NONE,   m') => (p, Rat.add i m')
         | (SOME u, m') => add_atom u m' pi)
    | poly (all as Const (@{const_name HOL.divide}, _) $ _ $ _, m, pi as (p, i)) =
        (case demult inj_consts (all, m) of
           (NONE,   m') => (p, Rat.add i m')
         | (SOME u, m') => add_atom u m' pi)
    | poly (all as Const ("Numeral.number_class.number_of", Type(_,[_,T])) $ t, m, pi as (p, i)) =
        (let val k = HOLogic.dest_numeral t
            val k2 = if k < 0 andalso T = HOLogic.natT then 0 else k
        in (p, Rat.add i (Rat.mult m (Rat.rat_of_int k2))) end
        handle TERM _ => add_atom all m pi)
    | poly (all as Const f $ x, m, pi) =
        if f mem inj_consts then poly (x, m, pi) else add_atom all m pi
    | poly (all, m, pi) =
        add_atom all m pi
  val (p, i) = poly (lhs, Rat.one, ([], Rat.zero))
  val (q, j) = poly (rhs, Rat.one, ([], Rat.zero))
in
  case rel of
    @{const_name Orderings.less}    => SOME (p, i, "<", q, j)
  | @{const_name Orderings.less_eq} => SOME (p, i, "<=", q, j)
  | "op ="              => SOME (p, i, "=", q, j)
  | _                   => NONE
end handle Zero => NONE;

fun of_lin_arith_sort sg (U : typ) : bool =
  Type.of_sort (Sign.tsig_of sg) (U, ["Ring_and_Field.ordered_idom"])

fun allows_lin_arith sg (discrete : string list) (U as Type (D, [])) : bool * bool =
  if of_lin_arith_sort sg U then
    (true, D mem discrete)
  else (* special cases *)
    if D mem discrete then  (true, true)  else  (false, false)
  | allows_lin_arith sg discrete U =
  (of_lin_arith_sort sg U, false);

fun decomp_typecheck (sg, discrete, inj_consts) (T : typ, xxx) : decompT option =
  case T of
    Type ("fun", [U, _]) =>
      (case allows_lin_arith sg discrete U of
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
  ((Const ("Trueprop", _)) $ (Const (rel, T) $ lhs $ rhs)) : decompT option =
      decomp_typecheck data (T, (rel, lhs, rhs))
  | decomp_negation data ((Const ("Trueprop", _)) $
  (Const ("Not", _) $ (Const (rel, T) $ lhs $ rhs))) =
      negate (decomp_typecheck data (T, (rel, lhs, rhs)))
  | decomp_negation data _ =
      NONE;

fun decomp sg : term -> decompT option =
let
  val {discrete, inj_consts, ...} = ArithTheoryData.get sg
in
  decomp_negation (sg, discrete, inj_consts)
end;

fun domain_is_nat (_ $ (Const (_, T) $ _ $ _))                      = nT T
  | domain_is_nat (_ $ (Const ("Not", _) $ (Const (_, T) $ _ $ _))) = nT T
  | domain_is_nat _                                                 = false;

fun number_of (n, T) = HOLogic.mk_number T n;

(*---------------------------------------------------------------------------*)
(* code that performs certain goal transformations for linear arithmetic     *)
(*---------------------------------------------------------------------------*)

(* A "do nothing" variant of pre_decomp and pre_tac:

fun pre_decomp sg Ts termitems = [termitems];
fun pre_tac i = all_tac;
*)

(*---------------------------------------------------------------------------*)
(* the following code performs splitting of certain constants (e.g. min,     *)
(* max) in a linear arithmetic problem; similar to what split_tac later does *)
(* to the proof state                                                        *)
(*---------------------------------------------------------------------------*)

val fast_arith_split_limit = ref 9;

(* checks if splitting with 'thm' is implemented                             *)

fun is_split_thm (thm : thm) : bool =
  case concl_of thm of _ $ (_ $ (_ $ lhs) $ _) => (
    (* Trueprop $ ((op =) $ (?P $ lhs) $ rhs) *)
    case head_of lhs of
      Const (a, _) => member (op =) [@{const_name Orderings.max},
                                    @{const_name Orderings.min},
                                    @{const_name HOL.abs},
                                    @{const_name HOL.minus},
                                    "IntDef.nat",
                                    "Divides.div_class.mod",
                                    "Divides.div_class.div"] a
    | _            => (warning ("Lin. Arith.: wrong format for split rule " ^
                                 Display.string_of_thm thm);
                       false))
  | _ => (warning ("Lin. Arith.: wrong format for split rule " ^
                   Display.string_of_thm thm);
          false);

(* substitute new for occurrences of old in a term, incrementing bound       *)
(* variables as needed when substituting inside an abstraction               *)

fun subst_term ([] : (term * term) list) (t : term) = t
  | subst_term pairs                     t          =
      (case AList.lookup (op aconv) pairs t of
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

fun split_once_items (sg : theory) (Ts : typ list, terms : term list) :
                     (typ list * term list) list option =
let
  (* takes a list  [t1, ..., tn]  to the term                                *)
  (*   tn' --> ... --> t1' --> False  ,                                      *)
  (* where ti' = HOLogic.dest_Trueprop ti                                    *)
  (* term list -> term *)
  fun REPEAT_DETERM_etac_rev_mp terms' =
    fold (curry HOLogic.mk_imp) (map HOLogic.dest_Trueprop terms') HOLogic.false_const
  val split_thms = filter is_split_thm (#splits (ArithTheoryData.get sg))
  val cmap       = Splitter.cmap_of_split_thms split_thms
  val splits     = Splitter.split_posns cmap sg Ts (REPEAT_DETERM_etac_rev_mp terms)
in
  if length splits > !fast_arith_split_limit then (
    tracing ("fast_arith_split_limit exceeded (current value is " ^
              string_of_int (!fast_arith_split_limit) ^ ")");
    NONE
  ) else (
  case splits of [] =>
    (* split_tac would fail: no possible split *)
    NONE
  | ((_, _, _, split_type, split_term) :: _) => (
    (* ignore all but the first possible split *)
    case strip_comb split_term of
    (* ?P (max ?i ?j) = ((?i <= ?j --> ?P ?j) & (~ ?i <= ?j --> ?P ?i)) *)
      (Const (@{const_name Orderings.max}, _), [t1, t2]) =>
      let
        val rev_terms     = rev terms
        val terms1        = map (subst_term [(split_term, t1)]) rev_terms
        val terms2        = map (subst_term [(split_term, t2)]) rev_terms
        val t1_leq_t2     = Const (@{const_name Orderings.less_eq},
                                    split_type --> split_type --> HOLogic.boolT) $ t1 $ t2
        val not_t1_leq_t2 = HOLogic.Not $ t1_leq_t2
        val not_false     = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
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
        val not_false     = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1      = (HOLogic.mk_Trueprop t1_leq_t2) :: terms1 @ [not_false]
        val subgoal2      = (HOLogic.mk_Trueprop not_t1_leq_t2) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P (abs ?a) = ((0 <= ?a --> ?P ?a) & (?a < 0 --> ?P (- ?a))) *)
    | (Const (@{const_name HOL.abs}, _), [t1]) =>
      let
        val rev_terms   = rev terms
        val terms1      = map (subst_term [(split_term, t1)]) rev_terms
        val terms2      = map (subst_term [(split_term, Const (@{const_name HOL.uminus},
                            split_type --> split_type) $ t1)]) rev_terms
        val zero        = Const (@{const_name HOL.zero}, split_type)
        val zero_leq_t1 = Const (@{const_name Orderings.less_eq},
                            split_type --> split_type --> HOLogic.boolT) $ zero $ t1
        val t1_lt_zero  = Const (@{const_name Orderings.less},
                            split_type --> split_type --> HOLogic.boolT) $ t1 $ zero
        val not_false   = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1    = (HOLogic.mk_Trueprop zero_leq_t1) :: terms1 @ [not_false]
        val subgoal2    = (HOLogic.mk_Trueprop t1_lt_zero) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (Ts, subgoal2)]
      end
    (* ?P (?a - ?b) = ((?a < ?b --> ?P 0) & (ALL d. ?a = ?b + d --> ?P d)) *)
    | (Const (@{const_name HOL.minus}, _), [t1, t2]) =>
      let
        (* "d" in the above theorem becomes a new bound variable after NNF   *)
        (* transformation, therefore some adjustment of indices is necessary *)
        val rev_terms       = rev terms
        val zero            = Const (@{const_name HOL.zero}, split_type)
        val d               = Bound 0
        val terms1          = map (subst_term [(split_term, zero)]) rev_terms
        val terms2          = map (subst_term [(incr_boundvars 1 split_term, d)])
                                (map (incr_boundvars 1) rev_terms)
        val t1'             = incr_boundvars 1 t1
        val t2'             = incr_boundvars 1 t2
        val t1_lt_t2        = Const (@{const_name Orderings.less},
                                split_type --> split_type --> HOLogic.boolT) $ t1 $ t2
        val t1_eq_t2_plus_d = Const ("op =", split_type --> split_type --> HOLogic.boolT) $ t1' $
                                (Const (@{const_name HOL.plus},
                                  split_type --> split_type --> split_type) $ t2' $ d)
        val not_false       = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1        = (HOLogic.mk_Trueprop t1_lt_t2) :: terms1 @ [not_false]
        val subgoal2        = (HOLogic.mk_Trueprop t1_eq_t2_plus_d) :: terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: Ts, subgoal2)]
      end
    (* ?P (nat ?i) = ((ALL n. ?i = int n --> ?P n) & (?i < 0 --> ?P 0)) *)
    | (Const ("IntDef.nat", _), [t1]) =>
      let
        val rev_terms   = rev terms
        val zero_int    = Const (@{const_name HOL.zero}, HOLogic.intT)
        val zero_nat    = Const (@{const_name HOL.zero}, HOLogic.natT)
        val n           = Bound 0
        val terms1      = map (subst_term [(incr_boundvars 1 split_term, n)])
                            (map (incr_boundvars 1) rev_terms)
        val terms2      = map (subst_term [(split_term, zero_nat)]) rev_terms
        val t1'         = incr_boundvars 1 t1
        val t1_eq_int_n = Const ("op =", HOLogic.intT --> HOLogic.intT --> HOLogic.boolT) $ t1' $
                            (Const ("Nat.of_nat", HOLogic.natT --> HOLogic.intT) $ n)
        val t1_lt_zero  = Const (@{const_name Orderings.less},
                            HOLogic.intT --> HOLogic.intT --> HOLogic.boolT) $ t1 $ zero_int
        val not_false   = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1    = (HOLogic.mk_Trueprop t1_eq_int_n) :: terms1 @ [not_false]
        val subgoal2    = (HOLogic.mk_Trueprop t1_lt_zero) :: terms2 @ [not_false]
      in
        SOME [(HOLogic.natT :: Ts, subgoal1), (Ts, subgoal2)]
      end
    (* "?P ((?n::nat) mod (number_of ?k)) =
         ((number_of ?k = 0 --> ?P ?n) & (~ (number_of ?k = 0) -->
           (ALL i j. j < number_of ?k --> ?n = number_of ?k * i + j --> ?P j))) *)
    | (Const ("Divides.div_class.mod", Type ("fun", [Type ("nat", []), _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name HOL.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, t1)]) rev_terms
        val terms2                  = map (subst_term [(incr_boundvars 2 split_term, j)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const ("op =",
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val t2_neq_zero             = HOLogic.mk_not (Const ("op =",
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero)
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const ("op =", split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name HOL.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name HOL.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop
                                        [t2_neq_zero, j_lt_t2, t1_eq_t2_times_i_plus_j])
                                          @ terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: split_type :: Ts, subgoal2)]
      end
    (* "?P ((?n::nat) div (number_of ?k)) =
         ((number_of ?k = 0 --> ?P 0) & (~ (number_of ?k = 0) -->
           (ALL i j. j < number_of ?k --> ?n = number_of ?k * i + j --> ?P i))) *)
    | (Const ("Divides.div_class.div", Type ("fun", [Type ("nat", []), _])), [t1, t2]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name HOL.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, zero)]) rev_terms
        val terms2                  = map (subst_term [(incr_boundvars 2 split_term, i)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val t2'                     = incr_boundvars 2 t2
        val t2_eq_zero              = Const ("op =",
                                        split_type --> split_type --> HOLogic.boolT) $ t2 $ zero
        val t2_neq_zero             = HOLogic.mk_not (Const ("op =",
                                        split_type --> split_type --> HOLogic.boolT) $ t2' $ zero)
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const ("op =", split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name HOL.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name HOL.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1                = (HOLogic.mk_Trueprop t2_eq_zero) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop
                                        [t2_neq_zero, j_lt_t2, t1_eq_t2_times_i_plus_j])
                                          @ terms2 @ [not_false]
      in
        SOME [(Ts, subgoal1), (split_type :: split_type :: Ts, subgoal2)]
      end
    (* "?P ((?n::int) mod (number_of ?k)) =
         ((iszero (number_of ?k) --> ?P ?n) &
          (neg (number_of (uminus ?k)) -->
            (ALL i j. 0 <= j & j < number_of ?k & ?n = number_of ?k * i + j --> ?P j)) &
          (neg (number_of ?k) -->
            (ALL i j. number_of ?k < j & j <= 0 & ?n = number_of ?k * i + j --> ?P j))) *)
    | (Const ("Divides.div_class.mod",
        Type ("fun", [Type ("IntDef.int", []), _])), [t1, t2 as (number_of $ k)]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name HOL.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, t1)]) rev_terms
        val terms2_3                = map (subst_term [(incr_boundvars 2 split_term, j)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val (t2' as (_ $ k'))       = incr_boundvars 2 t2
        val iszero_t2               = Const ("IntDef.iszero", split_type --> HOLogic.boolT) $ t2
        val neg_minus_k             = Const ("IntDef.neg", split_type --> HOLogic.boolT) $
                                        (number_of $
                                          (Const (@{const_name HOL.uminus},
                                            HOLogic.intT --> HOLogic.intT) $ k'))
        val zero_leq_j              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ j
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const ("op =", split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name HOL.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name HOL.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val neg_t2                  = Const ("IntDef.neg", split_type --> HOLogic.boolT) $ t2'
        val t2_lt_j                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ t2' $ j
        val j_leq_zero              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ j $ zero
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1                = (HOLogic.mk_Trueprop iszero_t2) :: terms1 @ [not_false]
        val subgoal2                = (map HOLogic.mk_Trueprop [neg_minus_k, zero_leq_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_lt_t2, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val subgoal3                = (map HOLogic.mk_Trueprop [neg_t2, t2_lt_j])
                                        @ hd terms2_3
                                        :: (if tl terms2_3 = [] then [not_false] else [])
                                        @ (map HOLogic.mk_Trueprop [j_leq_zero, t1_eq_t2_times_i_plus_j])
                                        @ (if tl terms2_3 = [] then [] else tl terms2_3 @ [not_false])
        val Ts'                     = split_type :: split_type :: Ts
      in
        SOME [(Ts, subgoal1), (Ts', subgoal2), (Ts', subgoal3)]
      end
    (* "?P ((?n::int) div (number_of ?k)) =
         ((iszero (number_of ?k) --> ?P 0) &
          (neg (number_of (uminus ?k)) -->
            (ALL i. (EX j. 0 <= j & j < number_of ?k & ?n = number_of ?k * i + j) --> ?P i)) &
          (neg (number_of ?k) -->
            (ALL i. (EX j. number_of ?k < j & j <= 0 & ?n = number_of ?k * i + j) --> ?P i))) *)
    | (Const ("Divides.div_class.div",
        Type ("fun", [Type ("IntDef.int", []), _])), [t1, t2 as (number_of $ k)]) =>
      let
        val rev_terms               = rev terms
        val zero                    = Const (@{const_name HOL.zero}, split_type)
        val i                       = Bound 1
        val j                       = Bound 0
        val terms1                  = map (subst_term [(split_term, zero)]) rev_terms
        val terms2_3                = map (subst_term [(incr_boundvars 2 split_term, i)])
                                        (map (incr_boundvars 2) rev_terms)
        val t1'                     = incr_boundvars 2 t1
        val (t2' as (_ $ k'))       = incr_boundvars 2 t2
        val iszero_t2               = Const ("IntDef.iszero", split_type --> HOLogic.boolT) $ t2
        val neg_minus_k             = Const ("IntDef.neg", split_type --> HOLogic.boolT) $
                                        (number_of $
                                          (Const (@{const_name HOL.uminus},
                                            HOLogic.intT --> HOLogic.intT) $ k'))
        val zero_leq_j              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ zero $ j
        val j_lt_t2                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ j $ t2'
        val t1_eq_t2_times_i_plus_j = Const ("op =",
                                        split_type --> split_type --> HOLogic.boolT) $ t1' $
                                       (Const (@{const_name HOL.plus}, split_type --> split_type --> split_type) $
                                         (Const (@{const_name HOL.times},
                                           split_type --> split_type --> split_type) $ t2' $ i) $ j)
        val neg_t2                  = Const ("IntDef.neg", split_type --> HOLogic.boolT) $ t2'
        val t2_lt_j                 = Const (@{const_name Orderings.less},
                                        split_type --> split_type--> HOLogic.boolT) $ t2' $ j
        val j_leq_zero              = Const (@{const_name Orderings.less_eq},
                                        split_type --> split_type --> HOLogic.boolT) $ j $ zero
        val not_false               = HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.false_const)
        val subgoal1                = (HOLogic.mk_Trueprop iszero_t2) :: terms1 @ [not_false]
        val subgoal2                = (HOLogic.mk_Trueprop neg_minus_k)
                                        :: terms2_3
                                        @ not_false
                                        :: (map HOLogic.mk_Trueprop
                                             [zero_leq_j, j_lt_t2, t1_eq_t2_times_i_plus_j])
        val subgoal3                = (HOLogic.mk_Trueprop neg_t2)
                                        :: terms2_3
                                        @ not_false
                                        :: (map HOLogic.mk_Trueprop
                                             [t2_lt_j, j_leq_zero, t1_eq_t2_times_i_plus_j])
        val Ts'                     = split_type :: split_type :: Ts
      in
        SOME [(Ts, subgoal1), (Ts', subgoal2), (Ts', subgoal3)]
      end
    (* this will only happen if a split theorem can be applied for which no  *)
    (* code exists above -- in which case either the split theorem should be *)
    (* implemented above, or 'is_split_thm' should be modified to filter it  *)
    (* out                                                                   *)
    | (t, ts) => (
      warning ("Lin. Arith.: split rule for " ^ Sign.string_of_term sg t ^
               " (with " ^ Int.toString (length ts) ^
               " argument(s)) not implemented; proof reconstruction is likely to fail");
      NONE
    ))
  )
end;

(* remove terms that do not satisfy 'p'; change the order of the remaining   *)
(* terms in the same way as filter_prems_tac does                            *)

fun filter_prems_tac_items (p : term -> bool) (terms : term list) : term list =
let
  fun filter_prems (t, (left, right)) =
    if  p t  then  (left, right @ [t])  else  (left @ right, [])
  val (left, right) = foldl filter_prems ([], []) terms
in
  right @ left
end;

(* return true iff TRY (etac notE) THEN eq_assume_tac would succeed on a     *)
(* subgoal that has 'terms' as premises                                      *)

fun negated_term_occurs_positively (terms : term list) : bool =
  List.exists
    (fn (Trueprop $ (Const ("Not", _) $ t)) => member (op aconv) terms (Trueprop $ t)
      | _                                   => false)
    terms;

fun pre_decomp sg (Ts : typ list, terms : term list) : (typ list * term list) list =
let
  (* repeatedly split (including newly emerging subgoals) until no further   *)
  (* splitting is possible                                                   *)
  fun split_loop ([] : (typ list * term list) list) = ([] : (typ list * term list) list)
    | split_loop (subgoal::subgoals)                = (
        case split_once_items sg subgoal of
          SOME new_subgoals => split_loop (new_subgoals @ subgoals)
        | NONE              => subgoal :: split_loop subgoals
      )
  fun is_relevant t  = isSome (decomp sg t)
  (* filter_prems_tac is_relevant: *)
  val relevant_terms = filter_prems_tac_items is_relevant terms
  (* split_tac, NNF normalization: *)
  val split_goals    = split_loop [(Ts, relevant_terms)]
  (* necessary because split_once_tac may normalize terms: *)
  val beta_eta_norm  = map (apsnd (map (Envir.eta_contract o Envir.beta_norm))) split_goals
  (* TRY (etac notE) THEN eq_assume_tac: *)
  val result         = List.filter (not o negated_term_occurs_positively o snd) beta_eta_norm
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
(* !fast_arith_split_limit splits are possible.                              *)

local
  val nnf_simpset =
    empty_ss setmkeqTrue mk_eq_True
    setmksimps (mksimps mksimps_pairs)
    addsimps [imp_conv_disj, iff_conv_conj_imp, de_Morgan_disj, de_Morgan_conj,
      not_all, not_ex, not_not]
  fun prem_nnf_tac i st =
    full_simp_tac (Simplifier.theory_context (Thm.theory_of_thm st) nnf_simpset) i st
in

fun split_once_tac (split_thms : thm list) (i : int) : tactic =
let
  fun cond_split_tac i st =
    let
      val subgoal = Logic.nth_prem (i, Thm.prop_of st)
      val Ts      = rev (map snd (Logic.strip_params subgoal))
      val concl   = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal)
      val cmap    = Splitter.cmap_of_split_thms split_thms
      val splits  = Splitter.split_posns cmap (theory_of_thm st) Ts concl
    in
      if length splits > !fast_arith_split_limit then
        no_tac st
      else
        split_tac split_thms i st
    end
in
  EVERY' [
    REPEAT_DETERM o etac rev_mp,
    cond_split_tac,
    rtac ccontr,
    prem_nnf_tac,
    TRY o REPEAT_ALL_NEW (DETERM o (eresolve_tac [conjE, exE] ORELSE' etac disjE))
  ] i
end

end;  (* local *)

(* remove irrelevant premises, then split the i-th subgoal (and all new      *)
(* subgoals) by using 'split_once_tac' repeatedly.  Beta-eta-normalize new   *)
(* subgoals and finally attempt to solve them by finding an immediate        *)
(* contradiction (i.e. a term and its negation) in their premises.           *)

fun pre_tac i st =
let
  val sg            = theory_of_thm st
  val split_thms    = filter is_split_thm (#splits (ArithTheoryData.get sg))
  fun is_relevant t = isSome (decomp sg t)
in
  DETERM (
    TRY (filter_prems_tac is_relevant i)
      THEN (
        (TRY o REPEAT_ALL_NEW (split_once_tac split_thms))
          THEN_ALL_NEW
            ((fn j => PRIMITIVE
                        (Conv.fconv_rule
                          (Conv.goals_conv (equal j) (Drule.beta_eta_conversion))))
              THEN'
            (TRY o (etac notE THEN' eq_assume_tac)))
      ) i
  ) st
end;

end;  (* LA_Data_Ref *)


structure Fast_Arith =
  Fast_Lin_Arith(structure LA_Logic=LA_Logic and LA_Data=LA_Data_Ref);

val fast_arith_tac         = Fast_Arith.lin_arith_tac false;
val fast_ex_arith_tac      = Fast_Arith.lin_arith_tac;
val trace_arith            = Fast_Arith.trace;
val fast_arith_neq_limit   = Fast_Arith.fast_arith_neq_limit;
val fast_arith_split_limit = LA_Data_Ref.fast_arith_split_limit;

(* reduce contradictory <= to False.
   Most of the work is done by the cancel tactics. *)

val init_lin_arith_data =
 Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, ...} =>
   {add_mono_thms = add_mono_thms @
    @{thms add_mono_thms_ordered_semiring} @ @{thms add_mono_thms_ordered_field},
    mult_mono_thms = mult_mono_thms,
    inj_thms = inj_thms,
    lessD = lessD @ [thm "Suc_leI"],
    neqE = [@{thm linorder_neqE_nat}, @{thm linorder_neqE_ordered_idom}],
    simpset = HOL_basic_ss
      addsimps [@{thm "monoid_add_class.zero_plus.add_0_left"}, @{thm "monoid_add_class.zero_plus.add_0_right"},
        @{thm "Zero_not_Suc"}, @{thm "Suc_not_Zero"}, @{thm "le_0_eq"}, @{thm "One_nat_def"},
        @{thm "order_less_irrefl"}, @{thm "zero_neq_one"}, @{thm "zero_less_one"},
        @{thm "zero_le_one"}, @{thm "zero_neq_one"} RS not_sym, @{thm "not_one_le_zero"},
        @{thm "not_one_less_zero"}]
      addsimprocs [ab_group_add_cancel.sum_conv, ab_group_add_cancel.rel_conv]
       (*abel_cancel helps it work in abstract algebraic domains*)
      addsimprocs nat_cancel_sums_add}) #>
  arith_discrete "nat";

val fast_nat_arith_simproc =
  Simplifier.simproc (the_context ()) "fast_nat_arith"
    ["(m::nat) < n","(m::nat) <= n", "(m::nat) = n"] Fast_Arith.lin_arith_prover;

(* Because of fast_nat_arith_simproc, the arithmetic solver is really only
useful to detect inconsistencies among the premises for subgoals which are
*not* themselves (in)equalities, because the latter activate
fast_nat_arith_simproc anyway. However, it seems cheaper to activate the
solver all the time rather than add the additional check. *)


(* arith proof method *)

local

fun raw_arith_tac ex i st =
  (* FIXME: K true should be replaced by a sensible test (perhaps "isSome o
     decomp sg"? -- but note that the test is applied to terms already before
     they are split/normalized) to speed things up in case there are lots of
     irrelevant terms involved; elimination of min/max can be optimized:
     (max m n + k <= r) = (m+k <= r & n+k <= r)
     (l <= min m n + k) = (l <= m+k & l <= n+k)
  *)
  refute_tac (K true)
    (* Splitting is also done inside fast_arith_tac, but not completely --   *)
    (* split_tac may use split theorems that have not been implemented in    *)
    (* fast_arith_tac (cf. pre_decomp and split_once_items above), and       *)
    (* fast_arith_split_limit may trigger.                                   *)
    (* Therefore splitting outside of fast_arith_tac may allow us to prove   *)
    (* some goals that fast_arith_tac alone would fail on.                   *)
    (REPEAT_DETERM o split_tac (#splits (ArithTheoryData.get (Thm.theory_of_thm st))))
    (fast_ex_arith_tac ex)
    i st;

fun arith_theory_tac i st =
let
  val tactics = #tactics (ArithTheoryData.get (Thm.theory_of_thm st))
in
  FIRST' (map (fn ArithTactic {tactic, ...} => tactic) tactics) i st
end;

in

  val simple_arith_tac = FIRST' [fast_arith_tac,
    ObjectLogic.full_atomize_tac THEN' (REPEAT_DETERM o rtac impI) THEN' raw_arith_tac true];

  val arith_tac = FIRST' [fast_arith_tac,
    ObjectLogic.full_atomize_tac THEN' (REPEAT_DETERM o rtac impI) THEN' raw_arith_tac true,
    arith_theory_tac];

  val silent_arith_tac = FIRST' [fast_arith_tac,
    ObjectLogic.full_atomize_tac THEN' (REPEAT_DETERM o rtac impI) THEN' raw_arith_tac false,
    arith_theory_tac];

  fun arith_method prems =
    Method.METHOD (fn facts => HEADGOAL (Method.insert_tac (prems @ facts) THEN' arith_tac));

end;

(* antisymmetry:
   combines x <= y (or ~(y < x)) and y <= x (or ~(x < y)) into x = y

local
val antisym = mk_meta_eq order_antisym
val not_lessD = @{thm linorder_not_less} RS iffD1
fun prp t thm = (#prop(rep_thm thm) = t)
in
fun antisym_eq prems thm =
  let
    val r = #prop(rep_thm thm);
  in
    case r of
      Tr $ ((c as Const(@{const_name Orderings.less_eq},T)) $ s $ t) =>
        let val r' = Tr $ (c $ t $ s)
        in
          case Library.find_first (prp r') prems of
            NONE =>
              let val r' = Tr $ (HOLogic.Not $ (Const(@{const_name Orderings.less},T) $ s $ t))
              in case Library.find_first (prp r') prems of
                   NONE => []
                 | SOME thm' => [(thm' RS not_lessD) RS (thm RS antisym)]
              end
          | SOME thm' => [thm' RS (thm RS antisym)]
        end
    | Tr $ (Const("Not",_) $ (Const(@{const_name Orderings.less},T) $ s $ t)) =>
        let val r' = Tr $ (Const(@{const_name Orderings.less_eq},T) $ s $ t)
        in
          case Library.find_first (prp r') prems of
            NONE =>
              let val r' = Tr $ (HOLogic.Not $ (Const(@{const_name Orderings.less},T) $ t $ s))
              in case Library.find_first (prp r') prems of
                   NONE => []
                 | SOME thm' =>
                     [(thm' RS not_lessD) RS ((thm RS not_lessD) RS antisym)]
              end
          | SOME thm' => [thm' RS ((thm RS not_lessD) RS antisym)]
        end
    | _ => []
  end
  handle THM _ => []
end;
*)

(* theory setup *)

val arith_setup =
  init_lin_arith_data #>
  (fn thy => (Simplifier.change_simpset_of thy (fn ss => ss
    addsimprocs (nat_cancel_sums @ [fast_nat_arith_simproc])
    addSolver (mk_solver' "lin. arith." Fast_Arith.cut_lin_arith_tac)); thy)) #>
  Method.add_methods
    [("arith", (arith_method o fst) oo Method.syntax Args.bang_facts,
      "decide linear arithmethic")] #>
  Attrib.add_attributes [("arith_split", Attrib.no_args arith_split_add,
    "declaration of split rules for arithmetic procedure")];
