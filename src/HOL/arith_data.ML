(*  Title:      HOL/arith_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, Stefan Berghofer and Tobias Nipkow

Various arithmetic proof procedures.
*)

(*---------------------------------------------------------------------------*)
(* 1. Cancellation of common terms                                           *)
(*---------------------------------------------------------------------------*)

signature ARITH_DATA =
sig
  val nat_cancel_sums_add: simproc list
  val nat_cancel_sums: simproc list
  val nat_cancel_factor: simproc list
  val nat_cancel: simproc list
end;

structure ArithData: ARITH_DATA =
struct


(** abstract syntax of structure nat: 0, Suc, + **)

(* mk_sum, mk_norm_sum *)

val one = HOLogic.mk_nat 1;
val mk_plus = HOLogic.mk_binop "op +";

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*normal form of sums: Suc (... (Suc (a + (b + ...))))*)
fun mk_norm_sum ts =
  let val (ones, sums) = partition (equal one) ts in
    funpow (length ones) HOLogic.mk_Suc (mk_sum sums)
  end;


(* dest_sum *)

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

fun dest_sum tm =
  if HOLogic.is_zero tm then []
  else
    (case try HOLogic.dest_Suc tm of
      Some t => one :: dest_sum t
    | None =>
        (case try dest_plus tm of
          Some (t, u) => dest_sum t @ dest_sum u
        | None => [tm]));


(** generic proof tools **)

(* prove conversions *)

val mk_eqv = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun prove_conv expand_tac norm_tac sg (t, u) =
  mk_meta_eq (prove_goalw_cterm_nocheck [] (cterm_of sg (mk_eqv (t, u)))
    (K [expand_tac, norm_tac]))
  handle ERROR => error ("The error(s) above occurred while trying to prove " ^
    (string_of_cterm (cterm_of sg (mk_eqv (t, u)))));

val subst_equals = prove_goal HOL.thy "[| t = s; u = t |] ==> u = s"
  (fn prems => [cut_facts_tac prems 1, SIMPSET' asm_simp_tac 1]);


(* rewriting *)

fun simp_all rules = ALLGOALS (simp_tac (HOL_ss addsimps rules));

val add_rules = [add_Suc, add_Suc_right, add_0, add_0_right];
val mult_rules = [mult_Suc, mult_Suc_right, mult_0, mult_0_right];



(** cancel common summands **)

structure Sum =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all add_rules THEN simp_all add_ac;
end;

fun gen_uncancel_tac rule ct =
  rtac (instantiate' [] [None, Some ct] (rule RS subst_equals)) 1;


(* nat eq *)

structure EqCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel;
end);


(* nat less *)

structure LessCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_less;
end);


(* nat le *)

structure LeCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_le;
end);


(* nat diff *)

structure DiffCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binop "op -";
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac diff_cancel;
end);



(** cancel common factor **)

structure Factor =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all (add_rules @ mult_rules) THEN simp_all add_ac;
end;

fun mk_cnat n = cterm_of (Theory.sign_of (the_context ())) (HOLogic.mk_nat n);

fun gen_multiply_tac rule k =
  if k > 0 then
    rtac (instantiate' [] [None, Some (mk_cnat (k - 1))] (rule RS subst_equals)) 1
  else no_tac;


(* nat eq *)

structure EqCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_cancel1;
end);


(* nat less *)

structure LessCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_less_cancel1;
end);


(* nat le *)

structure LeCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_le_cancel1;
end);



(** prepare nat_cancel simprocs **)

fun prep_pat s = Thm.read_cterm (Theory.sign_of (the_context ())) (s, HOLogic.termT);
val prep_pats = map prep_pat;

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;

val eq_pats = prep_pats ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", "m = Suc n"];
val less_pats = prep_pats ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n", "m < Suc n"];
val le_pats = prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n", "Suc m <= n", "m <= Suc n"];
val diff_pats = prep_pats ["((l::nat) + m) - n", "(l::nat) - (m + n)", "Suc m - n", "m - Suc n"];

val nat_cancel_sums_add = map prep_simproc
  [("nateq_cancel_sums", eq_pats, EqCancelSums.proc),
   ("natless_cancel_sums", less_pats, LessCancelSums.proc),
   ("natle_cancel_sums", le_pats, LeCancelSums.proc)];

val nat_cancel_sums = nat_cancel_sums_add @
  [prep_simproc("natdiff_cancel_sums", diff_pats, DiffCancelSums.proc)];

val nat_cancel_factor = map prep_simproc
  [("nateq_cancel_factor", eq_pats, EqCancelFactor.proc),
   ("natless_cancel_factor", less_pats, LessCancelFactor.proc),
   ("natle_cancel_factor", le_pats, LeCancelFactor.proc)];

val nat_cancel = nat_cancel_factor @ nat_cancel_sums;


end;

open ArithData;


(*---------------------------------------------------------------------------*)
(* 2. Linear arithmetic                                                      *)
(*---------------------------------------------------------------------------*)

(* Parameters data for general linear arithmetic functor *)

structure LA_Logic: LIN_ARITH_LOGIC =
struct
val ccontr = ccontr;
val conjI = conjI;
val neqE = linorder_neqE;
val notI = notI;
val sym = sym;
val not_lessD = linorder_not_less RS iffD1;
val not_leD = linorder_not_le RS iffD1;


fun mk_Eq thm = (thm RS Eq_FalseI) handle THM _ => (thm RS Eq_TrueI);

val mk_Trueprop = HOLogic.mk_Trueprop;

fun neg_prop(TP$(Const("Not",_)$t)) = TP$t
  | neg_prop(TP$t) = TP $ (Const("Not",HOLogic.boolT-->HOLogic.boolT)$t);

fun is_False thm =
  let val _ $ t = #prop(rep_thm thm)
  in t = Const("False",HOLogic.boolT) end;

fun is_nat(t) = fastype_of1 t = HOLogic.natT;

fun mk_nat_thm sg t =
  let val ct = cterm_of sg t  and cn = cterm_of sg (Var(("n",0),HOLogic.natT))
  in instantiate ([],[(cn,ct)]) le0 end;

end;


(* arith theory data *)

structure ArithTheoryDataArgs =
struct
  val name = "HOL/arith";
  type T = {splits: thm list, discrete: (string * bool) list};

  val empty = {splits = [], discrete = []};
  val copy = I;
  val prep_ext = I;
  fun merge ({splits = splits1, discrete = discrete1}, {splits = splits2, discrete = discrete2}) =
   {splits = Drule.merge_rules (splits1, splits2),
    discrete = merge_alists discrete1 discrete2};
  fun print _ _ = ();
end;

structure ArithTheoryData = TheoryDataFun(ArithTheoryDataArgs);

fun arith_split_add (thy, thm) = (ArithTheoryData.map (fn {splits, discrete} =>
  {splits = thm :: splits, discrete = discrete}) thy, thm);

fun arith_discrete d = ArithTheoryData.map (fn {splits, discrete} =>
  {splits = splits, discrete = d :: discrete});


structure LA_Data_Ref: LIN_ARITH_DATA =
struct

(* Decomposition of terms *)

fun nT (Type("fun",[N,_])) = N = HOLogic.natT
  | nT _ = false;

fun add_atom(t,m,(p,i)) = (case assoc(p,t) of None => ((t,m)::p,i)
                           | Some n => (overwrite(p,(t,n+m:int)), i));

(* Turn term into list of summand * multiplicity plus a constant *)
fun poly(Const("op +",_) $ s $ t, m, pi) = poly(s,m,poly(t,m,pi))
  | poly(all as Const("op -",T) $ s $ t, m, pi) =
      if nT T then add_atom(all,m,pi)
      else poly(s,m,poly(t,~1*m,pi))
  | poly(Const("uminus",_) $ t, m, pi) = poly(t,~1*m,pi)
  | poly(Const("0",_), _, pi) = pi
  | poly(Const("Suc",_)$t, m, (p,i)) = poly(t, m, (p,i+m))
  | poly(all as Const("op *",_) $ (Const("Numeral.number_of",_)$c) $ t, m, pi)=
      (poly(t,m*HOLogic.dest_binum c,pi)
       handle TERM _ => add_atom(all,m,pi))
  | poly(all as Const("op *",_) $ t $ (Const("Numeral.number_of",_)$c), m, pi)=
      (poly(t,m*HOLogic.dest_binum c,pi)
       handle TERM _ => add_atom(all,m,pi))
  | poly(all as Const("Numeral.number_of",_)$t,m,(p,i)) =
     ((p,i + m*HOLogic.dest_binum t)
      handle TERM _ => add_atom(all,m,(p,i)))
  | poly x  = add_atom x;

fun decomp2(rel,lhs,rhs) =
  let val (p,i) = poly(lhs,1,([],0)) and (q,j) = poly(rhs,1,([],0))
  in case rel of
       "op <"  => Some(p,i,"<",q,j)
     | "op <=" => Some(p,i,"<=",q,j)
     | "op ="  => Some(p,i,"=",q,j)
     | _       => None
  end;

fun negate(Some(x,i,rel,y,j,d)) = Some(x,i,"~"^rel,y,j,d)
  | negate None = None;

fun decomp1 discrete (T,xxx) =
  (case T of
     Type("fun",[Type(D,[]),_]) =>
       (case assoc(discrete,D) of
          None => None
        | Some d => (case decomp2 xxx of
                       None => None
                     | Some(p,i,rel,q,j) => Some(p,i,rel,q,j,d)))
   | _ => None);

fun decomp2 discrete (_$(Const(rel,T)$lhs$rhs)) = decomp1 discrete (T,(rel,lhs,rhs))
  | decomp2 discrete (_$(Const("Not",_)$(Const(rel,T)$lhs$rhs))) =
      negate(decomp1 discrete (T,(rel,lhs,rhs)))
  | decomp2 discrete _ = None

val decomp = decomp2 o #discrete o ArithTheoryData.get_sg;

end;


structure Fast_Arith =
  Fast_Lin_Arith(structure LA_Logic=LA_Logic and LA_Data=LA_Data_Ref);

val fast_arith_tac = Fast_Arith.lin_arith_tac
and trace_arith    = Fast_Arith.trace;

local

(* reduce contradictory <= to False.
   Most of the work is done by the cancel tactics.
*)
val add_rules = [add_0,add_0_right,Zero_not_Suc,Suc_not_Zero,le_0_eq];

val add_mono_thms_nat = map (fn s => prove_goal (the_context ()) s
 (fn prems => [cut_facts_tac prems 1,
               blast_tac (claset() addIs [add_le_mono]) 1]))
["(i <= j) & (k <= l) ==> i + k <= j + (l::nat)",
 "(i  = j) & (k <= l) ==> i + k <= j + (l::nat)",
 "(i <= j) & (k  = l) ==> i + k <= j + (l::nat)",
 "(i  = j) & (k  = l) ==> i + k  = j + (l::nat)"
];

in

val init_lin_arith_data =
 Fast_Arith.setup @
 [Fast_Arith.map_data (fn {add_mono_thms, lessD, simpset = _} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_nat,
    lessD = lessD @ [Suc_leI],
    simpset = HOL_basic_ss addsimps add_rules addsimprocs nat_cancel_sums_add}),
  ArithTheoryData.init, arith_discrete ("nat", true)];

end;


local
val nat_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of (the_context ())) (s, HOLogic.boolT))
      ["(m::nat) < n","(m::nat) <= n", "(m::nat) = n"];
in
val fast_nat_arith_simproc = mk_simproc
  "fast_nat_arith" nat_arith_simproc_pats Fast_Arith.lin_arith_prover;
end;

(* Because of fast_nat_arith_simproc, the arithmetic solver is really only
useful to detect inconsistencies among the premises for subgoals which are
*not* themselves (in)equalities, because the latter activate
fast_nat_arith_simproc anyway. However, it seems cheaper to activate the
solver all the time rather than add the additional check. *)


(* arith proof method *)

(* FIXME: K true should be replaced by a sensible test to speed things up
   in case there are lots of irrelevant terms involved;
   elimination of min/max can be optimized:
   (max m n + k <= r) = (m+k <= r & n+k <= r)
   (l <= min m n + k) = (l <= m+k & l <= n+k)
*)
fun arith_tac i st =
  refute_tac (K true) (REPEAT o split_tac (#splits (ArithTheoryData.get_sg (Thm.sign_of_thm st))))
             ((REPEAT_DETERM o etac linorder_neqE) THEN' fast_arith_tac) i st;

fun arith_method prems =
  Method.METHOD (fn facts => HEADGOAL (Method.insert_tac (prems @ facts) THEN' arith_tac));


(* theory setup *)

val arith_setup =
 [Simplifier.change_simpset_of (op addsimprocs) nat_cancel] @
  init_lin_arith_data @
  [Simplifier.change_simpset_of (op addSolver)
   (mk_solver "lin. arith." Fast_Arith.cut_lin_arith_tac),
  Simplifier.change_simpset_of (op addsimprocs) [fast_nat_arith_simproc],
  Method.add_methods [("arith", (arith_method o #2) oo Method.syntax Args.bang_facts,
    "decide linear arithmethic")],
  Attrib.add_attributes [("arith_split",
    (Attrib.no_args arith_split_add, Attrib.no_args Attrib.undef_local_attribute),
    "declaration of split rules for arithmetic procedure")]];
