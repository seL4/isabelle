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



(** prepare nat_cancel simprocs **)

fun prep_pat s = HOLogic.read_cterm (Theory.sign_of (the_context ())) s;
val prep_pats = map prep_pat;

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;

val eq_pats = prep_pats ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", 
                         "m = Suc n"];
val less_pats = prep_pats ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n",
                           "m < Suc n"];
val le_pats = prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n", 
                         "Suc m <= n", "m <= Suc n"];
val diff_pats = prep_pats ["((l::nat) + m) - n", "(l::nat) - (m + n)", 
                           "Suc m - n", "m - Suc n"];

val nat_cancel_sums_add = map prep_simproc
  [("nateq_cancel_sums",   eq_pats,   EqCancelSums.proc),
   ("natless_cancel_sums", less_pats, LessCancelSums.proc),
   ("natle_cancel_sums",   le_pats,   LeCancelSums.proc)];

val nat_cancel_sums = nat_cancel_sums_add @
  [prep_simproc("natdiff_cancel_sums", diff_pats, DiffCancelSums.proc)];


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
  type T = {splits: thm list, inj_consts: (string * typ)list, discrete: (string * bool) list};

  val empty = {splits = [], inj_consts = [], discrete = []};
  val copy = I;
  val prep_ext = I;
  fun merge ({splits= splits1, inj_consts= inj_consts1, discrete= discrete1},
             {splits= splits2, inj_consts= inj_consts2, discrete= discrete2}) =
   {splits = Drule.merge_rules (splits1, splits2),
    inj_consts = merge_lists inj_consts1 inj_consts2,
    discrete = merge_alists discrete1 discrete2};
  fun print _ _ = ();
end;

structure ArithTheoryData = TheoryDataFun(ArithTheoryDataArgs);

fun arith_split_add (thy, thm) = (ArithTheoryData.map (fn {splits,inj_consts,discrete} =>
  {splits= thm::splits, inj_consts= inj_consts, discrete= discrete}) thy, thm);

fun arith_discrete d = ArithTheoryData.map (fn {splits,inj_consts,discrete} =>
  {splits = splits, inj_consts = inj_consts, discrete = d :: discrete});

fun arith_inj_const c = ArithTheoryData.map (fn {splits,inj_consts,discrete} =>
  {splits = splits, inj_consts = c :: inj_consts, discrete = discrete});


structure LA_Data_Ref: LIN_ARITH_DATA =
struct

(* Decomposition of terms *)

fun nT (Type("fun",[N,_])) = N = HOLogic.natT
  | nT _ = false;

fun add_atom(t,m,(p,i)) = (case assoc(p,t) of None => ((t,m)::p,i)
                           | Some n => (overwrite(p,(t,ratadd(n,m))), i));

exception Zero;

fun rat_of_term(numt,dent) =
  let val num = HOLogic.dest_binum numt and den = HOLogic.dest_binum dent
  in if den = 0 then raise Zero else int_ratdiv(num,den) end;

(* Warning: in rare cases number_of encloses a non-numeral,
   in which case dest_binum raises TERM; hence all the handles below.
   Same for Suc-terms that turn out not to be numerals -
   although the simplifier should eliminate those anyway...
*)

fun number_of_Sucs (Const("Suc",_) $ n) = number_of_Sucs n + 1
  | number_of_Sucs t = if HOLogic.is_zero t then 0
                       else raise TERM("number_of_Sucs",[])

(* decompose nested multiplications, bracketing them to the right and combining all
   their coefficients
*)

fun demult((mC as Const("op *",_)) $ s $ t,m) = ((case s of
        Const("Numeral.number_of",_)$n
        => demult(t,ratmul(m,rat_of_int(HOLogic.dest_binum n)))
      | Const("Suc",_) $ _
        => demult(t,ratmul(m,rat_of_int(number_of_Sucs s)))
      | Const("op *",_) $ s1 $ s2 => demult(mC $ s1 $ (mC $ s2 $ t),m)
      | Const("HOL.divide",_) $ numt $ (Const("Numeral.number_of",_)$dent) =>
          let val den = HOLogic.dest_binum dent
          in if den = 0 then raise Zero
             else demult(mC $ numt $ t,ratmul(m, ratinv(rat_of_int den)))
          end
      | _ => atomult(mC,s,t,m)
      ) handle TERM _ => atomult(mC,s,t,m))
  | demult(atom as Const("HOL.divide",_) $ t $ (Const("Numeral.number_of",_)$dent), m) =
      (let val den = HOLogic.dest_binum dent
       in if den = 0 then raise Zero else demult(t,ratmul(m, ratinv(rat_of_int den))) end
       handle TERM _ => (Some atom,m))
  | demult(t as Const("Numeral.number_of",_)$n,m) =
      ((None,ratmul(m,rat_of_int(HOLogic.dest_binum n)))
       handle TERM _ => (Some t,m))
  | demult(atom,m) = (Some atom,m)

and atomult(mC,atom,t,m) = (case demult(t,m) of (None,m') => (Some atom,m')
                            | (Some t',m') => (Some(mC $ atom $ t'),m'))

fun decomp2 inj_consts (rel,lhs,rhs) =
let
(* Turn term into list of summand * multiplicity plus a constant *)
fun poly(Const("op +",_) $ s $ t, m, pi) = poly(s,m,poly(t,m,pi))
  | poly(all as Const("op -",T) $ s $ t, m, pi) =
      if nT T then add_atom(all,m,pi)
      else poly(s,m,poly(t,ratneg m,pi))
  | poly(Const("uminus",_) $ t, m, pi) = poly(t,ratneg m,pi)
  | poly(Const("0",_), _, pi) = pi
  | poly(Const("1",_), m, (p,i)) = (p,ratadd(i,m))
  | poly(Const("Suc",_)$t, m, (p,i)) = poly(t, m, (p,ratadd(i,m)))
  | poly(t as Const("op *",_) $ _ $ _, m, pi as (p,i)) =
      (case demult(t,m) of
         (None,m') => (p,ratadd(i,m))
       | (Some u,m') => add_atom(u,m',pi))
  | poly(t as Const("HOL.divide",_) $ _ $ _, m, pi as (p,i)) =
      (case demult(t,m) of
         (None,m') => (p,ratadd(i,m))
       | (Some u,m') => add_atom(u,m',pi))
  | poly(all as (Const("Numeral.number_of",_)$t,m,(p,i))) =
      ((p,ratadd(i,ratmul(m,rat_of_int(HOLogic.dest_binum t))))
       handle TERM _ => add_atom all)
  | poly(all as Const f $ x, m, pi) =
      if f mem inj_consts then poly(x,m,pi) else add_atom(all,m,pi)
  | poly x  = add_atom x;

val (p,i) = poly(lhs,rat_of_int 1,([],rat_of_int 0))
and (q,j) = poly(rhs,rat_of_int 1,([],rat_of_int 0))

  in case rel of
       "op <"  => Some(p,i,"<",q,j)
     | "op <=" => Some(p,i,"<=",q,j)
     | "op ="  => Some(p,i,"=",q,j)
     | _       => None
  end handle Zero => None;

fun negate(Some(x,i,rel,y,j,d)) = Some(x,i,"~"^rel,y,j,d)
  | negate None = None;

fun decomp1 (discrete,inj_consts) (T,xxx) =
  (case T of
     Type("fun",[Type(D,[]),_]) =>
       (case assoc(discrete,D) of
          None => None
        | Some d => (case decomp2 inj_consts xxx of
                       None => None
                     | Some(p,i,rel,q,j) => Some(p,i,rel,q,j,d)))
   | _ => None);

fun decomp2 data (_$(Const(rel,T)$lhs$rhs)) = decomp1 data (T,(rel,lhs,rhs))
  | decomp2 data (_$(Const("Not",_)$(Const(rel,T)$lhs$rhs))) =
      negate(decomp1 data (T,(rel,lhs,rhs)))
  | decomp2 data _ = None

fun decomp sg =
  let val {discrete, inj_consts, ...} = ArithTheoryData.get_sg sg
  in decomp2 (discrete,inj_consts) end

fun number_of(n,T) = HOLogic.number_of_const T $ (HOLogic.mk_bin n)

end;


structure Fast_Arith =
  Fast_Lin_Arith(structure LA_Logic=LA_Logic and LA_Data=LA_Data_Ref);

val fast_arith_tac = Fast_Arith.lin_arith_tac
and trace_arith    = Fast_Arith.trace;

local

(* reduce contradictory <= to False.
   Most of the work is done by the cancel tactics.
*)
val add_rules = [add_0,add_0_right,Zero_not_Suc,Suc_not_Zero,le_0_eq,One_nat_def];

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
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset = _} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_nat,
    mult_mono_thms = mult_mono_thms,
    inj_thms = inj_thms,
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
local

fun raw_arith_tac i st =
  refute_tac (K true) (REPEAT o split_tac (#splits (ArithTheoryData.get_sg (Thm.sign_of_thm st))))
             ((REPEAT_DETERM o etac linorder_neqE) THEN' fast_arith_tac) i st;

in

val arith_tac = fast_arith_tac ORELSE' (ObjectLogic.atomize_tac THEN' raw_arith_tac);

fun arith_method prems =
  Method.METHOD (fn facts => HEADGOAL (Method.insert_tac (prems @ facts) THEN' arith_tac));

end;


(* theory setup *)

val arith_setup =
 [Simplifier.change_simpset_of (op addsimprocs) nat_cancel_sums] @
  init_lin_arith_data @
  [Simplifier.change_simpset_of (op addSolver)
   (mk_solver "lin. arith." Fast_Arith.cut_lin_arith_tac),
  Simplifier.change_simpset_of (op addsimprocs) [fast_nat_arith_simproc],
  Method.add_methods [("arith", (arith_method o #2) oo Method.syntax Args.bang_facts,
    "decide linear arithmethic")],
  Attrib.add_attributes [("arith_split",
    (Attrib.no_args arith_split_add, Attrib.no_args Attrib.undef_local_attribute),
    "declaration of split rules for arithmetic procedure")]];
