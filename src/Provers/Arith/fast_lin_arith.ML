(*  Title:      Provers/Arith/fast_lin_arith.ML
    Author:     Tobias Nipkow and Tjark Weber and Sascha Boehme

A generic linear arithmetic package.

Only take premises and conclusions into account that are already
(negated) (in)equations. lin_arith_simproc tries to prove or disprove
the term.
*)

(*** Data needed for setting up the linear arithmetic package ***)

signature LIN_ARITH_LOGIC =
sig
  val conjI       : thm  (* P ==> Q ==> P & Q *)
  val ccontr      : thm  (* (~ P ==> False) ==> P *)
  val notI        : thm  (* (P ==> False) ==> ~ P *)
  val not_lessD   : thm  (* ~(m < n) ==> n <= m *)
  val not_leD     : thm  (* ~(m <= n) ==> n < m *)
  val sym         : thm  (* x = y ==> y = x *)
  val trueI       : thm  (* True *)
  val mk_Eq       : thm -> thm
  val atomize     : thm -> thm list
  val mk_Trueprop : term -> term
  val neg_prop    : term -> term
  val is_False    : thm -> bool
  val is_nat      : typ list * term -> bool
  val mk_nat_thm  : theory -> term -> thm
end;
(*
mk_Eq(~in) = `in == False'
mk_Eq(in) = `in == True'
where `in' is an (in)equality.

neg_prop(t) = neg  if t is wrapped up in Trueprop and neg is the
  (logically) negated version of t (again wrapped up in Trueprop),
  where the negation of a negative term is the term itself (no
  double negation!); raises TERM ("neg_prop", [t]) if t is not of
  the form 'Trueprop $ _'

is_nat(parameter-types,t) =  t:nat
mk_nat_thm(t) = "0 <= t"
*)

signature LIN_ARITH_DATA =
sig
  (*internal representation of linear (in-)equations:*)
  type decomp = (term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat * bool
  val decomp: Proof.context -> term -> decomp option
  val domain_is_nat: term -> bool

  (*preprocessing, performed on a representation of subgoals as list of premises:*)
  val pre_decomp: Proof.context -> typ list * term list -> (typ list * term list) list

  (*preprocessing, performed on the goal -- must do the same as 'pre_decomp':*)
  val pre_tac: simpset -> int -> tactic

  (*the limit on the number of ~= allowed; because each ~= is split
    into two cases, this can lead to an explosion*)
  val neq_limit: int Config.T

  val verbose: bool Config.T
  val trace: bool Config.T
end;
(*
decomp(`x Rel y') should yield (p,i,Rel,q,j,d)
   where Rel is one of "<", "~<", "<=", "~<=" and "=" and
         p (q, respectively) is the decomposition of the sum term x
         (y, respectively) into a list of summand * multiplicity
         pairs and a constant summand and d indicates if the domain
         is discrete.

domain_is_nat(`x Rel y') t should yield true iff x is of type "nat".

The relationship between pre_decomp and pre_tac is somewhat tricky.  The
internal representation of a subgoal and the corresponding theorem must
be modified by pre_decomp (pre_tac, resp.) in a corresponding way.  See
the comment for split_items below.  (This is even necessary for eta- and
beta-equivalent modifications, as some of the lin. arith. code is not
insensitive to them.)

ss must reduce contradictory <= to False.
   It should also cancel common summands to keep <= reduced;
   otherwise <= can grow to massive proportions.
*)

signature FAST_LIN_ARITH =
sig
  val prems_lin_arith_tac: simpset -> int -> tactic
  val lin_arith_tac: Proof.context -> bool -> int -> tactic
  val lin_arith_simproc: simpset -> term -> thm option
  val map_data:
    ({add_mono_thms: thm list, mult_mono_thms: thm list, inj_thms: thm list,
      lessD: thm list, neqE: thm list, simpset: Simplifier.simpset,
      number_of: (theory -> typ -> int -> cterm) option} ->
     {add_mono_thms: thm list, mult_mono_thms: thm list, inj_thms: thm list,
      lessD: thm list, neqE: thm list, simpset: Simplifier.simpset,
      number_of: (theory -> typ -> int -> cterm) option}) ->
      Context.generic -> Context.generic
  val add_inj_thms: thm list -> Context.generic -> Context.generic
  val add_lessD: thm -> Context.generic -> Context.generic
  val add_simps: thm list -> Context.generic -> Context.generic
  val add_simprocs: simproc list -> Context.generic -> Context.generic
  val set_number_of: (theory -> typ -> int -> cterm) -> Context.generic -> Context.generic
end;

functor Fast_Lin_Arith
  (structure LA_Logic: LIN_ARITH_LOGIC and LA_Data: LIN_ARITH_DATA): FAST_LIN_ARITH =
struct


(** theory data **)

structure Data = Generic_Data
(
  type T =
   {add_mono_thms: thm list,
    mult_mono_thms: thm list,
    inj_thms: thm list,
    lessD: thm list,
    neqE: thm list,
    simpset: Simplifier.simpset,
    number_of: (theory -> typ -> int -> cterm) option};

  val empty : T =
   {add_mono_thms = [], mult_mono_thms = [], inj_thms = [],
    lessD = [], neqE = [], simpset = Simplifier.empty_ss,
    number_of = NONE};
  val extend = I;
  fun merge
    ({add_mono_thms = add_mono_thms1, mult_mono_thms = mult_mono_thms1, inj_thms = inj_thms1,
      lessD = lessD1, neqE = neqE1, simpset = simpset1, number_of = number_of1},
     {add_mono_thms = add_mono_thms2, mult_mono_thms = mult_mono_thms2, inj_thms = inj_thms2,
      lessD = lessD2, neqE = neqE2, simpset = simpset2, number_of = number_of2}) : T =
    {add_mono_thms = Thm.merge_thms (add_mono_thms1, add_mono_thms2),
     mult_mono_thms = Thm.merge_thms (mult_mono_thms1, mult_mono_thms2),
     inj_thms = Thm.merge_thms (inj_thms1, inj_thms2),
     lessD = Thm.merge_thms (lessD1, lessD2),
     neqE = Thm.merge_thms (neqE1, neqE2),
     simpset = Simplifier.merge_ss (simpset1, simpset2),
     number_of = merge_options (number_of1, number_of2)};
);

val map_data = Data.map;
val get_data = Data.get o Context.Proof;

fun map_inj_thms f {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset, number_of} =
  {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms, inj_thms = f inj_thms,
    lessD = lessD, neqE = neqE, simpset = simpset, number_of = number_of};

fun map_lessD f {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset, number_of} =
  {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms, inj_thms = inj_thms,
    lessD = f lessD, neqE = neqE, simpset = simpset, number_of = number_of};

fun map_simpset f {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset, number_of} =
  {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms, inj_thms = inj_thms,
    lessD = lessD, neqE = neqE, simpset = f simpset, number_of = number_of};

fun add_inj_thms thms = map_data (map_inj_thms (append thms));
fun add_lessD thm = map_data (map_lessD (fn thms => thms @ [thm]));
fun add_simps thms = map_data (map_simpset (fn simpset => simpset addsimps thms));
fun add_simprocs procs = map_data (map_simpset (fn simpset => simpset addsimprocs procs));

fun set_number_of f =
  map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset, ...} =>
   {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms, inj_thms = inj_thms,
    lessD = lessD, neqE = neqE, simpset = simpset, number_of = SOME f});

fun number_of ctxt =
  (case Data.get (Context.Proof ctxt) of
    {number_of = SOME f, ...} => f (Proof_Context.theory_of ctxt)
  | _ => fn _ => fn _ => raise CTERM ("number_of", []));



(*** A fast decision procedure ***)
(*** Code ported from HOL Light ***)
(* possible optimizations:
   use (var,coeff) rep or vector rep  tp save space;
   treat non-negative atoms separately rather than adding 0 <= atom
*)

datatype lineq_type = Eq | Le | Lt;

datatype injust = Asm of int
                | Nat of int (* index of atom *)
                | LessD of injust
                | NotLessD of injust
                | NotLeD of injust
                | NotLeDD of injust
                | Multiplied of int * injust
                | Added of injust * injust;

datatype lineq = Lineq of int * lineq_type * int list * injust;

(* ------------------------------------------------------------------------- *)
(* Finding a (counter) example from the trace of a failed elimination        *)
(* ------------------------------------------------------------------------- *)
(* Examples are represented as rational numbers,                             *)
(* Dont blame John Harrison for this code - it is entirely mine. TN          *)

exception NoEx;

(* Coding: (i,true,cs) means i <= cs and (i,false,cs) means i < cs.
   In general, true means the bound is included, false means it is excluded.
   Need to know if it is a lower or upper bound for unambiguous interpretation!
*)

fun elim_eqns (Lineq (i, Le, cs, _)) = [(i, true, cs)]
  | elim_eqns (Lineq (i, Eq, cs, _)) = [(i, true, cs),(~i, true, map ~ cs)]
  | elim_eqns (Lineq (i, Lt, cs, _)) = [(i, false, cs)];

(* PRE: ex[v] must be 0! *)
fun eval ex v (a, le, cs) =
  let
    val rs = map Rat.rat_of_int cs;
    val rsum = fold2 (Rat.add oo Rat.mult) rs ex Rat.zero;
  in (Rat.mult (Rat.add (Rat.rat_of_int a) (Rat.neg rsum)) (Rat.inv (nth rs v)), le) end;
(* If nth rs v < 0, le should be negated.
   Instead this swap is taken into account in ratrelmin2.
*)

fun ratrelmin2 (x as (r, ler), y as (s, les)) =
  case Rat.ord (r, s)
   of EQUAL => (r, (not ler) andalso (not les))
    | LESS => x
    | GREATER => y;

fun ratrelmax2 (x as (r, ler), y as (s, les)) =
  case Rat.ord (r, s)
   of EQUAL => (r, ler andalso les)
    | LESS => y
    | GREATER => x;

val ratrelmin = foldr1 ratrelmin2;
val ratrelmax = foldr1 ratrelmax2;

fun ratexact up (r, exact) =
  if exact then r else
  let
    val (_, q) = Rat.quotient_of_rat r;
    val nth = Rat.inv (Rat.rat_of_int q);
  in Rat.add r (if up then nth else Rat.neg nth) end;

fun ratmiddle (r, s) = Rat.mult (Rat.add r s) (Rat.inv Rat.two);

fun choose2 d ((lb, exactl), (ub, exactu)) =
  let val ord = Rat.sign lb in
  if (ord = LESS orelse exactl) andalso (ord = GREATER orelse exactu)
    then Rat.zero
    else if not d then
      if ord = GREATER
        then if exactl then lb else ratmiddle (lb, ub)
        else if exactu then ub else ratmiddle (lb, ub)
      else (*discrete domain, both bounds must be exact*)
      if ord = GREATER
        then let val lb' = Rat.roundup lb in
          if Rat.le lb' ub then lb' else raise NoEx end
        else let val ub' = Rat.rounddown ub in
          if Rat.le lb ub' then ub' else raise NoEx end
  end;

fun findex1 discr (v, lineqs) ex =
  let
    val nz = filter (fn (Lineq (_, _, cs, _)) => nth cs v <> 0) lineqs;
    val ineqs = maps elim_eqns nz;
    val (ge, le) = List.partition (fn (_,_,cs) => nth cs v > 0) ineqs
    val lb = ratrelmax (map (eval ex v) ge)
    val ub = ratrelmin (map (eval ex v) le)
  in nth_map v (K (choose2 (nth discr v) (lb, ub))) ex end;

fun elim1 v x =
  map (fn (a,le,bs) => (Rat.add a (Rat.neg (Rat.mult (nth bs v) x)), le,
                        nth_map v (K Rat.zero) bs));

fun single_var v (_, _, cs) = case filter_out (curry (op =) EQUAL o Rat.sign) cs
 of [x] => x =/ nth cs v
  | _ => false;

(* The base case:
   all variables occur only with positive or only with negative coefficients *)
fun pick_vars discr (ineqs,ex) =
  let val nz = filter_out (fn (_,_,cs) => forall (curry (op =) EQUAL o Rat.sign) cs) ineqs
  in case nz of [] => ex
     | (_,_,cs) :: _ =>
       let val v = find_index (not o curry (op =) EQUAL o Rat.sign) cs
           val d = nth discr v;
           val pos = not (Rat.sign (nth cs v) = LESS);
           val sv = filter (single_var v) nz;
           val minmax =
             if pos then if d then Rat.roundup o fst o ratrelmax
                         else ratexact true o ratrelmax
                    else if d then Rat.rounddown o fst o ratrelmin
                         else ratexact false o ratrelmin
           val bnds = map (fn (a,le,bs) => (Rat.mult a (Rat.inv (nth bs v)), le)) sv
           val x = minmax((Rat.zero,if pos then true else false)::bnds)
           val ineqs' = elim1 v x nz
           val ex' = nth_map v (K x) ex
       in pick_vars discr (ineqs',ex') end
  end;

fun findex0 discr n lineqs =
  let val ineqs = maps elim_eqns lineqs
      val rineqs = map (fn (a,le,cs) => (Rat.rat_of_int a, le, map Rat.rat_of_int cs))
                       ineqs
  in pick_vars discr (rineqs,replicate n Rat.zero) end;

(* ------------------------------------------------------------------------- *)
(* End of counterexample finder. The actual decision procedure starts here.  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Calculate new (in)equality type after addition.                           *)
(* ------------------------------------------------------------------------- *)

fun find_add_type(Eq,x) = x
  | find_add_type(x,Eq) = x
  | find_add_type(_,Lt) = Lt
  | find_add_type(Lt,_) = Lt
  | find_add_type(Le,Le) = Le;

(* ------------------------------------------------------------------------- *)
(* Multiply out an (in)equation.                                             *)
(* ------------------------------------------------------------------------- *)

fun multiply_ineq n (i as Lineq(k,ty,l,just)) =
  if n = 1 then i
  else if n = 0 andalso ty = Lt then raise Fail "multiply_ineq"
  else if n < 0 andalso (ty=Le orelse ty=Lt) then raise Fail "multiply_ineq"
  else Lineq (n * k, ty, map (Integer.mult n) l, Multiplied (n, just));

(* ------------------------------------------------------------------------- *)
(* Add together (in)equations.                                               *)
(* ------------------------------------------------------------------------- *)

fun add_ineq (Lineq (k1,ty1,l1,just1)) (Lineq (k2,ty2,l2,just2)) =
  let val l = map2 Integer.add l1 l2
  in Lineq(k1+k2,find_add_type(ty1,ty2),l,Added(just1,just2)) end;

(* ------------------------------------------------------------------------- *)
(* Elimination of variable between a single pair of (in)equations.           *)
(* If they're both inequalities, 1st coefficient must be +ve, 2nd -ve.       *)
(* ------------------------------------------------------------------------- *)

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val c1 = nth l1 v and c2 = nth l2 v
      val m = Integer.lcm (abs c1) (abs c2)
      val m1 = m div (abs c1) and m2 = m div (abs c2)
      val (n1,n2) =
        if (c1 >= 0) = (c2 >= 0)
        then if ty1 = Eq then (~m1,m2)
             else if ty2 = Eq then (m1,~m2)
                  else raise Fail "elim_var"
        else (m1,m2)
      val (p1,p2) = if ty1=Eq andalso ty2=Eq andalso (n1 = ~1 orelse n2 = ~1)
                    then (~n1,~n2) else (n1,n2)
  in add_ineq (multiply_ineq p1 i1) (multiply_ineq p2 i2) end;

(* ------------------------------------------------------------------------- *)
(* The main refutation-finding code.                                         *)
(* ------------------------------------------------------------------------- *)

fun is_trivial (Lineq(_,_,l,_)) = forall (fn i => i=0) l;

fun is_contradictory (Lineq(k,ty,_,_)) =
  case ty  of Eq => k <> 0 | Le => k > 0 | Lt => k >= 0;

fun calc_blowup l =
  let val (p,n) = List.partition (curry (op <) 0) (filter (curry (op <>) 0) l)
  in length p * length n end;

(* ------------------------------------------------------------------------- *)
(* Main elimination code:                                                    *)
(*                                                                           *)
(* (1) Looks for immediate solutions (false assertions with no variables).   *)
(*                                                                           *)
(* (2) If there are any equations, picks a variable with the lowest absolute *)
(* coefficient in any of them, and uses it to eliminate.                     *)
(*                                                                           *)
(* (3) Otherwise, chooses a variable in the inequality to minimize the       *)
(* blowup (number of consequences generated) and eliminates it.              *)
(* ------------------------------------------------------------------------- *)

fun extract_first p =
  let
    fun extract xs (y::ys) = if p y then (y, xs @ ys) else extract (y::xs) ys
      | extract xs [] = raise Empty
  in extract [] end;

fun print_ineqs ctxt ineqs =
  if Config.get ctxt LA_Data.trace then
     tracing(cat_lines(""::map (fn Lineq(c,t,l,_) =>
       string_of_int c ^
       (case t of Eq => " =  " | Lt=> " <  " | Le => " <= ") ^
       commas(map string_of_int l)) ineqs))
  else ();

type history = (int * lineq list) list;
datatype result = Success of injust | Failure of history;

fun elim ctxt (ineqs, hist) =
  let val _ = print_ineqs ctxt ineqs
      val (triv, nontriv) = List.partition is_trivial ineqs in
  if not (null triv)
  then case Library.find_first is_contradictory triv of
         NONE => elim ctxt (nontriv, hist)
       | SOME(Lineq(_,_,_,j)) => Success j
  else
  if null nontriv then Failure hist
  else
  let val (eqs, noneqs) = List.partition (fn (Lineq(_,ty,_,_)) => ty=Eq) nontriv in
  if not (null eqs) then
     let val c =
           fold (fn Lineq(_,_,l,_) => fn cs => union (op =) l cs) eqs []
           |> filter (fn i => i <> 0)
           |> sort (int_ord o pairself abs)
           |> hd
         val (eq as Lineq(_,_,ceq,_),othereqs) =
               extract_first (fn Lineq(_,_,l,_) => member (op =) l c) eqs
         val v = find_index (fn v => v = c) ceq
         val (ioth,roth) = List.partition (fn (Lineq(_,_,l,_)) => nth l v = 0)
                                     (othereqs @ noneqs)
         val others = map (elim_var v eq) roth @ ioth
     in elim ctxt (others,(v,nontriv)::hist) end
  else
  let val lists = map (fn (Lineq(_,_,l,_)) => l) noneqs
      val numlist = 0 upto (length (hd lists) - 1)
      val coeffs = map (fn i => map (fn xs => nth xs i) lists) numlist
      val blows = map calc_blowup coeffs
      val iblows = blows ~~ numlist
      val nziblows = filter_out (fn (i, _) => i = 0) iblows
  in if null nziblows then Failure((~1,nontriv)::hist)
     else
     let val (c,v) = hd(sort (fn (x,y) => int_ord(fst(x),fst(y))) nziblows)
         val (no,yes) = List.partition (fn (Lineq(_,_,l,_)) => nth l v = 0) ineqs
         val (pos,neg) = List.partition(fn (Lineq(_,_,l,_)) => nth l v > 0) yes
     in elim ctxt (no @ map_product (elim_var v) pos neg, (v,nontriv)::hist) end
  end
  end
  end;

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

fun trace_thm ctxt msgs th =
 (if Config.get ctxt LA_Data.trace
  then tracing (cat_lines (msgs @ [Display.string_of_thm ctxt th]))
  else (); th);

fun trace_term ctxt msgs t =
 (if Config.get ctxt LA_Data.trace
  then tracing (cat_lines (msgs @ [Syntax.string_of_term ctxt t]))
  else (); t);

fun trace_msg ctxt msg =
  if Config.get ctxt LA_Data.trace then tracing msg else ();

val union_term = union Pattern.aeconv;
val union_bterm = union (fn ((b:bool, t), (b', t')) => b = b' andalso Pattern.aeconv (t, t'));

fun add_atoms (lhs, _, _, rhs, _, _) =
  union_term (map fst lhs) o union_term (map fst rhs);

fun atoms_of ds = fold add_atoms ds [];

(*
Simplification may detect a contradiction 'prematurely' due to type
information: n+1 <= 0 is simplified to False and does not need to be crossed
with 0 <= n.
*)
local
  exception FalseE of thm
in

fun mkthm ss asms (just: injust) =
  let
    val ctxt = Simplifier.the_context ss;
    val thy = Proof_Context.theory_of ctxt;
    val {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset, ...} = get_data ctxt;
    val number_of = number_of ctxt;
    val simpset' = Simplifier.inherit_context ss simpset;
    fun only_concl f thm =
      if Thm.no_prems thm then f (Thm.concl_of thm) else NONE;
    val atoms = atoms_of (map_filter (only_concl (LA_Data.decomp ctxt)) asms);

    fun use_first rules thm =
      get_first (fn th => SOME (thm RS th) handle THM _ => NONE) rules

    fun add2 thm1 thm2 =
      use_first add_mono_thms (thm1 RS (thm2 RS LA_Logic.conjI));
    fun try_add thms thm = get_first (fn th => add2 th thm) thms;

    fun add_thms thm1 thm2 =
      (case add2 thm1 thm2 of
        NONE =>
          (case try_add ([thm1] RL inj_thms) thm2 of
            NONE =>
              (the (try_add ([thm2] RL inj_thms) thm1)
                handle Option =>
                  (trace_thm ctxt [] thm1; trace_thm ctxt [] thm2;
                   raise Fail "Linear arithmetic: failed to add thms"))
          | SOME thm => thm)
      | SOME thm => thm);

    fun mult_by_add n thm =
      let fun mul i th = if i = 1 then th else mul (i - 1) (add_thms thm th)
      in mul n thm end;

    val rewr = Simplifier.rewrite simpset';
    val rewrite_concl = Conv.fconv_rule (Conv.concl_conv ~1 (Conv.arg_conv
      (Conv.binop_conv rewr)));
    fun discharge_prem thm = if Thm.nprems_of thm = 0 then thm else
      let val cv = Conv.arg1_conv (Conv.arg_conv rewr)
      in Thm.implies_elim (Conv.fconv_rule cv thm) LA_Logic.trueI end

    fun mult n thm =
      (case use_first mult_mono_thms thm of
        NONE => mult_by_add n thm
      | SOME mth =>
          let
            val cv = mth |> Thm.cprop_of |> Drule.strip_imp_concl
              |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg1
            val T = #T (Thm.rep_cterm cv)
          in
            mth
            |> Thm.instantiate ([], [(cv, number_of T n)])
            |> rewrite_concl
            |> discharge_prem
            handle CTERM _ => mult_by_add n thm
                 | THM _ => mult_by_add n thm
          end);

    fun mult_thm (n, thm) =
      if n = ~1 then thm RS LA_Logic.sym
      else if n < 0 then mult (~n) thm RS LA_Logic.sym
      else mult n thm;

    fun simp thm =
      let val thm' = trace_thm ctxt ["Simplified:"] (full_simplify simpset' thm)
      in if LA_Logic.is_False thm' then raise FalseE thm' else thm' end;

    fun mk (Asm i) = trace_thm ctxt ["Asm " ^ string_of_int i] (nth asms i)
      | mk (Nat i) = trace_thm ctxt ["Nat " ^ string_of_int i] (LA_Logic.mk_nat_thm thy (nth atoms i))
      | mk (LessD j) = trace_thm ctxt ["L"] (hd ([mk j] RL lessD))
      | mk (NotLeD j) = trace_thm ctxt ["NLe"] (mk j RS LA_Logic.not_leD)
      | mk (NotLeDD j) = trace_thm ctxt ["NLeD"] (hd ([mk j RS LA_Logic.not_leD] RL lessD))
      | mk (NotLessD j) = trace_thm ctxt ["NL"] (mk j RS LA_Logic.not_lessD)
      | mk (Added (j1, j2)) = simp (trace_thm ctxt ["+"] (add_thms (mk j1) (mk j2)))
      | mk (Multiplied (n, j)) =
          (trace_msg ctxt ("*" ^ string_of_int n); trace_thm ctxt ["*"] (mult_thm (n, mk j)))

  in
    let
      val _ = trace_msg ctxt "mkthm";
      val thm = trace_thm ctxt ["Final thm:"] (mk just);
      val fls = simplify simpset' thm;
      val _ = trace_thm ctxt ["After simplification:"] fls;
      val _ =
        if LA_Logic.is_False fls then ()
        else
         (tracing (cat_lines
           (["Assumptions:"] @ map (Display.string_of_thm ctxt) asms @ [""] @
            ["Proved:", Display.string_of_thm ctxt fls, ""]));
          warning "Linear arithmetic should have refuted the assumptions.\n\
            \Please inform Tobias Nipkow.")
    in fls end
    handle FalseE thm => trace_thm ctxt ["False reached early:"] thm
  end;

end;

fun coeff poly atom =
  AList.lookup Pattern.aeconv poly atom |> the_default 0;

fun integ(rlhs,r,rel,rrhs,s,d) =
let val (rn,rd) = Rat.quotient_of_rat r and (sn,sd) = Rat.quotient_of_rat s
    val m = Integer.lcms(map (abs o snd o Rat.quotient_of_rat) (r :: s :: map snd rlhs @ map snd rrhs))
    fun mult(t,r) =
        let val (i,j) = Rat.quotient_of_rat r
        in (t,i * (m div j)) end
in (m,(map mult rlhs, rn*(m div rd), rel, map mult rrhs, sn*(m div sd), d)) end

fun mklineq atoms =
  fn (item, k) =>
  let val (m, (lhs,i,rel,rhs,j,discrete)) = integ item
      val lhsa = map (coeff lhs) atoms
      and rhsa = map (coeff rhs) atoms
      val diff = map2 (curry (op -)) rhsa lhsa
      val c = i-j
      val just = Asm k
      fun lineq(c,le,cs,j) = Lineq(c,le,cs, if m=1 then j else Multiplied(m,j))
  in case rel of
      "<="   => lineq(c,Le,diff,just)
     | "~<=" => if discrete
                then lineq(1-c,Le,map (op ~) diff,NotLeDD(just))
                else lineq(~c,Lt,map (op ~) diff,NotLeD(just))
     | "<"   => if discrete
                then lineq(c+1,Le,diff,LessD(just))
                else lineq(c,Lt,diff,just)
     | "~<"  => lineq(~c,Le,map (op~) diff,NotLessD(just))
     | "="   => lineq(c,Eq,diff,just)
     | _     => raise Fail ("mklineq" ^ rel)
  end;

(* ------------------------------------------------------------------------- *)
(* Print (counter) example                                                   *)
(* ------------------------------------------------------------------------- *)

fun print_atom((a,d),r) =
  let val (p,q) = Rat.quotient_of_rat r
      val s = if d then string_of_int p else
              if p = 0 then "0"
              else string_of_int p ^ "/" ^ string_of_int q
  in a ^ " = " ^ s end;

fun is_variable (Free _) = true
  | is_variable (Var _) = true
  | is_variable (Bound _) = true
  | is_variable _ = false

fun trace_ex ctxt params atoms discr n (hist: history) =
  case hist of
    [] => ()
  | (v, lineqs) :: hist' =>
      let
        val frees = map Free params
        fun show_term t = Syntax.string_of_term ctxt (subst_bounds (frees, t))
        val start =
          if v = ~1 then (hist', findex0 discr n lineqs)
          else (hist, replicate n Rat.zero)
        val produce_ex =
          map print_atom #> commas #>
          prefix "Counterexample (possibly spurious):\n"
        val ex = (
          uncurry (fold (findex1 discr)) start
          |> map2 pair (atoms ~~ discr)
          |> filter (fn ((t, _), _) => is_variable t)
          |> map (apfst (apfst show_term))
          |> (fn [] => NONE | sdss => SOME (produce_ex sdss)))
          handle NoEx => NONE
      in
        case ex of
          SOME s =>
            (warning "Linear arithmetic failed -- see trace for a (potentially spurious) counterexample.";
              tracing s)
        | NONE => warning "Linear arithmetic failed"
      end;

(* ------------------------------------------------------------------------- *)

fun mknat (pTs : typ list) (ixs : int list) (atom : term, i : int) : lineq option =
  if LA_Logic.is_nat (pTs, atom)
  then let val l = map (fn j => if j=i then 1 else 0) ixs
       in SOME (Lineq (0, Le, l, Nat i)) end
  else NONE;

(* This code is tricky. It takes a list of premises in the order they occur
in the subgoal. Numerical premises are coded as SOME(tuple), non-numerical
ones as NONE. Going through the premises, each numeric one is converted into
a Lineq. The tricky bit is to convert ~= which is split into two cases < and
>. Thus split_items returns a list of equation systems. This may blow up if
there are many ~=, but in practice it does not seem to happen. The really
tricky bit is to arrange the order of the cases such that they coincide with
the order in which the cases are in the end generated by the tactic that
applies the generated refutation thms (see function 'refute_tac').

For variables n of type nat, a constraint 0 <= n is added.
*)

(* FIXME: To optimize, the splitting of cases and the search for refutations *)
(*        could be intertwined: separate the first (fully split) case,       *)
(*        refute it, continue with splitting and refuting.  Terminate with   *)
(*        failure as soon as a case could not be refuted; i.e. delay further *)
(*        splitting until after a refutation for other cases has been found. *)

fun split_items ctxt do_pre split_neq (Ts, terms) : (typ list * (LA_Data.decomp * int) list) list =
let
  (* splits inequalities '~=' into '<' and '>'; this corresponds to *)
  (* 'REPEAT_DETERM (eresolve_tac neqE i)' at the theorem/tactic    *)
  (* level                                                          *)
  (* FIXME: this is currently sensitive to the order of theorems in *)
  (*        neqE:  The theorem for type "nat" must come first.  A   *)
  (*        better (i.e. less likely to break when neqE changes)    *)
  (*        implementation should *test* which theorem from neqE    *)
  (*        can be applied, and split the premise accordingly.      *)
  fun elim_neq (ineqs : (LA_Data.decomp option * bool) list) :
               (LA_Data.decomp option * bool) list list =
  let
    fun elim_neq' nat_only ([] : (LA_Data.decomp option * bool) list) :
                  (LA_Data.decomp option * bool) list list =
          [[]]
      | elim_neq' nat_only ((NONE, is_nat) :: ineqs) =
          map (cons (NONE, is_nat)) (elim_neq' nat_only ineqs)
      | elim_neq' nat_only ((ineq as (SOME (l, i, rel, r, j, d), is_nat)) :: ineqs) =
          if rel = "~=" andalso (not nat_only orelse is_nat) then
            (* [| ?l ~= ?r; ?l < ?r ==> ?R; ?r < ?l ==> ?R |] ==> ?R *)
            elim_neq' nat_only (ineqs @ [(SOME (l, i, "<", r, j, d), is_nat)]) @
            elim_neq' nat_only (ineqs @ [(SOME (r, j, "<", l, i, d), is_nat)])
          else
            map (cons ineq) (elim_neq' nat_only ineqs)
  in
    ineqs |> elim_neq' true
          |> maps (elim_neq' false)
  end

  fun ignore_neq (NONE, bool) = (NONE, bool)
    | ignore_neq (ineq as SOME (_, _, rel, _, _, _), bool) =
      if rel = "~=" then (NONE, bool) else (ineq, bool)

  fun number_hyps _ []             = []
    | number_hyps n (NONE::xs)     = number_hyps (n+1) xs
    | number_hyps n ((SOME x)::xs) = (x, n) :: number_hyps (n+1) xs

  val result = (Ts, terms)
    |> (* user-defined preprocessing of the subgoal *)
       (if do_pre then LA_Data.pre_decomp ctxt else Library.single)
    |> tap (fn subgoals => trace_msg ctxt ("Preprocessing yields " ^
         string_of_int (length subgoals) ^ " subgoal(s) total."))
    |> (* produce the internal encoding of (in-)equalities *)
       map (apsnd (map (fn t => (LA_Data.decomp ctxt t, LA_Data.domain_is_nat t))))
    |> (* splitting of inequalities *)
       map (apsnd (if split_neq then elim_neq else
                     Library.single o map ignore_neq))
    |> maps (fn (Ts, subgoals) => map (pair Ts o map fst) subgoals)
    |> (* numbering of hypotheses, ignoring irrelevant ones *)
       map (apsnd (number_hyps 0))
in
  trace_msg ctxt ("Splitting of inequalities yields " ^
    string_of_int (length result) ^ " subgoal(s) total.");
  result
end;

fun add_datoms ((lhs,_,_,rhs,_,d) : LA_Data.decomp, _) (dats : (bool * term) list) =
  union_bterm (map (pair d o fst) lhs) (union_bterm (map (pair d o fst) rhs) dats);

fun discr (initems : (LA_Data.decomp * int) list) : bool list =
  map fst (fold add_datoms initems []);

fun refutes ctxt params show_ex :
    (typ list * (LA_Data.decomp * int) list) list -> injust list -> injust list option =
  let
    fun refute ((Ts, initems : (LA_Data.decomp * int) list) :: initemss) (js: injust list) =
          let
            val atoms = atoms_of (map fst initems)
            val n = length atoms
            val mkleq = mklineq atoms
            val ixs = 0 upto (n - 1)
            val iatoms = atoms ~~ ixs
            val natlineqs = map_filter (mknat Ts ixs) iatoms
            val ineqs = map mkleq initems @ natlineqs
          in case elim ctxt (ineqs, []) of
               Success j =>
                 (trace_msg ctxt ("Contradiction! (" ^ string_of_int (length js + 1) ^ ")");
                  refute initemss (js @ [j]))
             | Failure hist =>
                 (if not show_ex orelse not (Config.get ctxt LA_Data.verbose) then ()
                  else
                    let
                      val (param_names, ctxt') = ctxt |> Variable.variant_fixes (map fst params)
                      val (more_names, ctxt'') = ctxt' |> Variable.variant_fixes
                        (Name.invent (Variable.names_of ctxt') Name.uu (length Ts - length params))
                      val params' = (more_names @ param_names) ~~ Ts
                    in
                      trace_ex ctxt'' params' atoms (discr initems) n hist
                    end; NONE)
          end
      | refute [] js = SOME js
  in refute end;

fun refute ctxt params show_ex do_pre split_neq terms : injust list option =
  refutes ctxt params show_ex (split_items ctxt do_pre split_neq
    (map snd params, terms)) [];

fun count P xs = length (filter P xs);

fun prove ctxt params show_ex do_pre Hs concl : bool * injust list option =
  let
    val _ = trace_msg ctxt "prove:"
    (* append the negated conclusion to 'Hs' -- this corresponds to     *)
    (* 'DETERM (resolve_tac [LA_Logic.notI, LA_Logic.ccontr] i)' at the *)
    (* theorem/tactic level                                             *)
    val Hs' = Hs @ [LA_Logic.neg_prop concl]
    fun is_neq NONE                 = false
      | is_neq (SOME (_,_,r,_,_,_)) = (r = "~=")
    val neq_limit = Config.get ctxt LA_Data.neq_limit
    val split_neq = count is_neq (map (LA_Data.decomp ctxt) Hs') <= neq_limit
  in
    if split_neq then ()
    else
      trace_msg ctxt ("neq_limit exceeded (current value is " ^
        string_of_int neq_limit ^ "), ignoring all inequalities");
    (split_neq, refute ctxt params show_ex do_pre split_neq Hs')
  end handle TERM ("neg_prop", _) =>
    (* since no meta-logic negation is available, we can only fail if   *)
    (* the conclusion is not of the form 'Trueprop $ _' (simply         *)
    (* dropping the conclusion doesn't work either, because even        *)
    (* 'False' does not imply arbitrary 'concl::prop')                  *)
    (trace_msg ctxt "prove failed (cannot negate conclusion).";
      (false, NONE));

fun refute_tac ss (i, split_neq, justs) =
  fn state =>
    let
      val ctxt = Simplifier.the_context ss;
      val _ = trace_thm ctxt
        ["refute_tac (on subgoal " ^ string_of_int i ^ ", with " ^
          string_of_int (length justs) ^ " justification(s)):"] state
      val {neqE, ...} = get_data ctxt;
      fun just1 j =
        (* eliminate inequalities *)
        (if split_neq then
          REPEAT_DETERM (eresolve_tac neqE i)
        else
          all_tac) THEN
          PRIMITIVE (trace_thm ctxt ["State after neqE:"]) THEN
          (* use theorems generated from the actual justifications *)
          Subgoal.FOCUS (fn {prems, ...} => rtac (mkthm ss prems j) 1) ctxt i
    in
      (* rewrite "[| A1; ...; An |] ==> B" to "[| A1; ...; An; ~B |] ==> False" *)
      DETERM (resolve_tac [LA_Logic.notI, LA_Logic.ccontr] i) THEN
      (* user-defined preprocessing of the subgoal *)
      DETERM (LA_Data.pre_tac ss i) THEN
      PRIMITIVE (trace_thm ctxt ["State after pre_tac:"]) THEN
      (* prove every resulting subgoal, using its justification *)
      EVERY (map just1 justs)
    end  state;

(*
Fast but very incomplete decider. Only premises and conclusions
that are already (negated) (in)equations are taken into account.
*)
fun simpset_lin_arith_tac ss show_ex = SUBGOAL (fn (A, i) =>
  let
    val ctxt = Simplifier.the_context ss
    val params = rev (Logic.strip_params A)
    val Hs = Logic.strip_assums_hyp A
    val concl = Logic.strip_assums_concl A
    val _ = trace_term ctxt ["Trying to refute subgoal " ^ string_of_int i] A
  in
    case prove ctxt params show_ex true Hs concl of
      (_, NONE) => (trace_msg ctxt "Refutation failed."; no_tac)
    | (split_neq, SOME js) => (trace_msg ctxt "Refutation succeeded.";
                               refute_tac ss (i, split_neq, js))
  end);

fun prems_lin_arith_tac ss =
  Method.insert_tac (Simplifier.prems_of ss) THEN'
  simpset_lin_arith_tac ss false;

fun lin_arith_tac ctxt =
  simpset_lin_arith_tac (Simplifier.context ctxt Simplifier.empty_ss);



(** Forward proof from theorems **)

(* More tricky code. Needs to arrange the proofs of the multiple cases (due
to splits of ~= premises) such that it coincides with the order of the cases
generated by function split_items. *)

datatype splittree = Tip of thm list
                   | Spl of thm * cterm * splittree * cterm * splittree;

(* "(ct1 ==> ?R) ==> (ct2 ==> ?R) ==> ?R" is taken to (ct1, ct2) *)

fun extract (imp : cterm) : cterm * cterm =
let val (Il, r)    = Thm.dest_comb imp
    val (_, imp1)  = Thm.dest_comb Il
    val (Ict1, _)  = Thm.dest_comb imp1
    val (_, ct1)   = Thm.dest_comb Ict1
    val (Ir, _)    = Thm.dest_comb r
    val (_, Ict2r) = Thm.dest_comb Ir
    val (Ict2, _)  = Thm.dest_comb Ict2r
    val (_, ct2)   = Thm.dest_comb Ict2
in (ct1, ct2) end;

fun splitasms ctxt (asms : thm list) : splittree =
let val {neqE, ...} = get_data ctxt
    fun elim_neq [] (asms', []) = Tip (rev asms')
      | elim_neq [] (asms', asms) = Tip (rev asms' @ asms)
      | elim_neq (neq :: neqs) (asms', []) = elim_neq neqs ([],rev asms')
      | elim_neq (neqs as (neq :: _)) (asms', asm::asms) =
      (case get_first (fn th => SOME (asm COMP th) handle THM _ => NONE) [neq] of
        SOME spl =>
          let val (ct1, ct2) = extract (cprop_of spl)
              val thm1 = Thm.assume ct1
              val thm2 = Thm.assume ct2
          in Spl (spl, ct1, elim_neq neqs (asms', asms@[thm1]),
            ct2, elim_neq neqs (asms', asms@[thm2]))
          end
      | NONE => elim_neq neqs (asm::asms', asms))
in elim_neq neqE ([], asms) end;

fun fwdproof ss (Tip asms : splittree) (j::js : injust list) = (mkthm ss asms j, js)
  | fwdproof ss (Spl (thm, ct1, tree1, ct2, tree2)) js =
      let
        val (thm1, js1) = fwdproof ss tree1 js
        val (thm2, js2) = fwdproof ss tree2 js1
        val thm1' = Thm.implies_intr ct1 thm1
        val thm2' = Thm.implies_intr ct2 thm2
      in (thm2' COMP (thm1' COMP thm), js2) end;
      (* FIXME needs handle THM _ => NONE ? *)

fun prover ss thms Tconcl (js : injust list) split_neq pos : thm option =
  let
    val ctxt = Simplifier.the_context ss
    val thy = Proof_Context.theory_of ctxt
    val nTconcl = LA_Logic.neg_prop Tconcl
    val cnTconcl = cterm_of thy nTconcl
    val nTconclthm = Thm.assume cnTconcl
    val tree = (if split_neq then splitasms ctxt else Tip) (thms @ [nTconclthm])
    val (Falsethm, _) = fwdproof ss tree js
    val contr = if pos then LA_Logic.ccontr else LA_Logic.notI
    val concl = Thm.implies_intr cnTconcl Falsethm COMP contr
  in SOME (trace_thm ctxt ["Proved by lin. arith. prover:"] (LA_Logic.mk_Eq concl)) end
  (*in case concl contains ?-var, which makes assume fail:*)   (* FIXME Variable.import_terms *)
  handle THM _ => NONE;

(* PRE: concl is not negated!
   This assumption is OK because
   1. lin_arith_simproc tries both to prove and disprove concl and
   2. lin_arith_simproc is applied by the Simplifier which
      dives into terms and will thus try the non-negated concl anyway.
*)
fun lin_arith_simproc ss concl =
  let
    val ctxt = Simplifier.the_context ss
    val thms = maps LA_Logic.atomize (Simplifier.prems_of ss)
    val Hs = map Thm.prop_of thms
    val Tconcl = LA_Logic.mk_Trueprop concl
  in
    case prove ctxt [] false false Hs Tconcl of (* concl provable? *)
      (split_neq, SOME js) => prover ss thms Tconcl js split_neq true
    | (_, NONE) =>
        let val nTconcl = LA_Logic.neg_prop Tconcl in
          case prove ctxt [] false false Hs nTconcl of (* ~concl provable? *)
            (split_neq, SOME js) => prover ss thms nTconcl js split_neq false
          | (_, NONE) => NONE
        end
  end;

end;
