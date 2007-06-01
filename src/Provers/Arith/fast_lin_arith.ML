(*  Title:      Provers/Arith/fast_lin_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998  TU Munich

A generic linear arithmetic package.
It provides two tactics

    lin_arith_tac:         int -> tactic
cut_lin_arith_tac: thms -> int -> tactic

and a simplification procedure

    lin_arith_prover: theory -> simpset -> term -> thm option

Only take premises and conclusions into account that are already (negated)
(in)equations. lin_arith_prover tries to prove or disprove the term.
*)

(* Debugging: set Fast_Arith.trace *)

(*** Data needed for setting up the linear arithmetic package ***)

signature LIN_ARITH_LOGIC =
sig
  val conjI       : thm  (* P ==> Q ==> P & Q *)
  val ccontr      : thm  (* (~ P ==> False) ==> P *)
  val notI        : thm  (* (P ==> False) ==> ~ P *)
  val not_lessD   : thm  (* ~(m < n) ==> n <= m *)
  val not_leD     : thm  (* ~(m <= n) ==> n < m *)
  val sym         : thm  (* x = y ==> y = x *)
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
  (* internal representation of linear (in-)equations: *)
  type decompT = (term * Rat.rat) list * Rat.rat * string * (term * Rat.rat) list * Rat.rat * bool
  val decomp: theory -> term -> decompT option
  val domain_is_nat : term -> bool
  (* preprocessing, performed on a representation of subgoals as list of premises: *)
  val pre_decomp: theory -> typ list * term list -> (typ list * term list) list
  (* preprocessing, performed on the goal -- must do the same as 'pre_decomp': *)
  val pre_tac   : int -> Tactical.tactic
  val number_of : IntInf.int * typ -> term
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
  val map_data: ({add_mono_thms: thm list, mult_mono_thms: thm list, inj_thms: thm list,
                 lessD: thm list, neqE: thm list, simpset: Simplifier.simpset}
                 -> {add_mono_thms: thm list, mult_mono_thms: thm list, inj_thms: thm list,
                     lessD: thm list, neqE: thm list, simpset: Simplifier.simpset})
                -> theory -> theory
  val trace: bool ref
  val fast_arith_neq_limit: int ref
  val lin_arith_prover: theory -> simpset -> term -> thm option
  val     lin_arith_tac:    bool -> int -> tactic
  val cut_lin_arith_tac: simpset -> int -> tactic
end;

functor Fast_Lin_Arith(structure LA_Logic:LIN_ARITH_LOGIC
                       and       LA_Data:LIN_ARITH_DATA) : FAST_LIN_ARITH =
struct


(** theory data **)

structure Data = TheoryDataFun
(
  type T = {add_mono_thms: thm list, mult_mono_thms: thm list, inj_thms: thm list,
            lessD: thm list, neqE: thm list, simpset: Simplifier.simpset};

  val empty = {add_mono_thms = [], mult_mono_thms = [], inj_thms = [],
               lessD = [], neqE = [], simpset = Simplifier.empty_ss};
  val copy = I;
  val extend = I;

  fun merge _
    ({add_mono_thms= add_mono_thms1, mult_mono_thms= mult_mono_thms1, inj_thms= inj_thms1,
      lessD = lessD1, neqE=neqE1, simpset = simpset1},
     {add_mono_thms= add_mono_thms2, mult_mono_thms= mult_mono_thms2, inj_thms= inj_thms2,
      lessD = lessD2, neqE=neqE2, simpset = simpset2}) =
    {add_mono_thms = Drule.merge_rules (add_mono_thms1, add_mono_thms2),
     mult_mono_thms = Drule.merge_rules (mult_mono_thms1, mult_mono_thms2),
     inj_thms = Drule.merge_rules (inj_thms1, inj_thms2),
     lessD = Drule.merge_rules (lessD1, lessD2),
     neqE = Drule.merge_rules (neqE1, neqE2),
     simpset = Simplifier.merge_ss (simpset1, simpset2)};
);

val map_data = Data.map;



(*** A fast decision procedure ***)
(*** Code ported from HOL Light ***)
(* possible optimizations:
   use (var,coeff) rep or vector rep  tp save space;
   treat non-negative atoms separately rather than adding 0 <= atom
*)

val trace = ref false;

datatype lineq_type = Eq | Le | Lt;

datatype injust = Asm of int
                | Nat of int (* index of atom *)
                | LessD of injust
                | NotLessD of injust
                | NotLeD of injust
                | NotLeDD of injust
                | Multiplied of IntInf.int * injust
                | Multiplied2 of IntInf.int * injust
                | Added of injust * injust;

datatype lineq = Lineq of IntInf.int * lineq_type * IntInf.int list * injust;

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
fun eval ex v (a:IntInf.int,le,cs:IntInf.int list) =
  let
    val rs = map Rat.rat_of_int cs;
    val rsum = fold2 (Rat.add oo Rat.mult) rs ex Rat.zero;
  in (Rat.mult (Rat.add (Rat.rat_of_int a) (Rat.neg rsum)) (Rat.inv (nth rs v)), le) end;
(* If nth rs v < 0, le should be negated.
   Instead this swap is taken into account in ratrelmin2.
*)

fun ratrelmin2 (x as (r, ler), y as (s, les)) =
  case Rat.cmp (r, s)
   of EQUAL => (r, (not ler) andalso (not les))
    | LESS => x
    | GREATER => y;

fun ratrelmax2 (x as (r, ler), y as (s, les)) =
  case Rat.cmp (r, s)
   of EQUAL => (r, ler andalso les)
    | LESS => y
    | GREATER => x;

val ratrelmin = foldr1 ratrelmin2;
val ratrelmax = foldr1 ratrelmax2;

fun ratexact up (r, exact) =
  if exact then r else
  let
    val (p, q) = Rat.quotient_of_rat r;
    val nth = Rat.inv (Rat.rat_of_int q);
  in Rat.add r (if up then nth else Rat.neg nth) end;

fun ratmiddle (r, s) = Rat.mult (Rat.add r s) (Rat.inv Rat.two);

fun choose2 d ((lb, exactl), (ub, exactu)) =
  let val ord = Rat.cmp_zero lb in
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

fun single_var v (_, _, cs) = case filter_out (curry (op =) EQUAL o Rat.cmp_zero) cs
 of [x] => x =/ nth cs v
  | _ => false;

(* The base case:
   all variables occur only with positive or only with negative coefficients *)
fun pick_vars discr (ineqs,ex) =
  let val nz = filter_out (fn (_,_,cs) => forall (curry (op =) EQUAL o Rat.cmp_zero) cs) ineqs
  in case nz of [] => ex
     | (_,_,cs) :: _ =>
       let val v = find_index (not o curry (op =) EQUAL o Rat.cmp_zero) cs
           val d = nth discr v;
           val pos = not (Rat.cmp_zero (nth cs v) = LESS);
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
(* End of counter example finder. The actual decision procedure starts here. *)
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
  else if n = 0 andalso ty = Lt then sys_error "multiply_ineq"
  else if n < 0 andalso (ty=Le orelse ty=Lt) then sys_error "multiply_ineq"
  else Lineq (n * k, ty, map (curry op* n) l, Multiplied (n, just));

(* ------------------------------------------------------------------------- *)
(* Add together (in)equations.                                               *)
(* ------------------------------------------------------------------------- *)

fun add_ineq (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val l = map2 (curry (op +)) l1 l2
  in Lineq(k1+k2,find_add_type(ty1,ty2),l,Added(just1,just2)) end;

(* ------------------------------------------------------------------------- *)
(* Elimination of variable between a single pair of (in)equations.           *)
(* If they're both inequalities, 1st coefficient must be +ve, 2nd -ve.       *)
(* ------------------------------------------------------------------------- *)

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val c1 = nth l1 v and c2 = nth l2 v
      val m = lcm(abs c1, abs c2)
      val m1 = m div (abs c1) and m2 = m div (abs c2)
      val (n1,n2) =
        if (c1 >= 0) = (c2 >= 0)
        then if ty1 = Eq then (~m1,m2)
             else if ty2 = Eq then (m1,~m2)
                  else sys_error "elim_var"
        else (m1,m2)
      val (p1,p2) = if ty1=Eq andalso ty2=Eq andalso (n1 = ~1 orelse n2 = ~1)
                    then (~n1,~n2) else (n1,n2)
  in add_ineq (multiply_ineq n1 i1) (multiply_ineq n2 i2) end;

(* ------------------------------------------------------------------------- *)
(* The main refutation-finding code.                                         *)
(* ------------------------------------------------------------------------- *)

fun is_trivial (Lineq(_,_,l,_)) = forall (fn i => i=0) l;

fun is_answer (ans as Lineq(k,ty,l,_)) =
  case ty  of Eq => k <> 0 | Le => k > 0 | Lt => k >= 0;

fun calc_blowup (l:IntInf.int list) =
  let val (p,n) = List.partition (curry (op <) 0) (List.filter (curry (op <>) 0) l)
  in (length p) * (length n) end;

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

fun allpairs f xs ys =
  List.concat (map (fn x => map (fn y => f x y) ys) xs);

fun extract_first p =
  let fun extract xs (y::ys) = if p y then (SOME y,xs@ys)
                               else extract (y::xs) ys
        | extract xs []      = (NONE,xs)
  in extract [] end;

fun print_ineqs ineqs =
  if !trace then
     tracing(cat_lines(""::map (fn Lineq(c,t,l,_) =>
       IntInf.toString c ^
       (case t of Eq => " =  " | Lt=> " <  " | Le => " <= ") ^
       commas(map IntInf.toString l)) ineqs))
  else ();

type history = (int * lineq list) list;
datatype result = Success of injust | Failure of history;

fun elim (ineqs, hist) =
  let val dummy = print_ineqs ineqs
      val (triv, nontriv) = List.partition is_trivial ineqs in
  if not (null triv)
  then case Library.find_first is_answer triv of
         NONE => elim (nontriv, hist)
       | SOME(Lineq(_,_,_,j)) => Success j
  else
  if null nontriv then Failure hist
  else
  let val (eqs, noneqs) = List.partition (fn (Lineq(_,ty,_,_)) => ty=Eq) nontriv in
  if not (null eqs) then
     let val clist = Library.foldl (fn (cs,Lineq(_,_,l,_)) => l union cs) ([],eqs)
         val sclist = sort (fn (x,y) => IntInf.compare(abs(x),abs(y)))
                           (List.filter (fn i => i<>0) clist)
         val c = hd sclist
         val (SOME(eq as Lineq(_,_,ceq,_)),othereqs) =
               extract_first (fn Lineq(_,_,l,_) => c mem l) eqs
         val v = find_index_eq c ceq
         val (ioth,roth) = List.partition (fn (Lineq(_,_,l,_)) => nth l v = 0)
                                     (othereqs @ noneqs)
         val others = map (elim_var v eq) roth @ ioth
     in elim(others,(v,nontriv)::hist) end
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
     in elim(no @ allpairs (elim_var v) pos neg, (v,nontriv)::hist) end
  end
  end
  end;

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

fun trace_thm (msg : string) (th : thm) : thm =
    (if !trace then (tracing msg; tracing (Display.string_of_thm th)) else (); th);

fun trace_msg (msg : string) : unit =
    if !trace then tracing msg else ();

(* FIXME OPTIMIZE!!!! (partly done already)
   Addition/Multiplication need i*t representation rather than t+t+...
   Get rid of Mulitplied(2). For Nat LA_Data.number_of should return Suc^n
   because Numerals are not known early enough.

Simplification may detect a contradiction 'prematurely' due to type
information: n+1 <= 0 is simplified to False and does not need to be crossed
with 0 <= n.
*)
local
 exception FalseE of thm
in
fun mkthm (sg:theory, ss) (asms:thm list) (just:injust) : thm =
  let val {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset, ...} =
          Data.get sg;
      val simpset' = Simplifier.inherit_context ss simpset;
      val atoms = Library.foldl (fn (ats, (lhs,_,_,rhs,_,_)) =>
                            map fst lhs  union  (map fst rhs  union  ats))
                        ([], List.mapPartial (fn thm => if Thm.no_prems thm
                                              then LA_Data.decomp sg (concl_of thm)
                                              else NONE) asms)

      fun add2 thm1 thm2 =
        let val conj = thm1 RS (thm2 RS LA_Logic.conjI)
        in get_first (fn th => SOME(conj RS th) handle THM _ => NONE) add_mono_thms
        end;
      fun try_add [] _ = NONE
        | try_add (thm1::thm1s) thm2 = case add2 thm1 thm2 of
             NONE => try_add thm1s thm2 | some => some;

      fun addthms thm1 thm2 =
        case add2 thm1 thm2 of
          NONE => (case try_add ([thm1] RL inj_thms) thm2 of
                     NONE => ( the (try_add ([thm2] RL inj_thms) thm1)
                               handle Option =>
                               (trace_thm "" thm1; trace_thm "" thm2;
                                sys_error "Lin.arith. failed to add thms")
                             )
                   | SOME thm => thm)
        | SOME thm => thm;

      fun multn(n,thm) =
        let fun mul(i,th) = if i=1 then th else mul(i-1, addthms thm th)
        in if n < 0 then mul(~n,thm) RS LA_Logic.sym else mul(n,thm) end;

      fun multn2(n,thm) =
        let val SOME(mth) =
              get_first (fn th => SOME(thm RS th) handle THM _ => NONE) mult_mono_thms
            fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (Thm.theory_of_thm th) var;
            val cv = cvar(mth, hd(prems_of mth));
            val ct = cterm_of sg (LA_Data.number_of(n,#T(rep_cterm cv)))
        in instantiate ([],[(cv,ct)]) mth end

      fun simp thm =
        let val thm' = trace_thm "Simplified:" (full_simplify simpset' thm)
        in if LA_Logic.is_False thm' then raise FalseE thm' else thm' end

      fun mk (Asm i)              = trace_thm ("Asm " ^ Int.toString i) (nth asms i)
        | mk (Nat i)              = trace_thm ("Nat " ^ Int.toString i) (LA_Logic.mk_nat_thm sg (nth atoms i))
        | mk (LessD j)            = trace_thm "L" (hd ([mk j] RL lessD))
        | mk (NotLeD j)           = trace_thm "NLe" (mk j RS LA_Logic.not_leD)
        | mk (NotLeDD j)          = trace_thm "NLeD" (hd ([mk j RS LA_Logic.not_leD] RL lessD))
        | mk (NotLessD j)         = trace_thm "NL" (mk j RS LA_Logic.not_lessD)
        | mk (Added (j1, j2))     = simp (trace_thm "+" (addthms (mk j1) (mk j2)))
        | mk (Multiplied (n, j))  = (trace_msg ("*" ^ IntInf.toString n); trace_thm "*" (multn (n, mk j)))
        | mk (Multiplied2 (n, j)) = simp (trace_msg ("**" ^ IntInf.toString n); trace_thm "**" (multn2 (n, mk j)))

  in trace_msg "mkthm";
     let val thm = trace_thm "Final thm:" (mk just)
     in let val fls = simplify simpset' thm
        in trace_thm "After simplification:" fls;
           if LA_Logic.is_False fls then fls
           else
            (tracing "Assumptions:"; List.app (tracing o Display.string_of_thm) asms;
             tracing "Proved:"; tracing (Display.string_of_thm fls);
             warning "Linear arithmetic should have refuted the assumptions.\n\
                     \Please inform Tobias Nipkow (nipkow@in.tum.de).";
             fls)
        end
     end handle FalseE thm => trace_thm "False reached early:" thm
  end
end;

fun coeff poly atom : IntInf.int =
  AList.lookup (op =) poly atom |> the_default 0;

fun lcms (is : IntInf.int list) : IntInf.int = Library.foldl lcm (1, is);

fun integ(rlhs,r,rel,rrhs,s,d) =
let val (rn,rd) = Rat.quotient_of_rat r and (sn,sd) = Rat.quotient_of_rat s
    val m = lcms(map (abs o snd o Rat.quotient_of_rat) (r :: s :: map snd rlhs @ map snd rrhs))
    fun mult(t,r) =
        let val (i,j) = Rat.quotient_of_rat r
        in (t,i * (m div j)) end
in (m,(map mult rlhs, rn*(m div rd), rel, map mult rrhs, sn*(m div sd), d)) end

fun mklineq n atoms =
  fn (item, k) =>
  let val (m, (lhs,i,rel,rhs,j,discrete)) = integ item
      val lhsa = map (coeff lhs) atoms
      and rhsa = map (coeff rhs) atoms
      val diff = map2 (curry (op -)) rhsa lhsa
      val c = i-j
      val just = Asm k
      fun lineq(c,le,cs,j) = Lineq(c,le,cs, if m=1 then j else Multiplied2(m,j))
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
     | _     => sys_error("mklineq" ^ rel)
  end;

(* ------------------------------------------------------------------------- *)
(* Print (counter) example                                                   *)
(* ------------------------------------------------------------------------- *)

fun print_atom((a,d),r) =
  let val (p,q) = Rat.quotient_of_rat r
      val s = if d then IntInf.toString p else
              if p = 0 then "0"
              else IntInf.toString p ^ "/" ^ IntInf.toString q
  in a ^ " = " ^ s end;

fun produce_ex sds =
  curry (op ~~) sds
  #> map print_atom
  #> commas
  #> curry (op ^) "Counter example (possibly spurious):\n";

fun trace_ex (sg, params, atoms, discr, n, hist : history) =
  case hist of
    [] => ()
  | (v, lineqs) :: hist' =>
    let val frees = map Free params
        fun s_of_t t = Sign.string_of_term sg (subst_bounds (frees, t))
        val start = if v = ~1 then (hist', findex0 discr n lineqs)
          else (hist, replicate n Rat.zero)
        val ex = SOME (produce_ex ((map s_of_t atoms) ~~ discr)
          (uncurry (fold (findex1 discr)) start))
          handle NoEx => NONE
    in
      case ex of
        SOME s => (warning "arith failed - see trace for a counter example"; tracing s)
      | NONE => warning "arith failed"
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

fun split_items sg (do_pre : bool) (Ts, terms) :
                (typ list * (LA_Data.decompT * int) list) list =
let
  (* splits inequalities '~=' into '<' and '>'; this corresponds to *)
  (* 'REPEAT_DETERM (eresolve_tac neqE i)' at the theorem/tactic    *)
  (* level                                                          *)
  (* FIXME: this is currently sensitive to the order of theorems in *)
  (*        neqE:  The theorem for type "nat" must come first.  A   *)
  (*        better (i.e. less likely to break when neqE changes)    *)
  (*        implementation should *test* which theorem from neqE    *)
  (*        can be applied, and split the premise accordingly.      *)
  fun elim_neq (ineqs : (LA_Data.decompT option * bool) list) :
               (LA_Data.decompT option * bool) list list =
  let
    fun elim_neq' nat_only ([] : (LA_Data.decompT option * bool) list) :
                  (LA_Data.decompT option * bool) list list =
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
          |> map (elim_neq' false)
          |> List.concat
  end

  fun number_hyps _ []             = []
    | number_hyps n (NONE::xs)     = number_hyps (n+1) xs
    | number_hyps n ((SOME x)::xs) = (x, n) :: number_hyps (n+1) xs

  val result = (Ts, terms)
    |> (* user-defined preprocessing of the subgoal *)
       (if do_pre then LA_Data.pre_decomp sg else Library.single)
    |> (* produce the internal encoding of (in-)equalities *)
       map (apsnd (map (fn t => (LA_Data.decomp sg t, LA_Data.domain_is_nat t))))
    |> (* splitting of inequalities *)
       map (apsnd elim_neq)
    |> maps (fn (Ts, subgoals) => map (pair Ts o map fst) subgoals)
    |> (* numbering of hypotheses, ignoring irrelevant ones *)
       map (apsnd (number_hyps 0))
in result end;

fun add_atoms (ats : term list, ((lhs,_,_,rhs,_,_) : LA_Data.decompT, _)) : term list =
    (map fst lhs) union ((map fst rhs) union ats);

fun add_datoms (dats : (bool * term) list, ((lhs,_,_,rhs,_,d) : LA_Data.decompT, _)) :
  (bool * term) list =
  (map (pair d o fst) lhs) union ((map (pair d o fst) rhs) union dats);

fun discr (initems : (LA_Data.decompT * int) list) : bool list =
  map fst (Library.foldl add_datoms ([],initems));

fun refutes (sg : theory) (params : (string * typ) list) (show_ex : bool) :
  (typ list * (LA_Data.decompT * int) list) list -> injust list -> injust list option =
let
  fun refute ((Ts : typ list, initems : (LA_Data.decompT * int) list)::initemss)
             (js : injust list) : injust list option =
    let val atoms = Library.foldl add_atoms ([], initems)
        val n = length atoms
        val mkleq = mklineq n atoms
        val ixs = 0 upto (n-1)
        val iatoms = atoms ~~ ixs
        val natlineqs = List.mapPartial (mknat Ts ixs) iatoms
        val ineqs = map mkleq initems @ natlineqs
    in case elim (ineqs, []) of
         Success j =>
           (trace_msg ("Contradiction! (" ^ Int.toString (length js + 1) ^ ")");
            refute initemss (js@[j]))
       | Failure hist =>
           (if not show_ex then
              ()
            else let
              (* invent names for bound variables that are new, i.e. in Ts,  *)
              (* but not in params; we assume that Ts still contains (map    *)
              (* snd params) as a suffix                                     *)
              val new_count = length Ts - length params - 1
              val new_names = map Name.bound (0 upto new_count)
              val params'   = (new_names @ map fst params) ~~ Ts
            in
              trace_ex (sg, params', atoms, discr initems, n, hist)
            end; NONE)
    end
    | refute [] js = SOME js
in refute end;

fun refute (sg : theory) (params : (string * Term.typ) list) (show_ex : bool)
           (do_pre : bool) (terms : term list) : injust list option =
  refutes sg params show_ex (split_items sg do_pre (map snd params, terms)) [];

fun count P xs = length (filter P xs);

(* The limit on the number of ~= allowed.
   Because each ~= is split into two cases, this can lead to an explosion.
*)
val fast_arith_neq_limit = ref 9;

fun prove (sg : theory) (params : (string * Term.typ) list) (show_ex : bool)
          (do_pre : bool) (Hs : term list) (concl : term) : injust list option =
  let
    val _ = trace_msg "prove:"
    (* append the negated conclusion to 'Hs' -- this corresponds to     *)
    (* 'DETERM (resolve_tac [LA_Logic.notI, LA_Logic.ccontr] i)' at the *)
    (* theorem/tactic level                                             *)
    val Hs' = Hs @ [LA_Logic.neg_prop concl]
    fun is_neq NONE                 = false
      | is_neq (SOME (_,_,r,_,_,_)) = (r = "~=")
  in
    if count is_neq (map (LA_Data.decomp sg) Hs')
      > !fast_arith_neq_limit then (
      trace_msg ("fast_arith_neq_limit exceeded (current value is " ^
                   string_of_int (!fast_arith_neq_limit) ^ ")");
      NONE
    ) else
      refute sg params show_ex do_pre Hs'
  end handle TERM ("neg_prop", _) =>
    (* since no meta-logic negation is available, we can only fail if   *)
    (* the conclusion is not of the form 'Trueprop $ _' (simply         *)
    (* dropping the conclusion doesn't work either, because even        *)
    (* 'False' does not imply arbitrary 'concl::prop')                  *)
    (trace_msg "prove failed (cannot negate conclusion)."; NONE);

fun refute_tac ss (i, justs) =
  fn state =>
    let val _ = trace_thm ("refute_tac (on subgoal " ^ Int.toString i ^ ", with " ^
                             Int.toString (length justs) ^ " justification(s)):") state
        val sg          = theory_of_thm state
        val {neqE, ...} = Data.get sg
        fun just1 j =
          (* eliminate inequalities *)
          REPEAT_DETERM (eresolve_tac neqE i) THEN
            PRIMITIVE (trace_thm "State after neqE:") THEN
            (* use theorems generated from the actual justifications *)
            METAHYPS (fn asms => rtac (mkthm (sg, ss) asms j) 1) i
    in (* rewrite "[| A1; ...; An |] ==> B" to "[| A1; ...; An; ~B |] ==> False" *)
       DETERM (resolve_tac [LA_Logic.notI, LA_Logic.ccontr] i) THEN
       (* user-defined preprocessing of the subgoal *)
       DETERM (LA_Data.pre_tac i) THEN
       PRIMITIVE (trace_thm "State after pre_tac:") THEN
       (* prove every resulting subgoal, using its justification *)
       EVERY (map just1 justs)
    end  state;

(*
Fast but very incomplete decider. Only premises and conclusions
that are already (negated) (in)equations are taken into account.
*)
fun simpset_lin_arith_tac (ss : simpset) (show_ex : bool) (i : int) (st : thm) =
  SUBGOAL (fn (A,_) =>
  let val params = rev (Logic.strip_params A)
      val Hs     = Logic.strip_assums_hyp A
      val concl  = Logic.strip_assums_concl A
  in trace_thm ("Trying to refute subgoal " ^ string_of_int i) st;
     case prove (Thm.theory_of_thm st) params show_ex true Hs concl of
       NONE => (trace_msg "Refutation failed."; no_tac)
     | SOME js => (trace_msg "Refutation succeeded."; refute_tac ss (i, js))
  end) i st;

fun lin_arith_tac (show_ex : bool) (i : int) (st : thm) =
  simpset_lin_arith_tac
    (Simplifier.theory_context (Thm.theory_of_thm st) Simplifier.empty_ss)
    show_ex i st;

fun cut_lin_arith_tac (ss : simpset) (i : int) =
  cut_facts_tac (Simplifier.prems_of_ss ss) i THEN
  simpset_lin_arith_tac ss false i;

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

fun splitasms (sg : theory) (asms : thm list) : splittree =
let val {neqE, ...} = Data.get sg
    fun elim_neq (asms', []) = Tip (rev asms')
      | elim_neq (asms', asm::asms) =
      (case get_first (fn th => SOME (asm COMP th) handle THM _ => NONE) neqE of
        SOME spl =>
          let val (ct1, ct2) = extract (cprop_of spl)
              val thm1 = assume ct1
              val thm2 = assume ct2
          in Spl (spl, ct1, elim_neq (asms', asms@[thm1]), ct2, elim_neq (asms', asms@[thm2]))
          end
      | NONE => elim_neq (asm::asms', asms))
in elim_neq ([], asms) end;

fun fwdproof (ctxt : theory * simpset) (Tip asms : splittree) (j::js : injust list) =
    (mkthm ctxt asms j, js)
  | fwdproof ctxt (Spl (thm, ct1, tree1, ct2, tree2)) js =
    let val (thm1, js1) = fwdproof ctxt tree1 js
        val (thm2, js2) = fwdproof ctxt tree2 js1
        val thm1' = implies_intr ct1 thm1
        val thm2' = implies_intr ct2 thm2
    in (thm2' COMP (thm1' COMP thm), js2) end;
(* needs handle THM _ => NONE ? *)

fun prover (ctxt as (sg, ss)) thms (Tconcl : term) (js : injust list) (pos : bool) : thm option =
let
(* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv *)
(* Use this code instead if lin_arith_prover calls prove with do_pre set to true *)
(* but beware: this can be a significant performance issue.                      *)
    (* There is no "forward version" of 'pre_tac'.  Therefore we combine the     *)
    (* available theorems into a single proof state and perform "backward proof" *)
    (* using 'refute_tac'.                                                       *)
(*
    val Hs    = map prop_of thms
    val Prop  = fold (curry Logic.mk_implies) (rev Hs) Tconcl
    val cProp = cterm_of sg Prop
    val concl = Goal.init cProp
                  |> refute_tac ss (1, js)
                  |> Seq.hd
                  |> Goal.finish
                  |> fold (fn thA => fn thAB => implies_elim thAB thA) thms
*)
(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    val nTconcl       = LA_Logic.neg_prop Tconcl
    val cnTconcl      = cterm_of sg nTconcl
    val nTconclthm    = assume cnTconcl
    val tree          = splitasms sg (thms @ [nTconclthm])
    val (Falsethm, _) = fwdproof ctxt tree js
    val contr         = if pos then LA_Logic.ccontr else LA_Logic.notI
    val concl         = implies_intr cnTconcl Falsethm COMP contr
in SOME (trace_thm "Proved by lin. arith. prover:"
          (LA_Logic.mk_Eq concl)) end
(* in case concl contains ?-var, which makes assume fail: *)
handle THM _ => NONE;

(* PRE: concl is not negated!
   This assumption is OK because
   1. lin_arith_prover tries both to prove and disprove concl and
   2. lin_arith_prover is applied by the simplifier which
      dives into terms and will thus try the non-negated concl anyway.
*)

fun lin_arith_prover sg ss (concl : term) : thm option =
let val thms = List.concat (map LA_Logic.atomize (prems_of_ss ss));
    val Hs = map prop_of thms
    val Tconcl = LA_Logic.mk_Trueprop concl
(*
    val _ = trace_msg "lin_arith_prover"
    val _ = map (trace_thm "thms:") thms
    val _ = trace_msg ("concl:" ^ Sign.string_of_term sg concl)
*)
in case prove sg [] false false Hs Tconcl of (* concl provable? *)
     SOME js => prover (sg, ss) thms Tconcl js true
   | NONE => let val nTconcl = LA_Logic.neg_prop Tconcl
          in case prove sg [] false false Hs nTconcl of (* ~concl provable? *)
               SOME js => prover (sg, ss) thms nTconcl js false
             | NONE => NONE
          end
end;

end;
