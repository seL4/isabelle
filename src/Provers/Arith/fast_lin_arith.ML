(*  Title:      Provers/Arith/fast_lin_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998  TU Munich

A generic linear arithmetic package.
It provides two tactics

    lin_arith_tac:         int -> tactic
cut_lin_arith_tac: thms -> int -> tactic

and a simplification procedure

    lin_arith_prover: Sign.sg -> thm list -> term -> thm option

Only take premises and conclusions into account that are already (negated)
(in)equations. lin_arith_prover tries to prove or disprove the term.
*)

(* Debugging: set Fast_Arith.trace *)

(*** Data needed for setting up the linear arithmetic package ***)

signature LIN_ARITH_LOGIC =
sig
  val conjI:		thm
  val ccontr:           thm (* (~ P ==> False) ==> P *)
  val neqE:             thm (* [| m ~= n; m < n ==> P; n < m ==> P |] ==> P *)
  val notI:             thm (* (P ==> False) ==> ~ P *)
  val not_lessD:        thm (* ~(m < n) ==> n <= m *)
  val not_leD:          thm (* ~(m <= n) ==> n < m *)
  val sym:		thm (* x = y ==> y = x *)
  val mk_Eq: thm -> thm
  val mk_Trueprop: term -> term
  val neg_prop: term -> term
  val is_False: thm -> bool
  val is_nat: typ list * term -> bool
  val mk_nat_thm: Sign.sg -> term -> thm
end;
(*
mk_Eq(~in) = `in == False'
mk_Eq(in) = `in == True'
where `in' is an (in)equality.

neg_prop(t) = neg if t is wrapped up in Trueprop and
  nt is the (logically) negated version of t, where the negation
  of a negative term is the term itself (no double negation!);

is_nat(parameter-types,t) =  t:nat
mk_nat_thm(t) = "0 <= t"
*)

signature LIN_ARITH_DATA =
sig
  val decomp:
    Sign.sg -> term -> ((term*rat)list * rat * string * (term*rat)list * rat * bool)option
  val number_of: int * typ -> term
end;
(*
decomp(`x Rel y') should yield (p,i,Rel,q,j,d)
   where Rel is one of "<", "~<", "<=", "~<=" and "=" and
         p/q is the decomposition of the sum terms x/y into a list
         of summand * multiplicity pairs and a constant summand and
         d indicates if the domain is discrete.

ss must reduce contradictory <= to False.
   It should also cancel common summands to keep <= reduced;
   otherwise <= can grow to massive proportions.
*)

signature FAST_LIN_ARITH =
sig
  val setup: (theory -> theory) list
  val map_data: ({add_mono_thms: thm list, mult_mono_thms: (thm*cterm)list, inj_thms: thm list,
                 lessD: thm list, simpset: Simplifier.simpset}
                 -> {add_mono_thms: thm list, mult_mono_thms: (thm*cterm)list, inj_thms: thm list,
                     lessD: thm list, simpset: Simplifier.simpset})
                -> theory -> theory
  val trace           : bool ref
  val lin_arith_prover: Sign.sg -> thm list -> term -> thm option
  val     lin_arith_tac:     bool -> int -> tactic
  val cut_lin_arith_tac: thm list -> int -> tactic
end;

functor Fast_Lin_Arith(structure LA_Logic:LIN_ARITH_LOGIC 
                       and       LA_Data:LIN_ARITH_DATA) : FAST_LIN_ARITH =
struct


(** theory data **)

(* data kind 'Provers/fast_lin_arith' *)

structure DataArgs =
struct
  val name = "Provers/fast_lin_arith";
  type T = {add_mono_thms: thm list, mult_mono_thms: (thm*cterm)list, inj_thms: thm list,
            lessD: thm list, simpset: Simplifier.simpset};

  val empty = {add_mono_thms = [], mult_mono_thms = [], inj_thms = [],
               lessD = [], simpset = Simplifier.empty_ss};
  val copy = I;
  val prep_ext = I;

  fun merge ({add_mono_thms= add_mono_thms1, mult_mono_thms= mult_mono_thms1, inj_thms= inj_thms1,
              lessD = lessD1, simpset = simpset1},
             {add_mono_thms= add_mono_thms2, mult_mono_thms= mult_mono_thms2, inj_thms= inj_thms2,
              lessD = lessD2, simpset = simpset2}) =
    {add_mono_thms = Drule.merge_rules (add_mono_thms1, add_mono_thms2),
     mult_mono_thms = gen_merge_lists' (Drule.eq_thm_prop o pairself fst)
       mult_mono_thms1 mult_mono_thms2,
     inj_thms = Drule.merge_rules (inj_thms1, inj_thms2),
     lessD = Drule.merge_rules (lessD1, lessD2),
     simpset = Simplifier.merge_ss (simpset1, simpset2)};

  fun print _ _ = ();
end;

structure Data = TheoryDataFun(DataArgs);
val map_data = Data.map;
val setup = [Data.init];



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
                | Multiplied of int * injust
                | Multiplied2 of int * injust
                | Added of injust * injust;

datatype lineq = Lineq of int * lineq_type * int list * injust;

fun el 0 (h::_) = h
  | el n (_::t) = el (n - 1) t
  | el _ _  = sys_error "el";

(* ------------------------------------------------------------------------- *)
(* Finding a (counter) example from the trace of a failed elimination        *)
(* ------------------------------------------------------------------------- *)
(* Examples are represented as rational numbers,                             *)
(* although at the moment all examples are rounded to integers -             *)
(* thus it does not yet work for type real.                                  *)
(* Dont blame John Harrison for this code - it is entirely mine. TN          *)

exception NoEx;
exception NotYetImpl;

fun elim_eqns(ineqs,Lineq(i,Le,cs,_)) = (i,cs)::ineqs
  | elim_eqns(ineqs,Lineq(i,Eq,cs,_)) = (i,cs)::(~i,map ~ cs)::ineqs
  | elim_eqns(ineqs,Lineq(i,Lt,cs,_)) = raise NotYetImpl;

val rat0 = rat_of_int 0;

(* PRE: ex[v] must be 0! *)
fun eval (ex:rat list) v (a:int,cs:int list) =
  let val rs = map rat_of_int cs
      val rsum = foldl ratadd (rat0,map ratmul (rs ~~ ex))
  in ratmul(ratadd(rat_of_int a,ratneg rsum), ratinv(el v rs)) end;

(*
fun ratge0(Rat(a,p,q)) = (p = 0 orelse a)
*)
fun ratge0 r = fst(rep_rat r) >= 0;
fun ratle(r,s) = ratge0(ratadd(s,ratneg r))

fun ratmin2(r,s) = if ratle(r,s) then r else s;
fun ratmax2(r,s) = if ratle(r,s) then s else r;

val ratmin = foldr1 ratmin2;
val ratmax = foldr1 ratmax2;

fun ratroundup r = let val (p,q) = rep_rat r
                   in if q=1 then r else rat_of_int((p div q) + 1) end

fun ratrounddown r = let val (p,q) = rep_rat r
                     in if q=1 then r else rat_of_int((p div q) - 1) end

fun choose2 d (lb,ub) =
  if ratle(lb,rat0) andalso ratle(rat0,ub) then rat0 else
  if not d then (if ratge0 lb then lb else ub) else
  if ratge0 lb then let val lb' = ratroundup lb
                    in if ratle(lb',ub) then lb' else raise NoEx end
               else let val ub' = ratrounddown ub
                    in if ratle(lb,ub') then ub' else raise NoEx end;

fun findex1 discr (ex,(v,lineqs)) =
  let val nz = filter (fn (Lineq(_,_,cs,_)) => el v cs <> 0) lineqs;
      val ineqs = foldl elim_eqns ([],nz)
      val (ge,le) = partition (fn (_,cs) => el v cs > 0) ineqs
      val lb = ratmax(map (eval ex v) ge)
      val ub = ratmin(map (eval ex v) le)
  in nth_update (choose2 (nth_elem(v,discr)) (lb,ub)) (v,ex) end;

fun findex discr = foldl (findex1 discr);

fun elim1 v x =
  map (fn (a,bs) => (ratadd(a,ratneg(ratmul(el v bs,x))),
                     nth_update rat0 (v,bs)));

fun single_var v cs = (filter_out (equal rat0) cs = [el v cs]);

(* The base case:
   all variables occur only with positive or only with negative coefficients *)
fun pick_vars discr (ineqs,ex) =
  let val nz = filter_out (forall (equal rat0) o snd) ineqs
  in if null nz then ex
     else let val v = find_index (not o equal rat0) (snd(hd nz))
              val d = nth_elem(v,discr)
              val sv = filter (single_var v o snd) nz
              val minmax = if ratge0(el v (snd(hd nz)))
                           then if d then ratroundup o ratmax else ratmax
                           else if d then ratrounddown o ratmin else ratmin
              val bnds = map (fn (a,bs) => ratmul(a,ratinv(el v bs))) sv
              val x = minmax(rat0::bnds)
              val ineqs' = elim1 v x nz
              val ex' = nth_update x (v,ex)
          in pick_vars discr (ineqs',ex') end
  end;

fun findex0 discr n lineqs =
  let val ineqs = foldl elim_eqns ([],lineqs)
      val rineqs = map (fn (a,cs) => (rat_of_int a, map rat_of_int cs)) ineqs
  in pick_vars discr (rineqs,replicate n rat0) end;

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
  else Lineq(n * k,ty,map (apl(n,op * )) l,Multiplied(n,just));

(* ------------------------------------------------------------------------- *)
(* Add together (in)equations.                                               *)
(* ------------------------------------------------------------------------- *)

fun add_ineq (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val l = map2 (op +) (l1,l2)
  in Lineq(k1+k2,find_add_type(ty1,ty2),l,Added(just1,just2)) end;

(* ------------------------------------------------------------------------- *)
(* Elimination of variable between a single pair of (in)equations.           *)
(* If they're both inequalities, 1st coefficient must be +ve, 2nd -ve.       *)
(* ------------------------------------------------------------------------- *)

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val c1 = el v l1 and c2 = el v l2
      val m = lcm(abs c1,abs c2)
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

fun calc_blowup l =
  let val (p,n) = partition (apl(0,op<)) (filter (apl(0,op<>)) l)
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
  flat(map (fn x => map (fn y => f x y) ys) xs);

fun extract_first p =
  let fun extract xs (y::ys) = if p y then (Some y,xs@ys)
                               else extract (y::xs) ys
        | extract xs []      = (None,xs)
  in extract [] end;

fun print_ineqs ineqs =
  if !trace then
     tracing(cat_lines(""::map (fn Lineq(c,t,l,_) =>
       string_of_int c ^
       (case t of Eq => " =  " | Lt=> " <  " | Le => " <= ") ^
       commas(map string_of_int l)) ineqs))
  else ();

type history = (int * lineq list) list;
datatype result = Success of injust | Failure of history;

fun elim(ineqs,hist) =
  let val dummy = print_ineqs ineqs;
      val (triv,nontriv) = partition is_trivial ineqs in
  if not(null triv)
  then case Library.find_first is_answer triv of
         None => elim(nontriv,hist)
       | Some(Lineq(_,_,_,j)) => Success j
  else
  if null nontriv then Failure(hist)
  else
  let val (eqs,noneqs) = partition (fn (Lineq(_,ty,_,_)) => ty=Eq) nontriv in
  if not(null eqs) then
     let val clist = foldl (fn (cs,Lineq(_,_,l,_)) => l union cs) ([],eqs)
         val sclist = sort (fn (x,y) => int_ord(abs(x),abs(y)))
                           (filter (fn i => i<>0) clist)
         val c = hd sclist
         val (Some(eq as Lineq(_,_,ceq,_)),othereqs) =
               extract_first (fn Lineq(_,_,l,_) => c mem l) eqs
         val v = find_index_eq c ceq
         val (ioth,roth) = partition (fn (Lineq(_,_,l,_)) => el v l = 0)
                                     (othereqs @ noneqs)
         val others = map (elim_var v eq) roth @ ioth
     in elim(others,(v,nontriv)::hist) end
  else
  let val lists = map (fn (Lineq(_,_,l,_)) => l) noneqs
      val numlist = 0 upto (length(hd lists) - 1)
      val coeffs = map (fn i => map (el i) lists) numlist
      val blows = map calc_blowup coeffs
      val iblows = blows ~~ numlist
      val nziblows = filter (fn (i,_) => i<>0) iblows
  in if null nziblows then Failure((~1,nontriv)::hist)
     else
     let val (c,v) = hd(sort (fn (x,y) => int_ord(fst(x),fst(y))) nziblows)
         val (no,yes) = partition (fn (Lineq(_,_,l,_)) => el v l = 0) ineqs
         val (pos,neg) = partition(fn (Lineq(_,_,l,_)) => el v l > 0) yes
     in elim(no @ allpairs (elim_var v) pos neg, (v,nontriv)::hist) end
  end
  end
  end;

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

fun trace_thm msg th = 
    if !trace then (tracing msg; tracing (Display.string_of_thm th); th) else th;

fun trace_msg msg = 
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
fun mkthm sg asms just =
  let val {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} = Data.get_sg sg;
      val atoms = foldl (fn (ats,(lhs,_,_,rhs,_,_)) =>
                            map fst lhs  union  (map fst rhs  union  ats))
                        ([], mapfilter (fn thm => if Thm.no_prems thm
                                        then LA_Data.decomp sg (concl_of thm)
                                        else None) asms)

      fun add2 thm1 thm2 =
        let val conj = thm1 RS (thm2 RS LA_Logic.conjI)
        in get_first (fn th => Some(conj RS th) handle _ => None) add_mono_thms
        end;

      fun try_add [] _ = None
        | try_add (thm1::thm1s) thm2 = case add2 thm1 thm2 of
             None => try_add thm1s thm2 | some => some;

      fun addthms thm1 thm2 =
        case add2 thm1 thm2 of
          None => (case try_add ([thm1] RL inj_thms) thm2 of
                     None => ( the(try_add ([thm2] RL inj_thms) thm1)
                               handle OPTION =>
                               (trace_thm "" thm1; trace_thm "" thm2;
                                sys_error "Lin.arith. failed to add thms")
                             )
                   | Some thm => thm)
        | Some thm => thm;

      fun multn(n,thm) =
        let fun mul(i,th) = if i=1 then th else mul(i-1, addthms thm th)
        in if n < 0 then mul(~n,thm) RS LA_Logic.sym else mul(n,thm) end;

      fun multn2(n,thm) =
        let val Some(mth,cv) =
              get_first (fn (th,cv) => Some(thm RS th,cv) handle _ => None) mult_mono_thms
            val ct = cterm_of sg (LA_Data.number_of(n,#T(rep_cterm cv)))
        in instantiate ([],[(cv,ct)]) mth end

      fun simp thm =
        let val thm' = trace_thm "Simplified:" (full_simplify simpset thm)
        in if LA_Logic.is_False thm' then raise FalseE thm' else thm' end

      fun mk(Asm i) = trace_thm "Asm" (nth_elem(i,asms))
        | mk(Nat i) = (trace_msg "Nat"; LA_Logic.mk_nat_thm sg (nth_elem(i,atoms)))
        | mk(LessD(j)) = trace_thm "L" (hd([mk j] RL lessD))
        | mk(NotLeD(j)) = trace_thm "NLe" (mk j RS LA_Logic.not_leD)
        | mk(NotLeDD(j)) = trace_thm "NLeD" (hd([mk j RS LA_Logic.not_leD] RL lessD))
        | mk(NotLessD(j)) = trace_thm "NL" (mk j RS LA_Logic.not_lessD)
        | mk(Added(j1,j2)) = simp (trace_thm "+" (addthms (mk j1) (mk j2)))
        | mk(Multiplied(n,j)) = (trace_msg("*"^string_of_int n); trace_thm "*" (multn(n,mk j)))
        | mk(Multiplied2(n,j)) = simp (trace_msg("**"^string_of_int n); trace_thm "**" (multn2(n,mk j)))

  in trace_msg "mkthm";
     let val thm = trace_thm "Final thm:" (mk just)
     in let val fls = simplify simpset thm
        in trace_thm "After simplification:" fls;
           if LA_Logic.is_False fls then fls
           else
            (tracing "Assumptions:"; seq print_thm asms;
             tracing "Proved:"; print_thm fls;
             warning "Linear arithmetic should have refuted the assumptions.\n\
                     \Please inform Tobias Nipkow (nipkow@in.tum.de).";
             fls)
        end
     end handle FalseE thm => (trace_thm "False reached early:" thm; thm)
  end
end;

fun coeff poly atom = case assoc(poly,atom) of None => 0 | Some i => i;

fun lcms is = foldl lcm (1,is);

fun integ(rlhs,r,rel,rrhs,s,d) =
let val (rn,rd) = rep_rat r and (sn,sd) = rep_rat s
    val m = lcms(map (abs o snd o rep_rat) (r :: s :: map snd rlhs @ map snd rrhs))
    fun mult(t,r) = let val (i,j) = rep_rat r in (t,i * (m div j)) end
in (m,(map mult rlhs, rn*(m div rd), rel, map mult rrhs, sn*(m div sd), d)) end

fun mklineq n atoms =
  fn (item,k) =>
  let val (m,(lhs,i,rel,rhs,j,discrete)) = integ item
      val lhsa = map (coeff lhs) atoms
      and rhsa = map (coeff rhs) atoms
      val diff = map2 (op -) (rhsa,lhsa)
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
  let val (p,q) = rep_rat r
      val s = if d then string_of_int p else
              if p = 0 then "0"
              else string_of_int p ^ "/" ^ string_of_int q
  in a ^ " = " ^ s end;

fun print_ex sds =
  tracing o
  apl("Counter example:\n",op ^) o
  commas o
  map print_atom o
  apl(sds, op ~~);

fun trace_ex(sg,params,atoms,discr,n,hist:history) =
  if null hist then ()
  else let val frees = map Free params;
           fun s_of_t t = Sign.string_of_term sg (subst_bounds(frees,t));
           val (v,lineqs) :: hist' = hist
           val start = if v = ~1 then (findex0 discr n lineqs,hist')
                       else (replicate n rat0,hist)
       in warning "arith failed - see trace for a counter example";
          print_ex ((map s_of_t atoms)~~discr) (findex discr start)
          handle NoEx =>
  (tracing "The decision procedure failed to prove your proposition\n\
           \but could not construct a counter example either.\n\
           \Probably the proposition is true but cannot be proved\n\
           \by the incomplete decision procedure.")
       end
       handle NotYetImpl =>
 tracing "No counter example: < on real not yet implemented.";

fun mknat pTs ixs (atom,i) =
  if LA_Logic.is_nat(pTs,atom)
  then let val l = map (fn j => if j=i then 1 else 0) ixs
       in Some(Lineq(0,Le,l,Nat(i))) end
  else None

(* This code is tricky. It takes a list of premises in the order they occur
in the subgoal. Numerical premises are coded as Some(tuple), non-numerical
ones as None. Going through the premises, each numeric one is converted into
a Lineq. The tricky bit is to convert ~= which is split into two cases < and
>. Thus split_items returns a list of equation systems. This may blow up if
there are many ~=, but in practice it does not seem to happen. The really
tricky bit is to arrange the order of the cases such that they coincide with
the order in which the cases are in the end generated by the tactic that
applies the generated refutation thms (see function 'refute_tac').

For variables n of type nat, a constraint 0 <= n is added.
*)
fun split_items(items) =
  let fun elim_neq front _ [] = [rev front]
        | elim_neq front n (None::ineqs) = elim_neq front (n+1) ineqs
        | elim_neq front n (Some(ineq as (l,i,rel,r,j,d))::ineqs) =
          if rel = "~=" then elim_neq front n (ineqs @ [Some(l,i,"<",r,j,d)]) @
                             elim_neq front n (ineqs @ [Some(r,j,"<",l,i,d)])
          else elim_neq ((ineq,n) :: front) (n+1) ineqs
  in elim_neq [] 0 items end;

fun add_atoms(ats,((lhs,_,_,rhs,_,_),_)) =
    (map fst lhs) union ((map fst rhs) union ats)

fun add_datoms(dats,((lhs,_,_,rhs,_,d),_)) =
    (map (pair d o fst) lhs) union ((map (pair d o fst) rhs) union dats)

fun discr initems = map fst (foldl add_datoms ([],initems));

fun refutes sg (pTs,params) ex =
let
  fun refute (initems::initemss) js =
    let val atoms = foldl add_atoms ([],initems)
        val n = length atoms
        val mkleq = mklineq n atoms
        val ixs = 0 upto (n-1)
        val iatoms = atoms ~~ ixs
        val natlineqs = mapfilter (mknat pTs ixs) iatoms
        val ineqs = map mkleq initems @ natlineqs
    in case elim(ineqs,[]) of
         Success(j) =>
           (trace_msg "Contradiction!"; refute initemss (js@[j]))
       | Failure(hist) =>
           (if not ex then ()
            else trace_ex(sg,params,atoms,discr initems,n,hist);
            None)
    end
    | refute [] js = Some js
in refute end;

fun refute sg ps ex items = refutes sg ps ex (split_items items) [];

fun refute_tac(i,justs) =
  fn state =>
    let val sg = #sign(rep_thm state)
        fun just1 j = REPEAT_DETERM(etac LA_Logic.neqE i) THEN
                      METAHYPS (fn asms => rtac (mkthm sg asms j) 1) i
    in DETERM(resolve_tac [LA_Logic.notI,LA_Logic.ccontr] i) THEN
       EVERY(map just1 justs)
    end
    state;

fun prove sg ps ex Hs concl =
let val Hitems = map (LA_Data.decomp sg) Hs
in case LA_Data.decomp sg concl of
     None => refute sg ps ex (Hitems@[None])
   | Some(citem as (r,i,rel,l,j,d)) =>
       let val neg::rel0 = explode rel
           val nrel = if neg = "~" then implode rel0 else "~"^rel
       in refute sg ps ex (Hitems @ [Some(r,i,nrel,l,j,d)]) end
end;

(*
Fast but very incomplete decider. Only premises and conclusions
that are already (negated) (in)equations are taken into account.
*)
fun lin_arith_tac ex i st = SUBGOAL (fn (A,_) =>
  let val params = rev(Logic.strip_params A)
      val pTs = map snd params
      val Hs = Logic.strip_assums_hyp A
      val concl = Logic.strip_assums_concl A
  in trace_thm ("Trying to refute subgoal " ^ string_of_int i) st;
     case prove (Thm.sign_of_thm st) (pTs,params) ex Hs concl of
       None => (trace_msg "Refutation failed."; no_tac)
     | Some js => (trace_msg "Refutation succeeded."; refute_tac(i,js))
  end) i st;

fun cut_lin_arith_tac thms i = cut_facts_tac thms i THEN lin_arith_tac false i;

(** Forward proof from theorems **)

(* More tricky code. Needs to arrange the proofs of the multiple cases (due
to splits of ~= premises) such that it coincides with the order of the cases
generated by function split_items. *)

datatype splittree = Tip of thm list
                   | Spl of thm * cterm * splittree * cterm * splittree

fun extract imp =
let val (Il,r) = Thm.dest_comb imp
    val (_,imp1) = Thm.dest_comb Il
    val (Ict1,_) = Thm.dest_comb imp1
    val (_,ct1) = Thm.dest_comb Ict1
    val (Ir,_) = Thm.dest_comb r
    val (_,Ict2r) = Thm.dest_comb Ir
    val (Ict2,_) = Thm.dest_comb Ict2r
    val (_,ct2) = Thm.dest_comb Ict2
in (ct1,ct2) end;

fun splitasms asms =
let fun split(asms',[]) = Tip(rev asms')
      | split(asms',asm::asms) =
      let val spl = asm COMP LA_Logic.neqE
          val (ct1,ct2) = extract(cprop_of spl)
          val thm1 = assume ct1 and thm2 = assume ct2
      in Spl(spl,ct1,split(asms',asms@[thm1]),ct2,split(asms',asms@[thm2])) end
      handle THM _ => split(asm::asms', asms)
in split([],asms) end;

fun fwdproof sg (Tip asms) (j::js) = (mkthm sg asms j, js)
  | fwdproof sg (Spl(thm,ct1,tree1,ct2,tree2)) js =
    let val (thm1,js1) = fwdproof sg tree1 js
        val (thm2,js2) = fwdproof sg tree2 js1
        val thm1' = implies_intr ct1 thm1
        val thm2' = implies_intr ct2 thm2
    in (thm2' COMP (thm1' COMP thm), js2) end;
(* needs handle _ => None ? *)

fun prover sg thms Tconcl js pos =
let val nTconcl = LA_Logic.neg_prop Tconcl
    val cnTconcl = cterm_of sg nTconcl
    val nTconclthm = assume cnTconcl
    val tree = splitasms (thms @ [nTconclthm])
    val (thm,_) = fwdproof sg tree js
    val contr = if pos then LA_Logic.ccontr else LA_Logic.notI
in Some(LA_Logic.mk_Eq((implies_intr cnTconcl thm) COMP contr)) end
(* in case concl contains ?-var, which makes assume fail: *)
handle THM _ => None;

(* PRE: concl is not negated!
   This assumption is OK because
   1. lin_arith_prover tries both to prove and disprove concl and
   2. lin_arith_prover is applied by the simplifier which
      dives into terms and will thus try the non-negated concl anyway.
*)
fun lin_arith_prover sg thms concl =
let val Hs = map (#prop o rep_thm) thms
    val Tconcl = LA_Logic.mk_Trueprop concl
in case prove sg ([],[]) false Hs Tconcl of (* concl provable? *)
     Some js => prover sg thms Tconcl js true
   | None => let val nTconcl = LA_Logic.neg_prop Tconcl
          in case prove sg ([],[]) false Hs nTconcl of (* ~concl provable? *)
               Some js => prover sg thms nTconcl js false
             | None => None
          end
end;

end;
