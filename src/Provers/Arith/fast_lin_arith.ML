(*  Title:      Provers/Arith/fast_lin_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998  TU Munich

A generic linear arithmetic package.
The two tactics provided:
    lin_arith_tac:         int -> tactic
cut_lin_arith_tac: thms -> int -> tactic
Only take premises and conclusions into account
that are already (negated) (in)equations.
*)

(*** Data needed for setting up the linear arithmetic package ***)

signature LIN_ARITH_DATA =
sig
  val add_mono_thms:    thm list
                            (* [| i rel1 j; m rel2 n |] ==> i + m rel3 j + n *)
  val conjI:		thm
  val ccontr:           thm (* (~ P ==> False) ==> P *)
  val lessD:            thm (* m < n ==> Suc m <= n *)
  val neqE:             thm (* [| m ~= n; m < n ==> P; n < m ==> P |] ==> P *)
  val notI:             thm (* (P ==> False) ==> ~ P *)
  val not_leD:          thm (* ~(m <= n) ==> Suc n <= m *)
  val not_lessD:        thm (* ~(m < n) ==> n < m *)
  val sym:		thm (* x = y ==> y = x *)
  val decomp: term ->
             ((term * int)list * int * string * (term * int)list * int)option
  val simp: thm -> thm
  val is_False: thm -> bool
  val is_nat: typ list * term -> bool
  val mk_nat_thm: Sign.sg -> term -> thm
end;
(*
decomp(`x Rel y') should yield (p,i,Rel,q,j)
   where Rel is one of "<", "~<", "<=", "~<=" and "=" and
         p/q is the decomposition of the sum terms x/y into a list
         of summand * multiplicity pairs and a constant summand.

simp must reduce contradictory <= to False.
   It should also cancel common summands to keep <= reduced;
   otherwise <= can grow to massive proportions.

is_nat(parameter-types,t) =  t:nat
mk_nat_thm(t) = "0 <= t"
*)

signature FAST_LIN_ARITH =
sig
  val     lin_arith_tac:             int -> tactic
  val cut_lin_arith_tac: thm list -> int -> tactic
end;

functor Fast_Lin_Arith(LA_Data:LIN_ARITH_DATA):FAST_LIN_ARITH =
struct

(*** A fast decision procedure ***)
(*** Code ported from HOL Light ***)
(* possible optimizations:
   use (var,coeff) rep or vector rep  tp save space;
   treat non-negative atoms separately rather than adding 0 <= atom
*)

datatype lineq_type = Eq | Le | Lt;

datatype injust = Asm of int
                | Nat of int (* index of atom *)
                | Fwd of injust * thm
                | Multiplied of int * injust
                | Added of injust * injust;

datatype lineq = Lineq of int * lineq_type * int list * injust;

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

fun gcd x y =
  let fun gxd x y =
    if y = 0 then x else gxd y (x mod y)
  in if x < y then gxd y x else gxd x y end;

fun lcm x y = (x * y) div gcd x y;

fun el 0 (h::_) = h
  | el n (_::t) = el (n - 1) t
  | el _ _  = sys_error "el";

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let val c1 = el v l1 and c2 = el v l2
      val m = lcm (abs c1) (abs c2)
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

(*
fun print_ineqs ineqs =
 writeln(cat_lines(""::map (fn Lineq(c,t,l,_) =>
   string_of_int c ^
   (case t of Eq => " =  " | Lt=> " <  " | Le => " <= ") ^
   commas(map string_of_int l)) ineqs));
*)

fun elim ineqs =
  let (*val dummy = print_ineqs ineqs;*)
      val (triv,nontriv) = partition is_trivial ineqs in
  if not(null triv)
  then case find_first is_answer triv of
         None => elim nontriv | some => some
  else
  if null nontriv then None else
  let val (eqs,noneqs) = partition (fn (Lineq(_,ty,_,_)) => ty=Eq) nontriv in
  if not(null eqs) then
     let val clist = foldl (fn (cs,Lineq(_,_,l,_)) => l union cs) ([],eqs)
         val sclist = sort (fn (x,y) => int_ord(abs(x),abs(y)))
                           (filter (fn i => i<>0) clist)
         val c = hd sclist
         val (Some(eq as Lineq(_,_,ceq,_)),othereqs) =
               extract_first (fn Lineq(_,_,l,_) => c mem l) eqs
         val v = find_index (fn k => k=c) ceq
         val (ioth,roth) = partition (fn (Lineq(_,_,l,_)) => el v l = 0)
                                     (othereqs @ noneqs)
         val others = map (elim_var v eq) roth @ ioth
     in elim others end
  else
  let val lists = map (fn (Lineq(_,_,l,_)) => l) noneqs
      val numlist = 0 upto (length(hd lists) - 1)
      val coeffs = map (fn i => map (el i) lists) numlist
      val blows = map calc_blowup coeffs
      val iblows = blows ~~ numlist
      val nziblows = filter (fn (i,_) => i<>0) iblows
  in if null nziblows then None else
     let val (c,v) = hd(sort (fn (x,y) => int_ord(fst(x),fst(y))) nziblows)
         val (no,yes) = partition (fn (Lineq(_,_,l,_)) => el v l = 0) ineqs
         val (pos,neg) = partition(fn (Lineq(_,_,l,_)) => el v l > 0) yes
     in elim (no @ allpairs (elim_var v) pos neg) end
  end
  end
  end;

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

(* FIXME OPTIMIZE!!!!
   Addition/Multiplication need i*t representation rather than t+t+...

Simplification may detect a contradiction 'prematurely' due to type
information: n+1 <= 0 is simplified to False and does not need to be crossed
with 0 <= n.
*)
local
 exception FalseE of thm
in
fun mkproof sg asms just =
  let val atoms = foldl (fn (ats,(lhs,_,_,rhs,_)) =>
                            map fst lhs  union  (map fst rhs  union  ats))
                        ([], mapfilter (LA_Data.decomp o concl_of) asms)

      fun addthms thm1 thm2 =
        let val conj = thm1 RS (thm2 RS LA_Data.conjI)
        in the(get_first (fn th => Some(conj RS th) handle _ => None)
                         LA_Data.add_mono_thms)
        end;

      fun multn(n,thm) =
        let fun mul(i,th) = if i=1 then th else mul(i-1, addthms thm th)
        in if n < 0 then mul(~n,thm) RS LA_Data.sym else mul(n,thm) end;

      fun simp thm =
        let val thm' = LA_Data.simp thm
        in if LA_Data.is_False thm' then raise FalseE thm' else thm' end

      fun mk(Asm i) = nth_elem(i,asms)
        | mk(Nat(i)) = LA_Data.mk_nat_thm sg (nth_elem(i,atoms))
        | mk(Fwd(j,thm)) = mk j RS thm
        | mk(Added(j1,j2)) = simp(addthms (mk j1) (mk j2))
        | mk(Multiplied(n,j)) = multn(n,mk j)

  in LA_Data.simp(mk just) handle FalseE thm => thm end
end;

fun coeff poly atom = case assoc(poly,atom) of None => 0 | Some i => i;

fun mklineq atoms =
  let val n = length atoms in
    fn ((lhs,i,rel,rhs,j),k) =>
    let val lhsa = map (coeff lhs) atoms
        and rhsa = map (coeff rhs) atoms
        val diff = map2 (op -) (rhsa,lhsa)
        val c = i-j
        val just = Asm k
    in case rel of
        "<="   => Some(Lineq(c,Le,diff,just))
       | "~<=" => Some(Lineq(1-c,Le,map (op ~) diff,Fwd(just,LA_Data.not_leD)))
       | "<"   => Some(Lineq(c+1,Le,diff,Fwd(just,LA_Data.lessD)))
       | "~<"  => Some(Lineq(~c,Le,map (op~) diff,Fwd(just,LA_Data.not_lessD)))
       | "="   => Some(Lineq(c,Eq,diff,just))
       | "~="  => None
       | _     => sys_error("mklineq" ^ rel)   
    end
  end;

fun mknat pTs ixs (atom,i) =
  if LA_Data.is_nat(pTs,atom)
  then let val l = map (fn j => if j=i then 1 else 0) ixs
       in Some(Lineq(0,Le,l,Nat(i))) end
  else None

fun abstract pTs items =
  let val atoms = foldl (fn (ats,((lhs,_,_,rhs,_),_)) =>
                            (map fst lhs) union ((map fst rhs) union ats))
                        ([],items)
      val ixs = 0 upto (length(atoms)-1)
      val iatoms = atoms ~~ ixs
  in mapfilter (mklineq atoms) items @ mapfilter (mknat pTs ixs) iatoms end;

(* Ordinary refutation *)
fun refute1_tac pTs items =
  let val lineqs = abstract pTs items
  in case elim lineqs of
       None => K no_tac
     | Some(Lineq(_,_,_,j)) =>
         fn i => fn state => 
         let val sg = #sign(rep_thm state)
         in resolve_tac [LA_Data.notI,LA_Data.ccontr] i THEN
            METAHYPS (fn asms => rtac (mkproof sg asms j) 1) i
         end state
  end;

(* Double refutation caused by equality in conclusion *)
fun refute2_tac pTs items (rhs,i,_,lhs,j) nHs =
  (case elim (abstract pTs (items@[((rhs,i,"<",lhs,j),nHs)])) of
    None => K no_tac
  | Some(Lineq(_,_,_,j1)) =>
      (case elim (abstract pTs (items@[((lhs,j,"<",rhs,i),nHs)])) of
        None => K no_tac
      | Some(Lineq(_,_,_,j2)) =>
          fn i => fn state => 
          let val sg = #sign(rep_thm state)
          in rtac LA_Data.ccontr i THEN etac LA_Data.neqE i THEN
             METAHYPS (fn asms => rtac (mkproof sg asms j1) 1) i THEN
             METAHYPS (fn asms => rtac (mkproof sg asms j2) 1) i
          end state));

(*
Fast but very incomplete decider. Only premises and conclusions
that are already (negated) (in)equations are taken into account.
*)
val lin_arith_tac = SUBGOAL (fn (A,n) =>
  let val pTs = rev(map snd (Logic.strip_params A))
      val Hs = Logic.strip_assums_hyp A
      val nHs = length Hs
      val His = Hs ~~ (0 upto (nHs-1))
      val Hitems = mapfilter (fn (h,i) => case LA_Data.decomp h of
                                 None => None | Some(it) => Some(it,i)) His
  in case LA_Data.decomp(Logic.strip_assums_concl A) of
       None => if null Hitems then no_tac else refute1_tac pTs Hitems n
     | Some(citem as (r,i,rel,l,j)) =>
         if rel = "="
         then refute2_tac pTs Hitems citem nHs n
         else let val neg::rel0 = explode rel
                  val nrel = if neg = "~" then implode rel0 else "~"^rel
              in refute1_tac pTs (Hitems@[((r,i,nrel,l,j),nHs)]) n end
  end);

fun cut_lin_arith_tac thms i = cut_facts_tac thms i THEN lin_arith_tac i;

end;
