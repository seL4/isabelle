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
  val add_mono_thms:    thm list ref
                            (* [| i rel1 j; m rel2 n |] ==> i + m rel3 j + n *)
  val lessD:            thm list ref (* m < n ==> m+1 <= n *)
  val decomp:
    term ->
      ((term * int)list * int * string * (term * int)list * int * bool)option
  val simp: (thm -> thm) ref
end;
(*
decomp(`x Rel y') should yield (p,i,Rel,q,j,d)
   where Rel is one of "<", "~<", "<=", "~<=" and "=" and
         p/q is the decomposition of the sum terms x/y into a list
         of summand * multiplicity pairs and a constant summand and
         d indicates if the domain is discrete.

simp must reduce contradictory <= to False.
   It should also cancel common summands to keep <= reduced;
   otherwise <= can grow to massive proportions.
*)

signature FAST_LIN_ARITH =
sig
  val lin_arith_prover: Sign.sg -> thm list -> term -> thm option
  val     lin_arith_tac:             int -> tactic
  val cut_lin_arith_tac: thm list -> int -> tactic
end;

functor Fast_Lin_Arith(structure LA_Logic:LIN_ARITH_LOGIC 
                       and       LA_Data:LIN_ARITH_DATA) : FAST_LIN_ARITH =
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
                | LessD of injust
                | NotLessD of injust
                | NotLeD of injust
                | NotLeDD of injust
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


fun print_ineqs ineqs =
 writeln(cat_lines(""::map (fn Lineq(c,t,l,_) =>
   string_of_int c ^
   (case t of Eq => " =  " | Lt=> " <  " | Le => " <= ") ^
   commas(map string_of_int l)) ineqs));


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
fun mkthm sg asms just =
  let val atoms = foldl (fn (ats,(lhs,_,_,rhs,_,_)) =>
                            map fst lhs  union  (map fst rhs  union  ats))
                        ([], mapfilter (LA_Data.decomp o concl_of) asms)

      fun addthms thm1 thm2 =
        let val conj = thm1 RS (thm2 RS LA_Logic.conjI)
        in the(get_first (fn th => Some(conj RS th) handle _ => None)
                         (!LA_Data.add_mono_thms))
        end;

      fun multn(n,thm) =
        let fun mul(i,th) = if i=1 then th else mul(i-1, addthms thm th)
        in if n < 0 then mul(~n,thm) RS LA_Logic.sym else mul(n,thm) end;

      fun simp thm =
        let val thm' = !LA_Data.simp thm
        in if LA_Logic.is_False thm' then raise FalseE thm' else thm' end

      fun mk(Asm i) = ((*writeln"Asm";prth*)(nth_elem(i,asms)))
        | mk(Nat(i)) = ((*writeln"N";LA_Logic.mk_nat_thm sg (nth_elem(i,atoms)))
        | mk(LessD(j)) = ((*writeln"L";prth*)(hd([mk j] RL !LA_Data.lessD)))
        | mk(NotLeD(j)) = ((*writeln"NLe";prth*)(mk j RS LA_Logic.not_leD))
        | mk(NotLeDD(j)) = ((*writeln"NLeD";prth*)(hd([mk j RS LA_Logic.not_leD] RL !LA_Data.lessD)))
        | mk(NotLessD(j)) = ((*writeln"NL";prth*)(mk j RS LA_Logic.not_lessD))
        | mk(Added(j1,j2)) = ((*writeln"+";prth*)(simp(prth(addthms (mk j1) (mk j2)))))
        | mk(Multiplied(n,j)) = ((*writeln"*";multn(n,mk j))

  in (*writeln"mkthm";*)!LA_Data.simp(mk just) handle FalseE thm => thm end
end;

fun coeff poly atom = case assoc(poly,atom) of None => 0 | Some i => i;

fun mklineq atoms =
  let val n = length atoms in
    fn ((lhs,i,rel,rhs,j,discrete),k) =>
    let val lhsa = map (coeff lhs) atoms
        and rhsa = map (coeff rhs) atoms
        val diff = map2 (op -) (rhsa,lhsa)
        val c = i-j
        val just = Asm k
    in case rel of
        "<="   => Some(Lineq(c,Le,diff,just))
       | "~<=" => if discrete
                  then Some(Lineq(1-c,Le,map (op ~) diff,NotLeDD(just)))
                  else Some(Lineq(~c,Lt,map (op ~) diff,NotLeD(just)))
       | "<"   => if discrete
                  then Some(Lineq(c+1,Le,diff,LessD(just)))
                  else Some(Lineq(c,Lt,diff,just))
       | "~<"  => Some(Lineq(~c,Le,map (op~) diff,NotLessD(just)))
       | "="   => Some(Lineq(c,Eq,diff,just))
       | "~="  => None
       | _     => sys_error("mklineq" ^ rel)   
    end
  end;

fun mknat pTs ixs (atom,i) =
  if LA_Logic.is_nat(pTs,atom)
  then let val l = map (fn j => if j=i then 1 else 0) ixs
       in Some(Lineq(0,Le,l,Nat(i))) end
  else None

fun abstract pTs items =
  let val atoms = foldl (fn (ats,((lhs,_,_,rhs,_,_),_)) =>
                            (map fst lhs) union ((map fst rhs) union ats))
                        ([],items)
      val ixs = 0 upto (length(atoms)-1)
      val iatoms = atoms ~~ ixs
  in mapfilter (mklineq atoms) items @ mapfilter (mknat pTs ixs) iatoms end;

(* Ordinary refutation *)
fun refute1(pTs,items) =
  (case elim (abstract pTs items) of
       None => []
     | Some(Lineq(_,_,_,j)) => [j]);

fun refute1_tac(i,just) =
  fn state =>
    let val sg = #sign(rep_thm state)
    in resolve_tac [LA_Logic.notI,LA_Logic.ccontr] i THEN
       METAHYPS (fn asms => rtac (mkthm sg asms just) 1) i
    end
    state;

(* Double refutation caused by equality in conclusion *)
fun refute2(pTs,items, (rhs,i,_,lhs,j,d), nHs) =
  (case elim (abstract pTs (items@[((rhs,i,"<",lhs,j,d),nHs)])) of
    None => []
  | Some(Lineq(_,_,_,j1)) =>
      (case elim (abstract pTs (items@[((lhs,j,"<",rhs,i,d),nHs)])) of
        None => []
      | Some(Lineq(_,_,_,j2)) => [j1,j2]));

fun refute2_tac(i,just1,just2) =
  fn state => 
    let val sg = #sign(rep_thm state)
    in rtac LA_Logic.ccontr i THEN rotate_tac ~1 i THEN etac LA_Logic.neqE i THEN
       METAHYPS (fn asms => rtac (mkthm sg asms just1) 1) i THEN
       METAHYPS (fn asms => rtac (mkthm sg asms just2) 1) i
    end
    state;

fun prove(pTs,Hs,concl) =
let val nHs = length Hs
    val ixHs = Hs ~~ (0 upto (nHs-1))
    val Hitems = mapfilter (fn (h,i) => case LA_Data.decomp h of
                                 None => None | Some(it) => Some(it,i)) ixHs
in case LA_Data.decomp concl of
     None => if null Hitems then [] else refute1(pTs,Hitems)
   | Some(citem as (r,i,rel,l,j,d)) =>
       if rel = "="
       then refute2(pTs,Hitems,citem,nHs)
       else let val neg::rel0 = explode rel
                val nrel = if neg = "~" then implode rel0 else "~"^rel
            in refute1(pTs, Hitems@[((r,i,nrel,l,j,d),nHs)]) end
end;

(*
Fast but very incomplete decider. Only premises and conclusions
that are already (negated) (in)equations are taken into account.
*)
val lin_arith_tac = SUBGOAL (fn (A,n) =>
  let val pTs = rev(map snd (Logic.strip_params A))
      val Hs = Logic.strip_assums_hyp A
      val concl = Logic.strip_assums_concl A
  in case prove(pTs,Hs,concl) of
       [j] => refute1_tac(n,j)
     | [j1,j2] => refute2_tac(n,j1,j2)
     | _ => no_tac
  end);

fun cut_lin_arith_tac thms i = cut_facts_tac thms i THEN lin_arith_tac i;

fun prover1(just,sg,thms,concl,pos) =
let val nconcl = LA_Logic.neg_prop concl
    val cnconcl = cterm_of sg nconcl
    val Fthm = mkthm sg (thms @ [assume cnconcl]) just
    val contr = if pos then LA_Logic.ccontr else LA_Logic.notI
in Some(LA_Logic.mk_Eq ((implies_intr cnconcl Fthm) COMP contr)) end
handle _ => None;

(* handle thm with equality conclusion *)
fun prover2(just1,just2,sg,thms,concl) =
let val nconcl = LA_Logic.neg_prop concl (* m ~= n *)
    val cnconcl = cterm_of sg nconcl
    val neqthm = assume cnconcl
    val casethm = neqthm COMP LA_Logic.neqE (* [|m<n ==> R; n<m ==> R|] ==> R *)
    val [lessimp1,lessimp2] = prems_of casethm
    val less1 = fst(Logic.dest_implies lessimp1) (* m<n *)
    and less2 = fst(Logic.dest_implies lessimp2) (* n<m *)
    val cless1 = cterm_of sg less1 and cless2 = cterm_of sg less2
    val thm1 = mkthm sg (thms @ [assume cless1]) just1
    and thm2 = mkthm sg (thms @ [assume cless2]) just2
    val dthm1 = implies_intr cless1 thm1 and dthm2 = implies_intr cless2 thm2
    val thm = dthm2 COMP (dthm1 COMP casethm)
in Some(LA_Logic.mk_Eq ((implies_intr cnconcl thm) COMP LA_Logic.ccontr)) end
handle _ => None;

(* PRE: concl is not negated! *)
fun lin_arith_prover sg thms concl =
let val Hs = map (#prop o rep_thm) thms
    val Tconcl = LA_Logic.mk_Trueprop concl
in case prove([],Hs,Tconcl) of
     [j] => prover1(j,sg,thms,Tconcl,true)
   | [j1,j2] => prover2(j1,j2,sg,thms,Tconcl)
   | _ => let val nTconcl = LA_Logic.neg_prop Tconcl
          in case prove([],Hs,nTconcl) of
               [j] => prover1(j,sg,thms,nTconcl,false)
               (* [_,_] impossible because of negation *)
             | _ => None
          end
end;

end;
