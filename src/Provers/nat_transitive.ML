(*  Title:      Provers/nat_transitive.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Munich
*)

(***
A very simple package for inequalities over nat.
It uses all premises of the form

t = u, t < u, t <= u, ~(t < u), ~(t <= u)

where t and u must be of type nat, to
1. either derive a constradiction,
   in which case the conclusion can be any term,
2. or prove the conclusion, which must be of the same form as the premises.

The package
- does not deal with the relation ~=
- treats `pred', +, *, ... as atomic terms. Hence it can prove
  [| x < y+z; y+z < u |] ==> Suc x < u
  but not
  [| x < y+z; z < u |] ==> Suc x < y+u
- takes only (in)equalities which are atomic premises into account. It does
  not deal with logical operators like -->, & etc. Hence it cannot prove 
  [| x < y+z & y+z < u |] ==> Suc x < u

In order not to fall foul of the above limitations, the following hints are
useful:

1. You may need to run `by(safe_tac HOL_cs)' in order to bring out the atomic
   premises.

2. To get rid of ~= in the premises, it is advisable to use a rule like
   nat_neqE = "[| (m::nat) ~= n; m < n ==> P; n < m ==> P |] ==> P" : thm
   (the name nat_eqE is chosen in HOL), for example as follows:
   by(safe_tac (HOL_cs addSEs [nat_neqE])

3. To get rid of `pred', you may be able to do the following:
   expand `pred(m)' into `case m of 0 => 0 | Suc n => n' and use split_tac
   to turn the case-expressions into logical case distinctions. In HOL:
   simp_tac (... addsimps [pred_def] setloop (split_tac [expand_nat_case]))

The basic tactic is `trans_tac'. In order to use `trans_tac' as a solver in
the simplifier, `cut_trans_tac' is also provided, which cuts the given thms
in as facts.

Notes:
- It should easily be possible to adapt this package to other numeric types
  like int.
- There is ample scope for optimizations, which so far have not proved
  necessary.
- The code can be simplified by adding the negated conclusion to the
  premises to derive a contradiction. However, this would restrict the
  package to classical logics.
***)

(* The package works for arbitrary logics.
   You just need to instantiate the following parameter structure.
*)
signature LESS_ARITH =
sig
  val lessI:            thm (* n < Suc n *)
  val zero_less_Suc:    thm (* 0 < Suc n *)
  val less_reflE:       thm (* n < n ==> P *)
  val less_zeroE:       thm (* n < 0 ==> P *)
  val less_incr:        thm (* m < n ==> Suc m < Suc n *)
  val less_decr:        thm (* Suc m < Suc n ==> m < n *)
  val less_incr_rhs:    thm (* m < n ==> m < Suc n *)
  val less_decr_lhs:    thm (* Suc m < n ==> m < n *)
  val less_trans_Suc:   thm (* [| i < j; j < k |] ==> Suc i < k *)
  val leD:              thm (* m <= n ==> m < Suc n *)
  val not_lessD:        thm (* ~(m < n) ==> n < Suc m *)
  val not_leD:          thm (* ~(m <= n) ==> n < m *)
  val eqD1:             thm (* m = n ==> m < Suc n *)
  val eqD2:             thm (* m = n ==> m < Suc n *)
  val not_lessI:        thm (* n < Suc m ==> ~(m < n) *)
  val leI:              thm (* m < Suc n ==> m <= n *)
  val not_leI:          thm (* n < m ==> ~(m <= n) *)
  val eqI:              thm (* [| m < Suc n; n < Suc m |] ==> n = m *)
  val is_zero: term -> bool
  val decomp:  term -> (term * int * string * term * int)option
(* decomp(`Suc^i(x) Rel Suc^j(y)') should yield (x,i,Rel,y,j)
   where Rel is one of "<", "~<", "<=", "~<=" and "=" *)
end;


signature TRANS_TAC =
sig
  val trans_tac: int -> tactic
  val cut_trans_tac: thm list -> int -> tactic
end;

functor Trans_Tac_Fun(Less:LESS_ARITH):TRANS_TAC =
struct

datatype proof = Asm of int
               | Thm of proof list * thm
               | Incr1 of proof * int (* Increment 1 side *)
               | Incr2 of proof * int (* Increment 2 sides *);


(*** Turn proof objects into thms ***)

fun incr2(th,i) = if i=0 then th else
                  if i>0 then incr2(th RS Less.less_incr,i-1)
                  else incr2(th RS Less.less_decr,i+1);

fun incr1(th,i) = if i=0 then th else
                  if i>0 then incr1(th RS Less.less_incr_rhs,i-1)
                  else incr1(th RS Less.less_decr_lhs,i+1);

fun prove asms =
  let fun pr(Asm i) = nth_elem(i,asms)
        | pr(Thm(prfs,thm)) = (map pr prfs) MRS thm
        | pr(Incr1(p,i)) = incr1(pr p,i)
        | pr(Incr2(p,i)) = incr2(pr p,i)
  in pr end;

(*** Internal representation of inequalities
(x,i,y,j) means x+i < y+j.
Leads to simpler case distinctions than the normalized x < y+k
***)
type less = term * int * term * int * proof;

(*** raised when contradiction is found ***)
exception Contr of proof;

(*** raised when goal can't be proved ***)
exception Cant;

infix subsumes;

fun (x,i,y,j:int,_) subsumes (x',i',y',j',_) =
  x=x' andalso y=y' andalso j-i<=j'-i';

fun trivial(x,i:int,y,j,_)  =  (x=y orelse Less.is_zero(x)) andalso i<j;

(*** transitive closure ***)

(* Very naive: computes all consequences of a set of less-statements. *)
(* In the worst case very expensive not just in time but also space *)
(* Could easily be optimized but there are ususally only a few < asms *)

fun add new =
  let fun adds([],news) = new::news
        | adds(old::olds,news) = if new subsumes old then adds(olds,news)
                                 else adds(olds,old::news)
  in adds end;

fun ctest(less as (x,i,y,j,p)) =
  if x=y andalso i>=j
  then raise Contr(Thm([Incr1(Incr2(p,~j),j-i)],Less.less_reflE)) else
  if Less.is_zero(y) andalso i>=j
  then raise Contr(Thm([Incr2(p,~j)],Less.less_zeroE))
  else less;

fun mktrans((x,i,_,j,p):less,(_,k,z,l,q)) =
  ctest(if j >= k
        then (x,i+1,z,l+(j-k),Thm([p,Incr2(q,j-k)],Less.less_trans_Suc))
        else (x,i+(k-j)+1,z,l,Thm([Incr2(p,k-j),q],Less.less_trans_Suc)));

fun trans (new as (x,i,y,j,p)) olds =
  let fun tr(news, old as (x1,i1,y1,j1,p1):less) =
           if y1=x then mktrans(old,new)::news else
           if x1=y then mktrans(new,old)::news else news
  in foldl tr ([],olds) end;

fun close1(olds: less list)(new:less):less list =
      if trivial new orelse exists (fn old => old subsumes new) olds then olds
      else let val news = trans new olds
           in  close (add new (olds,[])) news end
and close (olds: less list) ([]:less list) = olds
  | close olds ((new:less)::news) = close (close1 olds (ctest new)) news;

(*** end of transitive closure ***)

(* recognize and solve trivial goal *)
fun triv_sol(x,i,y,j,_) =
  if x=y andalso i<j
  then Some(Incr1(Incr2(Thm([],Less.lessI),i),j-i)) else
  if Less.is_zero(x) andalso i<j
  then Some(Incr1(Incr2(Thm([],Less.zero_less_Suc),i),j-i-1))
  else None;

(* solve less starting from facts *)
fun solve facts (less as (x,i,y,j,_)) =
  case triv_sol less of
    None => (case find_first (fn fact => fact subsumes less) facts of
               None => raise Cant
             | Some(a,m,b,n,p) => Incr1(Incr2(p,j-n),n+i-m-j))
  | Some prf => prf;

(* turn term into a less-tuple *)
fun mkasm(t,n) =
  case Less.decomp(t) of
    Some(x,i,rel,y,j) => (case rel of
      "<"   => [(x,i,y,j,Asm n)]
    | "~<"  => [(y,j,x,i+1,Thm([Asm n],Less.not_lessD))]
    | "<="  => [(x,i,y,j+1,Thm([Asm n],Less.leD))]
    | "~<=" => [(y,j,x,i,Thm([Asm n],Less.not_leD))]
    | "="   => [(x,i,y,j+1,Thm([Asm n],Less.eqD1)),
                (y,j,x,i+1,Thm([Asm n],Less.eqD2))]
    | "~="  => []
    | _     => error("trans_tac/decomp: unknown relation " ^ rel))
  | None => [];

(* mkconcl t returns a pair (goals,proof) where goals is a list of *)
(* less-subgoals to solve, and proof the validation which proves the concl t *)
(* from the subgoals. Asm ~1 is dummy *)
fun mkconcl t =
  case Less.decomp(t) of
    Some(x,i,rel,y,j) => (case rel of
      "<"   => ([(x,i,y,j,Asm ~1)],Asm 0)
    | "~<"  => ([(y,j,x,i+1,Asm ~1)],Thm([Asm 0],Less.not_lessI))
    | "<="  => ([(x,i,y,j+1,Asm ~1)],Thm([Asm 0],Less.leI))
    | "~<=" => ([(y,j,x,i,Asm ~1)],Thm([Asm 0],Less.not_leI))
    | "="   => ([(x,i,y,j+1,Asm ~1),(y,j,x,i+1,Asm ~1)],
                Thm([Asm 0,Asm 1],Less.eqI))
    | "~="  => raise Cant
    | _     => error("trans_tac/decomp: unknown relation " ^ rel))
  | None => raise Cant;


val trans_tac = SUBGOAL (fn (A,n) =>
  let val Hs = Logic.strip_assums_hyp A
      val C = Logic.strip_assums_concl A
      val lesss = flat(map mkasm (Hs ~~ (0 upto (length Hs - 1))));
      val clesss = close [] lesss
      val (subgoals,prf) = mkconcl C
      val prfs = map (solve clesss) subgoals
  in METAHYPS (fn asms => let val thms = map (prove asms) prfs
                          in rtac (prove thms prf) 1 end) n
  end
  handle Contr(p) => METAHYPS (fn asms => rtac (prove asms p) 1) n
       | Cant => no_tac);

fun cut_trans_tac thms = cut_facts_tac thms THEN' trans_tac;

end;

(*** Tests
fun test s = prove_goal Nat.thy ("!!m::nat." ^ s) (fn _ => [trans_tac 1]);

test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l) |] ==> Suc(Suc i) < m";
test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l) |] ==> Suc(Suc(Suc i)) <= m";
test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l) |] ==> ~ m <= Suc(Suc i)";
test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l) |] ==> ~ m < Suc(Suc(Suc i))";
test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l); m <= Suc(Suc(Suc i)) |] \
\     ==> m = Suc(Suc(Suc i))";
test "[| i<j; j<=k; ~(l < Suc k); ~(m <= l); m=n; n <= Suc(Suc(Suc i)) |] \
\     ==> m = Suc(Suc(Suc i))";
***)
