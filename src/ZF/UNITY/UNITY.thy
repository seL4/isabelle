(*  Title:      ZF/UNITY/UNITY.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

UNITY = State + UNITYMisc +
consts
  constrains :: "[i, i] => i"  (infixl "co"     60)
  op_unless  :: "[i, i] => i"  (infixl "unless" 60)

constdefs
   program  :: i 
  "program == {<init, acts, allowed>:condition*actionSet*actionSet.
	       Id:acts & Id:allowed}"

  mk_program :: [i,i,i]=>i 
  "mk_program(init, acts, allowed) ==
     <init Int state, cons(Id, acts Int action), cons(Id, allowed Int action)>"

  SKIP :: i
  "SKIP == mk_program(state, 0, action)"

  (** Coercion from anything to program **)
  programify :: i=>i
  "programify(F) == if F:program then F else SKIP"
  
  RawInit :: i=>i
  "RawInit(F) == fst(F)"
  
  Init :: i=>i
  "Init(F) == RawInit(programify(F))"

  RawActs :: i=>i
  "RawActs(F) == cons(Id, fst(snd(F)))"

  Acts :: i=>i
  "Acts(F) == RawActs(programify(F))"

  RawAllowedActs :: i=>i
  "RawAllowedActs(F) == cons(Id, snd(snd(F)))"

  AllowedActs :: i=>i
  "AllowedActs(F) == RawAllowedActs(programify(F))"

  
  Allowed :: i =>i
  "Allowed(F) == {G:program. Acts(G) <= AllowedActs(F)}"

  (* initially property, used by some UNITY authors *)
  initially   :: i => i
  "initially(A) == {F:program. Init(F)<= A & A:condition}"
  
  stable     :: i=>i
   "stable(A) == A co A"

  strongest_rhs :: [i, i] => i
  "strongest_rhs(F, A) == Inter({B:Pow(state). F:A co B})"

  invariant :: i => i
  "invariant(A) == {F:program. Init(F)<=A} Int stable(A)"

  part_order :: [i, i] => o
  "part_order(A, r) == refl(A,r) & trans[A](r) & antisym(r)"

  nat_order :: i
  "nat_order == {<i,j>:nat*nat. i le j}"
  
  (*
  The constant increasing_on defines the Charpentier's increasing notion.
  It should not be confused with the ZF's increasing constant
  which have a different meaning.
  Increasing_on's parameters: a state function f, a domain A and
  a order relation r over the domain A 
  Should f be a meta function instead ?
  *)
  increasing_on :: [i,i, i] => i  ("increasing[_]'(_,_')") 
  "increasing[A](f, r) ==
     {F:program. f:state->A & part_order(A,r) & F:
                       (INT z:A. stable({s:state.  <z, f`s>:r}))}"
   
defs
  (* The typing requirements `A:condition & B:condition'
     make the definition stronger than the original ones in HOL. *)

  constrains_def "A co B ==
		   {F:program. (ALL act:Acts(F). act``A <= B)
		    & A:condition & B:condition}"
  
  unless_def     "A unless B == (A - B) co (A Un B)"

end

