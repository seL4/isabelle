(*  Title:      ZF/UNITY/UNITY.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

UNITY = State +
consts
  constrains :: "[i, i] => i"  (infixl "co"     60)
  op_unless  :: "[i, i] => i"  (infixl "unless" 60)

constdefs
   program  :: i 
  "program == {<init, acts, allowed>:
	       Pow(state)*Pow(Pow(state*state))*Pow(Pow(state*state)).
	       id(state):acts & id(state):allowed}"

  (* The definition below yields a program thanks to the coercions
  init Int state, acts Int Pow(state*state), etc. *)
  mk_program :: [i,i,i]=>i 
  "mk_program(init, acts, allowed) ==
    <init Int state, cons(id(state), acts Int Pow(state*state)),
              cons(id(state), allowed Int Pow(state*state))>"

  SKIP :: i
  "SKIP == mk_program(state, 0, Pow(state*state))"

  (* Coercion from anything to program *)
  programify :: i=>i
  "programify(F) == if F:program then F else SKIP"

  RawInit :: i=>i
  "RawInit(F) == fst(F)"
  
  Init :: i=>i
  "Init(F) == RawInit(programify(F))"

  RawActs :: i=>i
  "RawActs(F) == cons(id(state), fst(snd(F)))"

  Acts :: i=>i
  "Acts(F) == RawActs(programify(F))"

  RawAllowedActs :: i=>i
  "RawAllowedActs(F) == cons(id(state), snd(snd(F)))"

  AllowedActs :: i=>i
  "AllowedActs(F) == RawAllowedActs(programify(F))"

  
  Allowed :: i =>i
  "Allowed(F) == {G:program. Acts(G) <= AllowedActs(F)}"

  initially :: i=>i
  "initially(A) == {F:program. Init(F)<=A}"
  
  stable     :: i=>i
   "stable(A) == A co A"

  strongest_rhs :: [i, i] => i
  "strongest_rhs(F, A) == Inter({B:Pow(state). F:A co B})"

  invariant :: i => i
  "invariant(A) == initially(A) Int stable(A)"
    
  (* The `increasing' relation of Charpentier. Increasing's parameters are:
   a state function f, a domain A and an order relation r over the domain A. *)
  
  increasing :: [i,i, i] => i 
  "increasing(A, r, f) ==  INT a:A. stable({s:state.  <a, f`s>:r})"

  (* The definition of a partial order in ZF (predicate part_ord in theory Order)
     describes a strict order: irreflexive and transitive.
     However, the order used in association with Charpentier's increasing
     relation is not, hence the definition below: *)
  part_order :: [i, i] => o
  "part_order(A, r) == refl(A,r) & trans[A](r) & antisym(r)"

defs
  (* Condition `st_set(A)' makes the definition slightly stronger than the HOL one *)
  constrains_def "A co B == {F:program. (ALL act:Acts(F). act``A<=B) & st_set(A)}"
  unless_def     "A unless B == (A - B) co (A Un B)"
end

