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
    
  (* meta-function composition *)
  comp :: "[i=>i, i=>i] => (i=>i)" (infixl 65)
  "f comp g == %x. f(g(x))"

  pg_compl :: "i=>i"
  "pg_compl(X)== program - X"
    
defs
  (* Condition `st_set(A)' makes the definition slightly stronger than the HOL one *)
  constrains_def "A co B == {F:program. (ALL act:Acts(F). act``A<=B) & st_set(A)}"
  unless_def     "A unless B == (A - B) co (A Un B)"
end

