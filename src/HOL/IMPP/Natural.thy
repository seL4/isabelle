(*  Title:      HOL/IMPP/Natural.thy
    ID:         $Id$
    Author:     David von Oheimb (based on a theory by Tobias Nipkow et al), TUM
    Copyright   1999 TUM
*)

header {* Natural semantics of commands *}

theory Natural
imports Com
begin

(** Execution of commands **)
consts
  evalc :: "(com * state *       state) set"
  evaln :: "(com * state * nat * state) set"

syntax
  "@evalc":: "[com,state,    state] => bool"  ("<_,_>/ -c-> _" [0,0,  51] 51)
  "@evaln":: "[com,state,nat,state] => bool"  ("<_,_>/ -_-> _" [0,0,0,51] 51)

translations
  "<c,s> -c-> s'" == "(c,s,  s') : evalc"
  "<c,s> -n-> s'" == "(c,s,n,s') : evaln"

consts
  newlocs :: locals
  setlocs :: "state => locals => state"
  getlocs :: "state => locals"
  update  :: "state => vname => val => state"     ("_/[_/::=/_]" [900,0,0] 900)
syntax (* IN Natural.thy *)
  loc :: "state => locals"    ("_<_>" [75,0] 75)
translations
  "s<X>" == "getlocs s X"

inductive evalc
  intros
    Skip:    "<SKIP,s> -c-> s"

    Assign:  "<X :== a,s> -c-> s[X::=a s]"

    Local:   "<c, s0[Loc Y::= a s0]> -c-> s1 ==>
              <LOCAL Y := a IN c, s0> -c-> s1[Loc Y::=s0<Y>]"

    Semi:    "[| <c0,s0> -c-> s1; <c1,s1> -c-> s2 |] ==>
              <c0;; c1, s0> -c-> s2"

    IfTrue:  "[| b s; <c0,s> -c-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -c-> s1"

    IfFalse: "[| ~b s; <c1,s> -c-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -c-> s1"

    WhileFalse: "~b s ==> <WHILE b DO c,s> -c-> s"

    WhileTrue:  "[| b s0;  <c,s0> -c-> s1;  <WHILE b DO c, s1> -c-> s2 |] ==>
                 <WHILE b DO c, s0> -c-> s2"

    Body:       "<the (body pn), s0> -c-> s1 ==>
                 <BODY pn, s0> -c-> s1"

    Call:       "<BODY pn, (setlocs s0 newlocs)[Loc Arg::=a s0]> -c-> s1 ==>
                 <X:=CALL pn(a), s0> -c-> (setlocs s1 (getlocs s0))
                                          [X::=s1<Res>]"

inductive evaln
  intros
    Skip:    "<SKIP,s> -n-> s"

    Assign:  "<X :== a,s> -n-> s[X::=a s]"

    Local:   "<c, s0[Loc Y::= a s0]> -n-> s1 ==>
              <LOCAL Y := a IN c, s0> -n-> s1[Loc Y::=s0<Y>]"

    Semi:    "[| <c0,s0> -n-> s1; <c1,s1> -n-> s2 |] ==>
              <c0;; c1, s0> -n-> s2"

    IfTrue:  "[| b s; <c0,s> -n-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -n-> s1"

    IfFalse: "[| ~b s; <c1,s> -n-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -n-> s1"

    WhileFalse: "~b s ==> <WHILE b DO c,s> -n-> s"

    WhileTrue:  "[| b s0;  <c,s0> -n-> s1;  <WHILE b DO c, s1> -n-> s2 |] ==>
                 <WHILE b DO c, s0> -n-> s2"

    Body:       "<the (body pn), s0> -    n-> s1 ==>
                 <BODY pn, s0> -Suc n-> s1"

    Call:       "<BODY pn, (setlocs s0 newlocs)[Loc Arg::=a s0]> -n-> s1 ==>
                 <X:=CALL pn(a), s0> -n-> (setlocs s1 (getlocs s0))
                                          [X::=s1<Res>]"


inductive_cases evalc_elim_cases:
  "<SKIP,s> -c-> t"  "<X:==a,s> -c-> t"  "<LOCAL Y:=a IN c,s> -c-> t"
  "<c1;;c2,s> -c-> t"  "<IF b THEN c1 ELSE c2,s> -c-> t"
  "<BODY P,s> -c-> s1"  "<X:=CALL P(a),s> -c-> s1"

inductive_cases evaln_elim_cases:
  "<SKIP,s> -n-> t"  "<X:==a,s> -n-> t"  "<LOCAL Y:=a IN c,s> -n-> t"
  "<c1;;c2,s> -n-> t"  "<IF b THEN c1 ELSE c2,s> -n-> t"
  "<BODY P,s> -n-> s1"  "<X:=CALL P(a),s> -n-> s1"

inductive_cases evalc_WHILE_case: "<WHILE b DO c,s> -c-> t"
inductive_cases evaln_WHILE_case: "<WHILE b DO c,s> -n-> t"

ML {* use_legacy_bindings (the_context ()) *}

end
