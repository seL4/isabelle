(*  Title:      HOL/IMPP/Hoare.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM

Inductive definition of Hoare logic for partial correctness
Completeness is taken relative to completeness of the underlying logic
Two versions of completeness proof:
  nested single recursion vs. simultaneous recursion in call rule
*)

Hoare = Natural + 

types 'a assn = "'a => state => bool"
translations
      "a assn"   <= (type)"a => state => bool"

constdefs
  state_not_singleton :: bool
 "state_not_singleton == ? s t::state. s ~= t" (* at least two elements *)

  peek_and    :: "'a assn => (state => bool) => 'a assn" (infixr "&>" 35)
 "peek_and P p == %Z s. P Z s & p s"

datatype 'a triple =
    triple ('a assn) com ('a assn)         ("{(1_)}./ (_)/ .{(1_)}" [3,60,3] 58)
  
consts
  triple_valid ::            nat => 'a triple     => bool ( "|=_:_" [0 , 58] 57)
  hoare_valids ::  'a triple set => 'a triple set => bool ("_||=_"  [58, 58] 57)
  hoare_derivs ::"('a triple set *  'a triple set)   set"
syntax
  triples_valid::            nat => 'a triple set => bool ("||=_:_" [0 , 58] 57)
  hoare_valid  ::  'a triple set => 'a triple     => bool ("_|=_"   [58, 58] 57)
"@hoare_derivs"::  'a triple set => 'a triple set => bool ("_||-_"  [58, 58] 57)
"@hoare_deriv" ::  'a triple set => 'a triple     => bool ("_|-_"   [58, 58] 57)

defs triple_valid_def  "|=n:t  ==  case t of {P}.c.{Q} =>
		                !Z s. P Z s --> (!s'. <c,s> -n-> s' --> Q Z s')"
translations          "||=n:G" == "Ball G (triple_valid n)"
defs hoare_valids_def"G||=ts   ==  !n. ||=n:G --> ||=n:ts"
translations         "G |=t  " == " G||={t}"
                     "G||-ts"  == "(G,ts) : hoare_derivs"
                     "G |-t"   == " G||-{t}"

(* Most General Triples *)
constdefs MGT    :: com => state triple              ("{=}._.{->}" [60] 58)
         "{=}.c.{->} == {%Z s0. Z = s0}. c .{%Z s1. <c,Z> -c-> s1}"

inductive hoare_derivs intrs
  
  empty    "G||-{}"
  insert"[| G |-t;  G||-ts |]
	==> G||-insert t ts"

  asm	   "ts <= G ==>
	    G||-ts" (* {P}.BODY pn.{Q} instead of (general) t for SkipD_lemma *)

  cut   "[| G'||-ts; G||-G' |] ==> G||-ts" (* for convenience and efficiency *)

  weaken"[| G||-ts' ; ts <= ts' |] ==> G||-ts"

  conseq"!Z s. P  Z  s --> (? P' Q'. G|-{P'}.c.{Q'} &
                                  (!s'. (!Z'. P' Z' s --> Q' Z' s') --> Q Z s'))
         ==> G|-{P}.c.{Q}"


  Skip	"G|-{P}. SKIP .{P}"

  Ass	"G|-{%Z s. P Z (s[X::=a s])}. X:==a .{P}"

  Local	"G|-{P}. c .{%Z s. Q Z (s[Loc X::=s'<X>])}
     ==> G|-{%Z s. s'=s & P Z (s[Loc X::=a s])}. LOCAL X:=a IN c .{Q}"

  Comp	"[| G|-{P}.c.{Q};
	    G|-{Q}.d.{R} |]
	==> G|-{P}. (c;;d) .{R}"

  If	"[| G|-{P &>        b }.c.{Q};
	    G|-{P &> (Not o b)}.d.{Q} |]
	==> G|-{P}. IF b THEN c ELSE d .{Q}"

  Loop  "G|-{P &> b}.c.{P} ==>
	 G|-{P}. WHILE b DO c .{P &> (Not o b)}"

(*
  BodyN	"(insert ({P}. BODY pn  .{Q}) G)
	  |-{P}.  the (body pn) .{Q} ==>
	 G|-{P}.       BODY pn  .{Q}"
*)
  Body	"[| G Un (%p. {P p}.      BODY p  .{Q p})``Procs
	      ||-(%p. {P p}. the (body p) .{Q p})``Procs |]
	==>  G||-(%p. {P p}.      BODY p  .{Q p})``Procs"

  Call	   "G|-{P}. BODY pn .{%Z s. Q Z (setlocs s (getlocs s')[X::=s<Res>])}
	==> G|-{%Z s. s'=s & P Z (setlocs s newlocs[Loc Arg::=a s])}.
	    X:=CALL pn(a) .{Q}"

end
