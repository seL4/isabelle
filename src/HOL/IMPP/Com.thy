(*  Title:    HOL/IMPP/Com.thy
    Author:   David von Oheimb (based on a theory by Tobias Nipkow et al), TUM
*)

section \<open>Semantics of arithmetic and boolean expressions, Syntax of commands\<close>

theory Com
imports Main
begin

type_synonym val = nat
  (* for the meta theory, this may be anything, but types cannot be refined later *)

typedecl glb
typedecl loc

axiomatization
  Arg :: loc and
  Res :: loc

datatype vname  = Glb glb | Loc loc
type_synonym globs = "glb => val"
type_synonym locals = "loc => val"
datatype state  = st globs locals
(* for the meta theory, the following would be sufficient:
typedecl state
consts   st :: "[globs , locals] => state"
*)
type_synonym aexp = "state => val"
type_synonym bexp = "state => bool"

typedecl pname

datatype com
      = SKIP
      | Ass   vname aexp        (\<open>_:==_\<close>                [65, 65    ] 60)
      | Local loc aexp com      (\<open>LOCAL _:=_ IN _\<close>      [65,  0, 61] 60)
      | Semi  com  com          (\<open>_;; _\<close>                [59, 60    ] 59)
      | Cond  bexp com com      (\<open>IF _ THEN _ ELSE _\<close>   [65, 60, 61] 60)
      | While bexp com          (\<open>WHILE _ DO _\<close>         [65,     61] 60)
      | BODY  pname
      | Call  vname pname aexp  (\<open>_:=CALL _'(_')\<close>       [65, 65,  0] 60)

consts bodies :: "(pname  *  com) list"(* finitely many procedure definitions *)
definition
  body :: " pname \<rightharpoonup> com" where
  "body = map_of bodies"


(* Well-typedness: all procedures called must exist *)

inductive WT  :: "com => bool" where

    Skip:    "WT SKIP"

  | Assign:  "WT (X :== a)"

  | Local:   "WT c ==>
              WT (LOCAL Y := a IN c)"

  | Semi:    "[| WT c0; WT c1 |] ==>
              WT (c0;; c1)"

  | If:      "[| WT c0; WT c1 |] ==>
              WT (IF b THEN c0 ELSE c1)"

  | While:   "WT c ==>
              WT (WHILE b DO c)"

  | Body:    "body pn ~= None ==>
              WT (BODY pn)"

  | Call:    "WT (BODY pn) ==>
              WT (X:=CALL pn(a))"

inductive_cases WTs_elim_cases:
  "WT SKIP"  "WT (X:==a)"  "WT (LOCAL Y:=a IN c)"
  "WT (c1;;c2)"  "WT (IF b THEN c1 ELSE c2)"  "WT (WHILE b DO c)"
  "WT (BODY P)"  "WT (X:=CALL P(a))"

definition
  WT_bodies :: bool where
  "WT_bodies = (\<forall>(pn,b) \<in> set bodies. WT b)"


ML \<open>
  fun make_imp_tac ctxt =
    EVERY' [resolve_tac ctxt [mp], fn i => assume_tac ctxt (i + 1), eresolve_tac ctxt [thin_rl]]
\<close>

lemma finite_dom_body: "finite (dom body)"
apply (unfold body_def)
apply (rule finite_dom_map_of)
done

lemma WT_bodiesD: "[| WT_bodies; body pn = Some b |] ==> WT b"
apply (unfold WT_bodies_def body_def)
apply (drule map_of_SomeD)
apply fast
done

declare WTs_elim_cases [elim!]

end
