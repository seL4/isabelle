(*  Title:      HOL/IMPP/Natural.thy
    Author:     David von Oheimb (based on a theory by Tobias Nipkow et al), TUM
*)

section \<open>Natural semantics of commands\<close>

theory Natural
imports Com
begin

(** Execution of commands **)

consts
  newlocs :: locals
  setlocs :: "state => locals => state"
  getlocs :: "state => locals"
  update  :: "state => vname => val => state"     (\<open>_/[_/::=/_]\<close> [900,0,0] 900)

abbreviation
  loc :: "state => locals"  (\<open>_<_>\<close> [75,0] 75) where
  "s<X> == getlocs s X"

inductive
  evalc :: "[com,state,    state] => bool"  (\<open><_,_>/ -c-> _\<close> [0,0,  51] 51)
  where
    Skip:    "<SKIP,s> -c-> s"

  | Assign:  "<X :== a,s> -c-> s[X::=a s]"

  | Local:   "<c, s0[Loc Y::= a s0]> -c-> s1 ==>
              <LOCAL Y := a IN c, s0> -c-> s1[Loc Y::=s0<Y>]"

  | Semi:    "[| <c0,s0> -c-> s1; <c1,s1> -c-> s2 |] ==>
              <c0;; c1, s0> -c-> s2"

  | IfTrue:  "[| b s; <c0,s> -c-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -c-> s1"

  | IfFalse: "[| ~b s; <c1,s> -c-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -c-> s1"

  | WhileFalse: "~b s ==> <WHILE b DO c,s> -c-> s"

  | WhileTrue:  "[| b s0;  <c,s0> -c-> s1;  <WHILE b DO c, s1> -c-> s2 |] ==>
                 <WHILE b DO c, s0> -c-> s2"

  | Body:       "<the (body pn), s0> -c-> s1 ==>
                 <BODY pn, s0> -c-> s1"

  | Call:       "<BODY pn, (setlocs s0 newlocs)[Loc Arg::=a s0]> -c-> s1 ==>
                 <X:=CALL pn(a), s0> -c-> (setlocs s1 (getlocs s0))
                                          [X::=s1<Res>]"

inductive
  evaln :: "[com,state,nat,state] => bool"  (\<open><_,_>/ -_-> _\<close> [0,0,0,51] 51)
  where
    Skip:    "<SKIP,s> -n-> s"

  | Assign:  "<X :== a,s> -n-> s[X::=a s]"

  | Local:   "<c, s0[Loc Y::= a s0]> -n-> s1 ==>
              <LOCAL Y := a IN c, s0> -n-> s1[Loc Y::=s0<Y>]"

  | Semi:    "[| <c0,s0> -n-> s1; <c1,s1> -n-> s2 |] ==>
              <c0;; c1, s0> -n-> s2"

  | IfTrue:  "[| b s; <c0,s> -n-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -n-> s1"

  | IfFalse: "[| ~b s; <c1,s> -n-> s1 |] ==>
              <IF b THEN c0 ELSE c1, s> -n-> s1"

  | WhileFalse: "~b s ==> <WHILE b DO c,s> -n-> s"

  | WhileTrue:  "[| b s0;  <c,s0> -n-> s1;  <WHILE b DO c, s1> -n-> s2 |] ==>
                 <WHILE b DO c, s0> -n-> s2"

  | Body:       "<the (body pn), s0> -    n-> s1 ==>
                 <BODY pn, s0> -Suc n-> s1"

  | Call:       "<BODY pn, (setlocs s0 newlocs)[Loc Arg::=a s0]> -n-> s1 ==>
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

declare evalc.intros [intro]
declare evaln.intros [intro]

declare evalc_elim_cases [elim!]
declare evaln_elim_cases [elim!]

(* evaluation of com is deterministic *)
lemma com_det [rule_format (no_asm)]: "<c,s> -c-> t \<Longrightarrow> (\<forall>u. <c,s> -c-> u \<longrightarrow> u=t)"
apply (erule evalc.induct)
apply (erule_tac [8] V = "<c,s1> -c-> s2" for c in thin_rl)
apply (blast elim: evalc_WHILE_case)+
done

lemma evaln_evalc: "<c,s> -n-> t ==> <c,s> -c-> t"
apply (erule evaln.induct)
apply (tactic \<open>
  ALLGOALS (resolve_tac \<^context> @{thms evalc.intros} THEN_ALL_NEW assume_tac \<^context>)
\<close>)
done

lemma Suc_le_D_lemma: "[| Suc n <= m'; (!!m. n <= m ==> P (Suc m)) |] ==> P m'"
apply (frule Suc_le_D)
apply blast
done

lemma evaln_nonstrict [rule_format]: "<c,s> -n-> t \<Longrightarrow> \<forall>m. n<=m \<longrightarrow> <c,s> -m-> t"
apply (erule evaln.induct)
apply (auto elim!: Suc_le_D_lemma)
done

lemma evaln_Suc: "<c,s> -n-> s' ==> <c,s> -Suc n-> s'"
apply (erule evaln_nonstrict)
apply auto
done

lemma evaln_max2: "[| <c1,s1> -n1-> t1;  <c2,s2> -n2-> t2 |] ==>  
    \<exists>n. <c1,s1> -n -> t1 \<and> <c2,s2> -n -> t2"
apply (cut_tac m = "n1" and n = "n2" in nat_le_linear)
apply (blast dest: evaln_nonstrict)
done

lemma evalc_evaln: "<c,s> -c-> t \<Longrightarrow> \<exists>n. <c,s> -n-> t"
apply (erule evalc.induct)
apply (tactic \<open>ALLGOALS (REPEAT o eresolve_tac \<^context> [exE])\<close>)
apply (tactic \<open>TRYALL (EVERY' [dresolve_tac \<^context> @{thms evaln_max2}, assume_tac \<^context>,
  REPEAT o eresolve_tac \<^context> [exE, conjE]])\<close>)
apply (tactic
  \<open>ALLGOALS (resolve_tac \<^context> [exI] THEN'
    resolve_tac \<^context> @{thms evaln.intros} THEN_ALL_NEW assume_tac \<^context>)\<close>)
done

lemma eval_eq: "<c,s> -c-> t = (\<exists>n. <c,s> -n-> t)"
apply (fast elim: evalc_evaln evaln_evalc)
done

end
