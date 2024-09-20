(*  Title:      HOL/IMPP/Hoare.thy
    Author:     David von Oheimb
    Copyright   1999 TUM
*)

section \<open>Inductive definition of Hoare logic for partial correctness\<close>

theory Hoare
imports Natural
begin

text \<open>
  Completeness is taken relative to completeness of the underlying logic.

  Two versions of completeness proof: nested single recursion
  vs. simultaneous recursion in call rule
\<close>

type_synonym 'a assn = "'a => state => bool"
translations
  (type) "'a assn" <= (type) "'a => state => bool"

definition
  state_not_singleton :: bool where
  "state_not_singleton = (\<exists>s t::state. s ~= t)" (* at least two elements *)

definition
  peek_and :: "'a assn => (state => bool) => 'a assn" (infixr \<open>&>\<close> 35) where
  "peek_and P p = (%Z s. P Z s & p s)"

datatype 'a triple =
  triple "'a assn"  com  "'a assn"       (\<open>{(1_)}./ (_)/ .{(1_)}\<close> [3,60,3] 58)

definition
  triple_valid :: "nat => 'a triple     => bool" ( \<open>|=_:_\<close> [0 , 58] 57) where
  "|=n:t = (case t of {P}.c.{Q} =>
             \<forall>Z s. P Z s \<longrightarrow> (\<forall>s'. <c,s> -n-> s' \<longrightarrow> Q Z s'))"
abbreviation
  triples_valid :: "nat => 'a triple set => bool" (\<open>||=_:_\<close> [0 , 58] 57) where
  "||=n:G == Ball G (triple_valid n)"

definition
  hoare_valids :: "'a triple set => 'a triple set => bool" (\<open>_||=_\<close>  [58, 58] 57) where
  "G||=ts = (\<forall>n. ||=n:G --> ||=n:ts)"
abbreviation
  hoare_valid :: "'a triple set => 'a triple     => bool" (\<open>_|=_\<close>   [58, 58] 57) where
  "G |=t == G||={t}"

(* Most General Triples *)
definition
  MGT :: "com => state triple"            (\<open>{=}._.{->}\<close> [60] 58) where
  "{=}.c.{->} = {%Z s0. Z = s0}. c .{%Z s1. <c,Z> -c-> s1}"

inductive
  hoare_derivs :: "'a triple set => 'a triple set => bool" (\<open>_||-_\<close>  [58, 58] 57) and
  hoare_deriv :: "'a triple set => 'a triple     => bool" (\<open>_|-_\<close>   [58, 58] 57)
where
  "G |-t == G||-{t}"

| empty:    "G||-{}"
| insert: "[| G |-t;  G||-ts |]
        ==> G||-insert t ts"

| asm:      "ts <= G ==>
             G||-ts" (* {P}.BODY pn.{Q} instead of (general) t for SkipD_lemma *)

| cut:   "[| G'||-ts; G||-G' |] ==> G||-ts" (* for convenience and efficiency *)

| weaken: "[| G||-ts' ; ts <= ts' |] ==> G||-ts"

| conseq: "\<forall>Z s. P  Z  s \<longrightarrow> (\<exists>P' Q'. G|-{P'}.c.{Q'} \<and>
                                   (\<forall>s'. (\<forall>Z'. P' Z' s \<longrightarrow> Q' Z' s') \<longrightarrow> Q Z s'))
          ==> G|-{P}.c.{Q}"


| Skip:  "G|-{P}. SKIP .{P}"

| Ass:   "G|-{%Z s. P Z (s[X::=a s])}. X:==a .{P}"

| Local: "G|-{P}. c .{%Z s. Q Z (s[Loc X::=s'<X>])}
      ==> G|-{%Z s. s'=s & P Z (s[Loc X::=a s])}. LOCAL X:=a IN c .{Q}"

| Comp:  "[| G|-{P}.c.{Q};
             G|-{Q}.d.{R} |]
         ==> G|-{P}. (c;;d) .{R}"

| If:    "[| G|-{P &>        b }.c.{Q};
             G|-{P &> (Not o b)}.d.{Q} |]
         ==> G|-{P}. IF b THEN c ELSE d .{Q}"

| Loop:  "G|-{P &> b}.c.{P} ==>
          G|-{P}. WHILE b DO c .{P &> (Not o b)}"

(*
  BodyN: "(insert ({P}. BODY pn  .{Q}) G)
           |-{P}.  the (body pn) .{Q} ==>
          G|-{P}.       BODY pn  .{Q}"
*)
| Body:  "[| G Un (%p. {P p}.      BODY p  .{Q p})`Procs
               ||-(%p. {P p}. the (body p) .{Q p})`Procs |]
         ==>  G||-(%p. {P p}.      BODY p  .{Q p})`Procs"

| Call:     "G|-{P}. BODY pn .{%Z s. Q Z (setlocs s (getlocs s')[X::=s<Res>])}
         ==> G|-{%Z s. s'=s & P Z (setlocs s newlocs[Loc Arg::=a s])}.
             X:=CALL pn(a) .{Q}"


section \<open>Soundness and relative completeness of Hoare rules wrt operational semantics\<close>

lemma single_stateE:
  "state_not_singleton \<Longrightarrow> \<forall>t. (\<forall>s::state. s = t) \<longrightarrow> False"
apply (unfold state_not_singleton_def)
apply clarify
apply (case_tac "ta = t")
apply blast
apply (blast dest: not_sym)
done

declare peek_and_def [simp]


subsection "validity"

lemma triple_valid_def2:
  "|=n:{P}.c.{Q} = (\<forall>Z s. P Z s \<longrightarrow> (\<forall>s'. <c,s> -n-> s' \<longrightarrow> Q Z s'))"
apply (unfold triple_valid_def)
apply auto
done

lemma Body_triple_valid_0: "|=0:{P}. BODY pn .{Q}"
apply (simp (no_asm) add: triple_valid_def2)
apply clarsimp
done

(* only ==> direction required *)
lemma Body_triple_valid_Suc: "|=n:{P}. the (body pn) .{Q} = |=Suc n:{P}. BODY pn .{Q}"
apply (simp (no_asm) add: triple_valid_def2)
apply force
done

lemma triple_valid_Suc [rule_format (no_asm)]: "|=Suc n:t --> |=n:t"
apply (unfold triple_valid_def)
apply (induct_tac t)
apply simp
apply (fast intro: evaln_Suc)
done

lemma triples_valid_Suc: "||=Suc n:ts ==> ||=n:ts"
apply (fast intro: triple_valid_Suc)
done


subsection "derived rules"

lemma conseq12: "[| G|-{P'}.c.{Q'}; \<forall>Z s. P Z s \<longrightarrow>
                         (\<forall>s'. (\<forall>Z'. P' Z' s \<longrightarrow> Q' Z' s') --> Q Z s') |]
       ==> G|-{P}.c.{Q}"
apply (rule hoare_derivs.conseq)
apply blast
done

lemma conseq1: "[| G|-{P'}.c.{Q}; \<forall>Z s. P Z s \<longrightarrow> P' Z s |] ==> G|-{P}.c.{Q}"
apply (erule conseq12)
apply fast
done

lemma conseq2: "[| G|-{P}.c.{Q'}; \<forall>Z s. Q' Z s \<longrightarrow> Q Z s |] ==> G|-{P}.c.{Q}"
apply (erule conseq12)
apply fast
done

lemma Body1: "[| G Un (\<lambda>p. {P p}.      BODY p  .{Q p})`Procs
          ||- (\<lambda>p. {P p}. the (body p) .{Q p})`Procs;
    pn \<in> Procs |] ==> G|-{P pn}. BODY pn .{Q pn}"
apply (drule hoare_derivs.Body)
apply (erule hoare_derivs.weaken)
apply fast
done

lemma BodyN: "(insert ({P}. BODY pn .{Q}) G) |-{P}. the (body pn) .{Q} ==>
  G|-{P}. BODY pn .{Q}"
apply (rule Body1)
apply (rule_tac [2] singletonI)
apply clarsimp
done

lemma escape: "[| \<forall>Z s. P Z s \<longrightarrow> G|-{\<lambda>Z s'. s'=s}.c.{\<lambda>Z'. Q Z} |] ==> G|-{P}.c.{Q}"
apply (rule hoare_derivs.conseq)
apply fast
done

lemma "constant": "[| C ==> G|-{P}.c.{Q} |] ==> G|-{\<lambda>Z s. P Z s & C}.c.{Q}"
apply (rule hoare_derivs.conseq)
apply fast
done

lemma LoopF: "G|-{\<lambda>Z s. P Z s \<and> \<not>b s}.WHILE b DO c.{P}"
apply (rule hoare_derivs.Loop [THEN conseq2])
apply  (simp_all (no_asm))
apply (rule hoare_derivs.conseq)
apply fast
done

(*
Goal "[| G'||-ts; G' <= G |] ==> G||-ts"
by (etac hoare_derivs.cut 1);
by (etac hoare_derivs.asm 1);
qed "thin";
*)
lemma thin [rule_format]: "G'||-ts \<Longrightarrow> \<forall>G. G' <= G \<longrightarrow> G||-ts"
apply (erule hoare_derivs.induct)
apply                (tactic \<open>ALLGOALS (EVERY'[clarify_tac \<^context>, REPEAT o smp_tac \<^context> 1])\<close>)
apply (rule hoare_derivs.empty)
apply               (erule (1) hoare_derivs.insert)
apply              (fast intro: hoare_derivs.asm)
apply             (fast intro: hoare_derivs.cut)
apply            (fast intro: hoare_derivs.weaken)
apply           (rule hoare_derivs.conseq, intro strip, tactic "smp_tac \<^context> 2 1", clarify, tactic "smp_tac \<^context> 1 1",rule exI, rule exI, erule (1) conjI)
prefer 7
apply          (rule_tac hoare_derivs.Body, drule_tac spec, erule_tac mp, fast)
apply         (tactic \<open>ALLGOALS (resolve_tac \<^context> ((funpow 5 tl) @{thms hoare_derivs.intros}) THEN_ALL_NEW (fast_tac \<^context>))\<close>)
done

lemma weak_Body: "G|-{P}. the (body pn) .{Q} ==> G|-{P}. BODY pn .{Q}"
apply (rule BodyN)
apply (erule thin)
apply auto
done

lemma derivs_insertD: "G||-insert t ts ==> G|-t & G||-ts"
apply (fast intro: hoare_derivs.weaken)
done

lemma finite_pointwise [rule_format (no_asm)]: "[| finite U;
  \<forall>p. G |-     {P' p}.c0 p.{Q' p}       --> G |-     {P p}.c0 p.{Q p} |] ==>
      G||-(%p. {P' p}.c0 p.{Q' p}) ` U --> G||-(%p. {P p}.c0 p.{Q p}) ` U"
apply (erule finite_induct)
apply simp
apply clarsimp
apply (drule derivs_insertD)
apply (rule hoare_derivs.insert)
apply  auto
done


subsection "soundness"

lemma Loop_sound_lemma:
 "G|={P &> b}. c .{P} ==>
  G|={P}. WHILE b DO c .{P &> (Not o b)}"
apply (unfold hoare_valids_def)
apply (simp (no_asm_use) add: triple_valid_def2)
apply (rule allI)
apply (subgoal_tac "\<forall>d s s'. <d,s> -n-> s' --> d = WHILE b DO c --> ||=n:G --> (\<forall>Z. P Z s --> P Z s' & ~b s') ")
apply  (erule thin_rl, fast)
apply ((rule allI)+, rule impI)
apply (erule evaln.induct)
apply (simp_all (no_asm))
apply fast
apply fast
done

lemma Body_sound_lemma:
   "[| G Un (%pn. {P pn}.      BODY pn  .{Q pn})`Procs
         ||=(%pn. {P pn}. the (body pn) .{Q pn})`Procs |] ==>
        G||=(%pn. {P pn}.      BODY pn  .{Q pn})`Procs"
apply (unfold hoare_valids_def)
apply (rule allI)
apply (induct_tac n)
apply  (fast intro: Body_triple_valid_0)
apply clarsimp
apply (drule triples_valid_Suc)
apply (erule (1) notE impE)
apply (simp add: ball_Un)
apply (drule spec, erule impE, erule conjI, assumption)
apply (fast intro!: Body_triple_valid_Suc [THEN iffD1])
done

lemma hoare_sound: "G||-ts ==> G||=ts"
apply (erule hoare_derivs.induct)
apply              (tactic \<open>TRYALL (eresolve_tac \<^context> [@{thm Loop_sound_lemma}, @{thm Body_sound_lemma}] THEN_ALL_NEW assume_tac \<^context>)\<close>)
apply            (unfold hoare_valids_def)
apply            blast
apply           blast
apply          (blast) (* asm *)
apply         (blast) (* cut *)
apply        (blast) (* weaken *)
apply       (tactic \<open>ALLGOALS (EVERY'
  [REPEAT o Rule_Insts.thin_tac \<^context> "hoare_derivs _ _" [],
   simp_tac \<^context>, clarify_tac \<^context>, REPEAT o smp_tac \<^context> 1])\<close>)
apply       (simp_all (no_asm_use) add: triple_valid_def2)
apply       (intro strip, tactic "smp_tac \<^context> 2 1", blast) (* conseq *)
apply      (tactic \<open>ALLGOALS (clarsimp_tac \<^context>)\<close>) (* Skip, Ass, Local *)
prefer 3 apply   (force) (* Call *)
apply  (erule_tac [2] evaln_elim_cases) (* If *)
apply   blast+
done


section "completeness"

(* Both versions *)

(*unused*)
lemma MGT_alternI: "G|-MGT c \<Longrightarrow>
  G|-{\<lambda>Z s0. \<forall>s1. <c,s0> -c-> s1 \<longrightarrow> Z=s1}. c .{\<lambda>Z s1. Z=s1}"
apply (unfold MGT_def)
apply (erule conseq12)
apply auto
done

(* requires com_det *)
lemma MGT_alternD: "state_not_singleton \<Longrightarrow>
  G|-{\<lambda>Z s0. \<forall>s1. <c,s0> -c-> s1 \<longrightarrow> Z=s1}. c .{\<lambda>Z s1. Z=s1} \<Longrightarrow> G|-MGT c"
apply (unfold MGT_def)
apply (erule conseq12)
apply auto
apply (case_tac "\<exists>t. <c,s> -c-> t" for s)
apply  (fast elim: com_det)
apply clarsimp
apply (drule single_stateE)
apply blast
done

lemma MGF_complete:
 "{}|-(MGT c::state triple) ==> {}|={P}.c.{Q} ==> {}|-{P}.c.{Q::state assn}"
apply (unfold MGT_def)
apply (erule conseq12)
apply (clarsimp simp add: hoare_valids_def eval_eq triple_valid_def2)
done

declare WTs_elim_cases [elim!]
declare not_None_eq [iff]
(* requires com_det, escape (i.e. hoare_derivs.conseq) *)
lemma MGF_lemma1 [rule_format (no_asm)]: "state_not_singleton \<Longrightarrow>
  \<forall>pn \<in> dom body. G|-{=}.BODY pn.{->} \<Longrightarrow> WT c --> G|-{=}.c.{->}"
apply (induct_tac c)
apply        (tactic \<open>ALLGOALS (clarsimp_tac \<^context>)\<close>)
prefer 7 apply        (fast intro: domI)
apply (erule_tac [6] MGT_alternD)
apply       (unfold MGT_def)
apply       (drule_tac [7] bspec, erule_tac [7] domI)
apply       (rule_tac [7] escape, tactic \<open>clarsimp_tac \<^context> 7\<close>,
  rename_tac [7] "fun" y Z,
  rule_tac [7] P1 = "%Z' s. s= (setlocs Z newlocs) [Loc Arg ::= fun Z]" in hoare_derivs.Call [THEN conseq1], erule_tac [7] conseq12)
apply        (erule_tac [!] thin_rl)
apply (rule hoare_derivs.Skip [THEN conseq2])
apply (rule_tac [2] hoare_derivs.Ass [THEN conseq1])
apply        (rule_tac [3] escape, tactic \<open>clarsimp_tac \<^context> 3\<close>,
  rename_tac [3] loc "fun" y Z,
  rule_tac [3] P1 = "%Z' s. s= (Z[Loc loc::=fun Z])" in hoare_derivs.Local [THEN conseq1],
  erule_tac [3] conseq12)
apply         (erule_tac [5] hoare_derivs.Comp, erule_tac [5] conseq12)
apply         (tactic \<open>(resolve_tac \<^context> @{thms hoare_derivs.If} THEN_ALL_NEW
                eresolve_tac \<^context> @{thms conseq12}) 6\<close>)
apply          (rule_tac [8] hoare_derivs.Loop [THEN conseq2], erule_tac [8] conseq12)
apply           auto
done

(* Version: nested single recursion *)

lemma nesting_lemma [rule_format]:
  assumes "!!G ts. ts <= G ==> P G ts"
    and "!!G pn. P (insert (mgt_call pn) G) {mgt(the(body pn))} ==> P G {mgt_call pn}"
    and "!!G c. [| wt c; \<forall>pn\<in>U. P G {mgt_call pn} |] ==> P G {mgt c}"
    and "!!pn. pn \<in> U ==> wt (the (body pn))"
  shows "finite U ==> uG = mgt_call`U ==>
  \<forall>G. G <= uG --> n <= card uG --> card G = card uG - n --> (\<forall>c. wt c --> P G {mgt c})"
apply (induct_tac n)
apply  (tactic \<open>ALLGOALS (clarsimp_tac \<^context>)\<close>)
apply  (subgoal_tac "G = mgt_call ` U")
prefer 2
apply   (simp add: card_seteq)
apply  simp
apply  (erule assms(3-)) (*MGF_lemma1*)
apply (rule ballI)
apply  (rule assms) (*hoare_derivs.asm*)
apply  fast
apply (erule assms(3-)) (*MGF_lemma1*)
apply (rule ballI)
apply (case_tac "mgt_call pn \<in> G")
apply  (rule assms) (*hoare_derivs.asm*)
apply  fast
apply (rule assms(2-)) (*MGT_BodyN*)
apply (drule spec, erule impE, erule_tac [2] impE, drule_tac [3] spec, erule_tac [3] mp)
apply   (erule_tac [3] assms(4-))
apply   fast
apply (drule finite_subset)
apply (erule finite_imageI)
apply (simp (no_asm_simp))
done

lemma MGT_BodyN: "insert ({=}.BODY pn.{->}) G|-{=}. the (body pn) .{->} ==>
  G|-{=}.BODY pn.{->}"
apply (unfold MGT_def)
apply (rule BodyN)
apply (erule conseq2)
apply force
done

(* requires BodyN, com_det *)
lemma MGF: "[| state_not_singleton; WT_bodies; WT c |] ==> {}|-MGT c"
apply (rule_tac P = "%G ts. G||-ts" and U = "dom body" in nesting_lemma)
apply (erule hoare_derivs.asm)
apply (erule MGT_BodyN)
apply (rule_tac [3] finite_dom_body)
apply (erule MGF_lemma1)
prefer 2 apply (assumption)
apply       blast
apply      clarsimp
apply     (erule (1) WT_bodiesD)
apply (rule_tac [3] le_refl)
apply    auto
done


(* Version: simultaneous recursion in call rule *)

(* finiteness not really necessary here *)
lemma MGT_Body: "[| G Un (%pn. {=}.      BODY pn  .{->})`Procs
                          ||-(%pn. {=}. the (body pn) .{->})`Procs;
  finite Procs |] ==>   G ||-(%pn. {=}.      BODY pn  .{->})`Procs"
apply (unfold MGT_def)
apply (rule hoare_derivs.Body)
apply (erule finite_pointwise)
prefer 2 apply (assumption)
apply clarify
apply (erule conseq2)
apply auto
done

(* requires empty, insert, com_det *)
lemma MGF_lemma2_simult [rule_format (no_asm)]: "[| state_not_singleton; WT_bodies;
  F<=(%pn. {=}.the (body pn).{->})`dom body |] ==>
     (%pn. {=}.     BODY pn .{->})`dom body||-F"
apply (frule finite_subset)
apply (rule finite_dom_body [THEN finite_imageI])
apply (rotate_tac 2)
apply (tactic "make_imp_tac \<^context> 1")
apply (erule finite_induct)
apply  (clarsimp intro!: hoare_derivs.empty)
apply (clarsimp intro!: hoare_derivs.insert simp del: range_composition)
apply (erule MGF_lemma1)
prefer 2 apply  (fast dest: WT_bodiesD)
apply clarsimp
apply (rule hoare_derivs.asm)
apply (fast intro: domI)
done

(* requires Body, empty, insert, com_det *)
lemma MGF': "[| state_not_singleton; WT_bodies; WT c |] ==> {}|-MGT c"
apply (rule MGF_lemma1)
apply assumption
prefer 2 apply (assumption)
apply clarsimp
apply (subgoal_tac "{}||- (%pn. {=}. BODY pn .{->}) `dom body")
apply (erule hoare_derivs.weaken)
apply  (fast intro: domI)
apply (rule finite_dom_body [THEN [2] MGT_Body])
apply (simp (no_asm))
apply (erule (1) MGF_lemma2_simult)
apply (rule subset_refl)
done

(* requires Body+empty+insert / BodyN, com_det *)
lemmas hoare_complete = MGF' [THEN MGF_complete]


subsection "unused derived rules"

lemma falseE: "G|-{%Z s. False}.c.{Q}"
apply (rule hoare_derivs.conseq)
apply fast
done

lemma trueI: "G|-{P}.c.{%Z s. True}"
apply (rule hoare_derivs.conseq)
apply (fast intro!: falseE)
done

lemma disj: "[| G|-{P}.c.{Q}; G|-{P'}.c.{Q'} |]
        ==> G|-{%Z s. P Z s | P' Z s}.c.{%Z s. Q Z s | Q' Z s}"
apply (rule hoare_derivs.conseq)
apply (fast elim: conseq12)
done (* analogue conj non-derivable *)

lemma hoare_SkipI: "(\<forall>Z s. P Z s \<longrightarrow> Q Z s) \<Longrightarrow> G|-{P}. SKIP .{Q}"
apply (rule conseq12)
apply (rule hoare_derivs.Skip)
apply fast
done


subsection "useful derived rules"

lemma single_asm: "{t}|-t"
apply (rule hoare_derivs.asm)
apply (rule subset_refl)
done

lemma export_s: "[| !!s'. G|-{%Z s. s'=s & P Z s}.c.{Q} |] ==> G|-{P}.c.{Q}"
apply (rule hoare_derivs.conseq)
apply auto
done


lemma weak_Local: "[| G|-{P}. c .{Q}; \<forall>k Z s. Q Z s --> Q Z (s[Loc Y::=k]) |] ==>
    G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{Q}"
apply (rule export_s)
apply (rule hoare_derivs.Local)
apply (erule conseq2)
apply (erule spec)
done

(*
Goal "!Q. G |-{%Z s. ~(? s'. <c,s> -c-> s')}. c .{Q}"
by (induct_tac "c" 1);
by Auto_tac;
by (rtac conseq1 1);
by (rtac hoare_derivs.Skip 1);
force 1;
by (rtac conseq1 1);
by (rtac hoare_derivs.Ass 1);
force 1;
by (defer_tac 1);
###
by (rtac hoare_derivs.Comp 1);
by (dtac spec 2);
by (dtac spec 2);
by (assume_tac 2);
by (etac conseq1 2);
by (Clarsimp_tac 2);
force 1;
*)

end
