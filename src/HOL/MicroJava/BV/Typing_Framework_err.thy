(*  Title:      HOL/MicroJava/BV/Typing_Framework_err.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 TUM

*)

header {* \isaheader{Static and Dynamic Welltyping} *}

theory Typing_Framework_err = Typing_Framework + SemilatAlg:

constdefs

dynamic_wt :: "'s ord \<Rightarrow> 's err step_type \<Rightarrow> 's err list \<Rightarrow> bool"
"dynamic_wt r step ts == wt_step (Err.le r) Err step ts"

static_wt :: "'s ord \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
"static_wt r app step ts == 
  \<forall>p < size ts. app p (ts!p) \<and> (\<forall>(q,t) \<in> set (step p (ts!p)). t <=_r ts!q)"

map_snd :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list"
"map_snd f == map (\<lambda>(x,y). (x, f y))"

map_err :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b err) list"
"map_err == map_snd (\<lambda>y. Err)"

err_step :: "(nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's step_type \<Rightarrow> 's err step_type"
"err_step app step p t == case t of Err \<Rightarrow> map_err (step p arbitrary) | OK t' \<Rightarrow> 
  if app p t' then map_snd OK (step p t') else map_err (step p t')"

non_empty :: "'s step_type \<Rightarrow> bool"
"non_empty step == \<forall>p t. step p t \<noteq> []"


lemmas err_step_defs = err_step_def map_snd_def map_err_def

lemma non_emptyD:
  "non_empty step \<Longrightarrow> \<exists>q t'. (q,t') \<in> set(step p t)"
proof (unfold non_empty_def)
  assume "\<forall>p t. step p t \<noteq> []"
  hence "step p t \<noteq> []" by blast
  then obtain x xs where "step p t = x#xs"
    by (auto simp add: neq_Nil_conv)
  hence "x \<in> set(step p t)" by simp
  thus ?thesis by (cases x) blast
qed


lemma dynamic_imp_static:
  "\<lbrakk> bounded step (size ts); non_empty step;
      dynamic_wt r (err_step app step) ts \<rbrakk> 
  \<Longrightarrow> static_wt r app step (map ok_val ts)"
proof (unfold static_wt_def, intro strip, rule conjI)

  assume b:  "bounded step (size ts)"
  assume n:  "non_empty step"
  assume wt: "dynamic_wt r (err_step app step) ts"

  fix p 
  assume "p < length (map ok_val ts)"
  hence lp: "p < length ts" by simp

  from wt lp
  have [intro?]: "\<And>p. p < length ts \<Longrightarrow> ts ! p \<noteq> Err" 
    by (unfold dynamic_wt_def wt_step_def) simp

  show app: "app p (map ok_val ts ! p)"
  proof -
    from wt lp 
    obtain s where
      OKp:  "ts ! p = OK s" and
      less: "\<forall>(q,t) \<in> set (err_step app step p (ts!p)). t <=_(Err.le r) ts!q"
      by (unfold dynamic_wt_def wt_step_def stable_def) 
         (auto iff: not_Err_eq)
    
    from n
    obtain q t where q: "(q,t) \<in> set(step p s)"
      by (blast dest: non_emptyD)

    from lp b q
    have lq: "q < length ts" by (unfold bounded_def) blast
    hence "ts!q \<noteq> Err" ..
    then obtain s' where OKq: "ts ! q = OK s'" by (auto iff: not_Err_eq)      

    with OKp less q have "app p s"
      by (auto simp add: err_step_defs split: err.split_asm split_if_asm)

    with lp OKp show ?thesis by simp
  qed
  
  show "\<forall>(q,t)\<in>set(step p (map ok_val ts ! p)). t <=_r map ok_val ts ! q" 
  proof clarify
    fix q t assume q: "(q,t) \<in> set (step p (map ok_val ts ! p))"

    from wt lp q
    obtain s where
      OKp:  "ts ! p = OK s" and
      less: "\<forall>(q,t) \<in> set (err_step app step p (ts!p)). t <=_(Err.le r) ts!q"
      by (unfold dynamic_wt_def wt_step_def stable_def) 
         (auto iff: not_Err_eq)

    from lp b q
    have lq: "q < length ts" by (unfold bounded_def) blast
    hence "ts!q \<noteq> Err" ..
    then obtain s' where OKq: "ts ! q = OK s'" by (auto iff: not_Err_eq)

    from lp lq OKp OKq app less q
    show "t <=_r map ok_val ts ! q"
      by (auto simp add: err_step_def map_snd_def) 
  qed
qed


lemma static_imp_dynamic:
  "\<lbrakk> static_wt r app step ts; bounded step (size ts) \<rbrakk> 
  \<Longrightarrow> dynamic_wt r (err_step app step) (map OK ts)"
proof (unfold dynamic_wt_def wt_step_def, intro strip, rule conjI)
  assume bounded: "bounded step (size ts)"
  assume static:  "static_wt r app step ts"
  fix p assume "p < length (map OK ts)" 
  hence p: "p < length ts" by simp
  thus "map OK ts ! p \<noteq> Err" by simp
  { fix q t
    assume q: "(q,t) \<in> set (err_step app step p (map OK ts ! p))" 
    with p static obtain 
      "app p (ts ! p)" "\<forall>(q,t) \<in> set (step p (ts!p)). t <=_r ts!q"
      by (unfold static_wt_def) blast
    moreover
    from q p bounded have "q < size ts" 
      by (clarsimp simp add: bounded_def err_step_defs 
          split: err.splits split_if_asm) blast+
    hence "map OK ts ! q = OK (ts!q)" by simp
    moreover
    have "p < size ts" by (rule p)
    moreover note q
    ultimately     
    have "t <=_(Err.le r) map OK ts ! q" 
      by (auto simp add: err_step_def map_snd_def)
  }
  thus "stable (Err.le r) (err_step app step) (map OK ts) p"
    by (unfold stable_def) blast
qed

end
