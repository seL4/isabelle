(*  Title:      HOL/BCV/DFA_err.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 TUM

static and dynamic welltyping 
*)

header "Static and Dynamic Welltyping"

theory DFA_err = DFA_Framework:

constdefs

dynamic_wt :: "'s ord => (nat => 's err => 's err) => (nat => nat list) => 
               's err list => bool"
"dynamic_wt r step succs ts == welltyping (Err.le r) Err step succs ts"

static_wt :: "'s ord => (nat => 's => bool) => 
              (nat => 's => 's) => (nat => nat list) =>  's list => bool"
"static_wt r app step succs ts == 
  !p < size ts. app p (ts!p) & (!q:set(succs p). step p (ts!p) <=_r ts!q)"

err_step :: "(nat => 's => bool) => (nat => 's => 's) => 
             (nat => 's err => 's err)"
"err_step app step p == lift (%t. if app p t then OK (step p t) else Err)"

bounded :: "(nat => nat list) => nat => bool"
"bounded succs n == !p<n. !q:set(succs p). q<n"

non_empty :: "(nat => nat list) => bool"
"non_empty succs == !p. succs p ~= []"


lemma non_emptyD:
  "non_empty succs ==> ? q. q:set(succs p)"
proof (unfold non_empty_def)
  assume "!p. succs p ~= []"
  hence "succs p ~= []" ..
  then obtain x xs where "succs p = x#xs"
    by (auto simp add: neq_Nil_conv)
  thus ?thesis 
    by auto
qed

text_raw {* \newpage *}
lemma dynamic_imp_static:
  "[| bounded succs (size ts); non_empty succs;
      dynamic_wt r (err_step app step) succs ts |] 
  ==> static_wt r app step succs (map ok_val ts)"
proof (unfold static_wt_def, intro strip, rule conjI)

  assume b:  "bounded succs (size ts)"
  assume n:  "non_empty succs"
  assume wt: "dynamic_wt r (err_step app step) succs ts"

  fix p 
  assume "p < length (map ok_val ts)"
  hence lp: "p < length ts" by simp

  from wt lp
  have [intro?]: "!!p. p < length ts ==> ts ! p ~= Err" 
    by (unfold dynamic_wt_def welltyping_def) simp

  show app: "app p (map ok_val ts ! p)"
  proof -
    from n
    obtain q where q: "q:set(succs p)"
      by (auto dest: non_emptyD)

    from wt lp q
    obtain s where
      OKp:  "ts ! p = OK s" and
      less: "err_step app step p (ts ! p) <=_(Err.le r) ts ! q"
      by (unfold dynamic_wt_def welltyping_def stable_def) 
         (auto iff: not_Err_eq)

    from lp b q
    have lq: "q < length ts"
      by (unfold bounded_def) blast
    hence "ts!q ~= Err" ..
    then
    obtain s' where OKq: "ts ! q = OK s'"
      by (auto iff: not_Err_eq)      

    with OKp less
    have "app p s"
      by (simp add: err_step_def lift_def split: err.split_asm split_if_asm)

    with lp OKp
    show ?thesis
      by simp
  qed
  
  show "!q:set(succs p). step p (map ok_val ts ! p) <=_r map ok_val ts ! q"
  proof (intro strip)
    fix q
    assume q: "q:set (succs p)"

    from wt lp q
    obtain s where
      OKp:  "ts ! p = OK s" and
      less: "err_step app step p (ts ! p) <=_(Err.le r) ts ! q"
      by (unfold dynamic_wt_def welltyping_def stable_def) 
         (auto iff: not_Err_eq)

    from lp b q
    have lq: "q < length ts"
      by (unfold bounded_def) blast
    hence "ts!q ~= Err" ..
    then
    obtain s' where OKq: "ts ! q = OK s'"
      by (auto iff: not_Err_eq)      

    from lp lq OKp OKq app less
    show "step p (map ok_val ts ! p) <=_r map ok_val ts ! q"
      by (simp add: err_step_def lift_def)
  qed
qed

end
