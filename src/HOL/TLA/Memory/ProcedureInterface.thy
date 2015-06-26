(*  Title:      HOL/TLA/Memory/ProcedureInterface.thy
    Author:     Stephan Merz, University of Munich
*)

section {* Procedure interface for RPC-Memory components *}

theory ProcedureInterface
imports "../TLA" RPCMemoryParams
begin

typedecl ('a,'r) chan
  (* type of channels with argument type 'a and return type 'r.
     we model a channel as an array of variables (of type chan)
     rather than a single array-valued variable because the
     notation gets a little simpler.
  *)
type_synonym ('a,'r) channel =" (PrIds \<Rightarrow> ('a,'r) chan) stfun"

consts
  (* data-level functions *)
  cbit          :: "('a,'r) chan \<Rightarrow> bit"
  rbit          :: "('a,'r) chan \<Rightarrow> bit"
  arg           :: "('a,'r) chan \<Rightarrow> 'a"
  res           :: "('a,'r) chan \<Rightarrow> 'r"

  (* state functions *)
  caller        :: "('a,'r) channel \<Rightarrow> (PrIds \<Rightarrow> (bit * 'a)) stfun"
  rtrner        :: "('a,'r) channel \<Rightarrow> (PrIds \<Rightarrow> (bit * 'r)) stfun"

  (* state predicates *)
  Calling   :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> stpred"

  (* actions *)
  ACall      :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> 'a stfun \<Rightarrow> action"
  AReturn    :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> 'r stfun \<Rightarrow> action"

  (* temporal formulas *)
  PLegalCaller      :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> temporal"
  LegalCaller       :: "('a,'r) channel \<Rightarrow> temporal"
  PLegalReturner    :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> temporal"
  LegalReturner     :: "('a,'r) channel \<Rightarrow> temporal"

  (* slice through array-valued state function *)
  slice        :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b stfun"

syntax
  "_slice"    :: "[lift, 'a] \<Rightarrow> lift"      ("(_!_)" [70,70] 70)

  "_Call"     :: "['a, 'b, lift] \<Rightarrow> lift"    ("(Call _ _ _)" [90,90,90] 90)
  "_Return"   :: "['a, 'b, lift] \<Rightarrow> lift"    ("(Return _ _ _)" [90,90,90] 90)

translations
  "_slice"  ==  "CONST slice"

  "_Call"   ==  "CONST ACall"
  "_Return" ==  "CONST AReturn"

defs
  slice_def:     "(PRED (x!i)) s == x s i"

  caller_def:    "caller ch   == \<lambda>s p. (cbit (ch s p), arg (ch s p))"
  rtrner_def:    "rtrner ch   == \<lambda>s p. (rbit (ch s p), res (ch s p))"

  Calling_def:   "Calling ch p  == PRED cbit< ch!p > \<noteq> rbit< ch!p >"
  Call_def:      "(ACT Call ch p v)   == ACT  \<not> $Calling ch p
                                     \<and> (cbit<ch!p>$ \<noteq> $rbit<ch!p>)
                                     \<and> (arg<ch!p>$ = $v)"
  Return_def:    "(ACT Return ch p v) == ACT  $Calling ch p
                                     \<and> (rbit<ch!p>$ = $cbit<ch!p>)
                                     \<and> (res<ch!p>$ = $v)"
  PLegalCaller_def:      "PLegalCaller ch p == TEMP
                             Init(\<not> Calling ch p)
                             \<and> \<box>[\<exists>a. Call ch p a ]_((caller ch)!p)"
  LegalCaller_def:       "LegalCaller ch == TEMP (\<forall>p. PLegalCaller ch p)"
  PLegalReturner_def:    "PLegalReturner ch p == TEMP
                                \<box>[\<exists>v. Return ch p v ]_((rtrner ch)!p)"
  LegalReturner_def:     "LegalReturner ch == TEMP (\<forall>p. PLegalReturner ch p)"

declare slice_def [simp]

lemmas Procedure_defs = caller_def rtrner_def Calling_def Call_def Return_def
  PLegalCaller_def LegalCaller_def PLegalReturner_def LegalReturner_def

(* Calls and returns change their subchannel *)
lemma Call_changed: "\<turnstile> Call ch p v \<longrightarrow> <Call ch p v>_((caller ch)!p)"
  by (auto simp: angle_def Call_def caller_def Calling_def)

lemma Return_changed: "\<turnstile> Return ch p v \<longrightarrow> <Return ch p v>_((rtrner ch)!p)"
  by (auto simp: angle_def Return_def rtrner_def Calling_def)

end
