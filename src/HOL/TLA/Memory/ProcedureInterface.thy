(*  Title:      HOL/TLA/Memory/ProcedureInterface.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>Procedure interface for RPC-Memory components\<close>

theory ProcedureInterface
imports "HOL-TLA.TLA" RPCMemoryParams
begin

typedecl ('a,'r) chan
  (* type of channels with argument type 'a and return type 'r.
     we model a channel as an array of variables (of type chan)
     rather than a single array-valued variable because the
     notation gets a little simpler.
  *)
type_synonym ('a,'r) channel =" (PrIds \<Rightarrow> ('a,'r) chan) stfun"


(* data-level functions *)

consts
  cbit          :: "('a,'r) chan \<Rightarrow> bit"
  rbit          :: "('a,'r) chan \<Rightarrow> bit"
  arg           :: "('a,'r) chan \<Rightarrow> 'a"
  res           :: "('a,'r) chan \<Rightarrow> 'r"


(* state functions *)

definition caller :: "('a,'r) channel \<Rightarrow> (PrIds \<Rightarrow> (bit * 'a)) stfun"
  where "caller ch == \<lambda>s p. (cbit (ch s p), arg (ch s p))"

definition rtrner :: "('a,'r) channel \<Rightarrow> (PrIds \<Rightarrow> (bit * 'r)) stfun"
  where "rtrner ch == \<lambda>s p. (rbit (ch s p), res (ch s p))"


(* slice through array-valued state function *)

definition slice :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b stfun"
  where "slice x i s \<equiv> x s i"

syntax
  "_slice" :: "[lift, 'a] \<Rightarrow> lift"  (\<open>(_!_)\<close> [70,70] 70)
translations
  "_slice" \<rightleftharpoons> "CONST slice"


(* state predicates *)

definition Calling :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> stpred"
  where "Calling ch p == PRED cbit< ch!p > \<noteq> rbit< ch!p >"


(* actions *)

definition ACall :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> 'a stfun \<Rightarrow> action"
  where "ACall ch p v \<equiv> ACT
      \<not> $Calling ch p
    \<and> (cbit<ch!p>$ \<noteq> $rbit<ch!p>)
    \<and> (arg<ch!p>$ = $v)"

definition AReturn :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> 'r stfun \<Rightarrow> action"
  where "AReturn ch p v == ACT
      $Calling ch p
    \<and> (rbit<ch!p>$ = $cbit<ch!p>)
    \<and> (res<ch!p>$ = $v)"

syntax
  "_Call" :: "['a, 'b, lift] \<Rightarrow> lift"  (\<open>(Call _ _ _)\<close> [90,90,90] 90)
  "_Return" :: "['a, 'b, lift] \<Rightarrow> lift"  (\<open>(Return _ _ _)\<close> [90,90,90] 90)
translations
  "_Call" \<rightleftharpoons> "CONST ACall"
  "_Return" \<rightleftharpoons> "CONST AReturn"


(* temporal formulas *)

definition PLegalCaller :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> temporal"
  where "PLegalCaller ch p == TEMP
     Init(\<not> Calling ch p)
     \<and> \<box>[\<exists>a. Call ch p a ]_((caller ch)!p)"

definition LegalCaller :: "('a,'r) channel \<Rightarrow> temporal"
  where "LegalCaller ch == TEMP (\<forall>p. PLegalCaller ch p)"

definition PLegalReturner :: "('a,'r) channel \<Rightarrow> PrIds \<Rightarrow> temporal"
  where "PLegalReturner ch p == TEMP \<box>[\<exists>v. Return ch p v ]_((rtrner ch)!p)"

definition LegalReturner :: "('a,'r) channel \<Rightarrow> temporal"
  where "LegalReturner ch == TEMP (\<forall>p. PLegalReturner ch p)"

declare slice_def [simp]

lemmas Procedure_defs = caller_def rtrner_def Calling_def ACall_def AReturn_def
  PLegalCaller_def LegalCaller_def PLegalReturner_def LegalReturner_def

(* Calls and returns change their subchannel *)
lemma Call_changed: "\<turnstile> Call ch p v \<longrightarrow> <Call ch p v>_((caller ch)!p)"
  by (auto simp: angle_def ACall_def caller_def Calling_def)

lemma Return_changed: "\<turnstile> Return ch p v \<longrightarrow> <Return ch p v>_((rtrner ch)!p)"
  by (auto simp: angle_def AReturn_def rtrner_def Calling_def)

end
