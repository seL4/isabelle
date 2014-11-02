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
type_synonym ('a,'r) channel =" (PrIds => ('a,'r) chan) stfun"

consts
  (* data-level functions *)
  cbit          :: "('a,'r) chan => bit"
  rbit          :: "('a,'r) chan => bit"
  arg           :: "('a,'r) chan => 'a"
  res           :: "('a,'r) chan => 'r"

  (* state functions *)
  caller        :: "('a,'r) channel => (PrIds => (bit * 'a)) stfun"
  rtrner        :: "('a,'r) channel => (PrIds => (bit * 'r)) stfun"

  (* state predicates *)
  Calling   :: "('a,'r) channel => PrIds => stpred"

  (* actions *)
  ACall      :: "('a,'r) channel => PrIds => 'a stfun => action"
  AReturn    :: "('a,'r) channel => PrIds => 'r stfun => action"

  (* temporal formulas *)
  PLegalCaller      :: "('a,'r) channel => PrIds => temporal"
  LegalCaller       :: "('a,'r) channel => temporal"
  PLegalReturner    :: "('a,'r) channel => PrIds => temporal"
  LegalReturner     :: "('a,'r) channel => temporal"

  (* slice through array-valued state function *)
  slice        :: "('a => 'b) stfun => 'a => 'b stfun"

syntax
  "_slice"    :: "[lift, 'a] => lift"      ("(_!_)" [70,70] 70)

  "_Call"     :: "['a, 'b, lift] => lift"    ("(Call _ _ _)" [90,90,90] 90)
  "_Return"   :: "['a, 'b, lift] => lift"    ("(Return _ _ _)" [90,90,90] 90)

translations
  "_slice"  ==  "CONST slice"

  "_Call"   ==  "CONST ACall"
  "_Return" ==  "CONST AReturn"

defs
  slice_def:     "(PRED (x!i)) s == x s i"

  caller_def:    "caller ch   == %s p. (cbit (ch s p), arg (ch s p))"
  rtrner_def:    "rtrner ch   == %s p. (rbit (ch s p), res (ch s p))"

  Calling_def:   "Calling ch p  == PRED cbit< ch!p > ~= rbit< ch!p >"
  Call_def:      "(ACT Call ch p v)   == ACT  ~ $Calling ch p
                                     & (cbit<ch!p>$ ~= $rbit<ch!p>)
                                     & (arg<ch!p>$ = $v)"
  Return_def:    "(ACT Return ch p v) == ACT  $Calling ch p
                                     & (rbit<ch!p>$ = $cbit<ch!p>)
                                     & (res<ch!p>$ = $v)"
  PLegalCaller_def:      "PLegalCaller ch p == TEMP
                             Init(~ Calling ch p)
                             & [][ ? a. Call ch p a ]_((caller ch)!p)"
  LegalCaller_def:       "LegalCaller ch == TEMP (! p. PLegalCaller ch p)"
  PLegalReturner_def:    "PLegalReturner ch p == TEMP
                                [][ ? v. Return ch p v ]_((rtrner ch)!p)"
  LegalReturner_def:     "LegalReturner ch == TEMP (! p. PLegalReturner ch p)"

declare slice_def [simp]

lemmas Procedure_defs = caller_def rtrner_def Calling_def Call_def Return_def
  PLegalCaller_def LegalCaller_def PLegalReturner_def LegalReturner_def

(* Calls and returns change their subchannel *)
lemma Call_changed: "|- Call ch p v --> <Call ch p v>_((caller ch)!p)"
  by (auto simp: angle_def Call_def caller_def Calling_def)

lemma Return_changed: "|- Return ch p v --> <Return ch p v>_((rtrner ch)!p)"
  by (auto simp: angle_def Return_def rtrner_def Calling_def)

end
