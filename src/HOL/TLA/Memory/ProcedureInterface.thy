(*
    File:        ProcedureInterface.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

   Theory Name: ProcedureInterface
   Logic Image: TLA

   Procedure interface for RPC-Memory components.
*)

ProcedureInterface = TLA + RPCMemoryParams +

types
  (* type of channels with argument type 'a and return type 'r.
     we model a channel as an array of variables (of type chan) 
     rather than a single array-valued variable because the 
     notation gets a little simpler.
  *)
  ('a,'r) chan
  ('a,'r) channel = (PrIds => ('a,'r) chan) stfun

arities
  chan :: (term,term) term

consts
  (* data-level functions *)
  cbit,rbit	:: "('a,'r) chan => bit"
  arg           :: "('a,'r) chan => 'a"
  res           :: "('a,'r) chan => 'r"

  (* state functions *)
  caller	:: "('a,'r) channel => (PrIds => (bit * 'a)) stfun"
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
  "_slice"     :: [lift, 'a] => lift       ("(_!_)" [70,70] 70)

  "_Call"     :: ['a, 'b, lift] => lift    ("(Call _ _ _)" [90,90,90] 90)
  "_Return"   :: ['a, 'b, lift] => lift    ("(Return _ _ _)" [90,90,90] 90)

translations
  "_slice"  ==  "slice"

  "_Call"   ==  "ACall"
  "_Return" ==  "AReturn"

rules
  slice_def     "(PRED (x!i)) s == x s i"

  caller_def	"caller ch   == %s p. (cbit (ch s p), arg (ch s p))"
  rtrner_def	"rtrner ch   == %s p. (rbit (ch s p), res (ch s p))"

  Calling_def	"Calling ch p  == PRED cbit< ch!p > ~= rbit< ch!p >"
  Call_def      "(ACT Call ch p v)   == ACT  ~ $Calling ch p
                                     & (cbit<ch!p>` ~= $rbit<ch!p>)
                                     & (arg<ch!p>` = $v)"
  Return_def    "(ACT Return ch p v) == ACT  $Calling ch p
                                     & (rbit<ch!p>` = $cbit<ch!p>)
                                     & (res<ch!p>` = $v)"
  PLegalCaller_def      "PLegalCaller ch p == TEMP
                             Init(~ Calling ch p)
                             & [][ ? a. Call ch p a ]_((caller ch)!p)"
  LegalCaller_def       "LegalCaller ch == TEMP (! p. PLegalCaller ch p)"
  PLegalReturner_def    "PLegalReturner ch p == TEMP
                                [][ ? v. Return ch p v ]_((rtrner ch)!p)"
  LegalReturner_def     "LegalReturner ch == TEMP (! p. PLegalReturner ch p)"

end


