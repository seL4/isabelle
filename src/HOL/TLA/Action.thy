(* 
    File:	 TLA/Action.thy
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

    Theory Name: Action
    Logic Image: HOL

Define the action level of TLA as an Isabelle theory.
*)

Action  =  Intensional + Stfun +

(** abstract syntax **)

types
  'a trfun = "(state * state) => 'a"
  action   = bool trfun

instance
  "*" :: (world, world) world

consts
  (** abstract syntax **)
  before        :: 'a stfun => 'a trfun
  after         :: 'a stfun => 'a trfun
  unch          :: 'a stfun => action

  SqAct         :: [action, 'a stfun] => action
  AnAct         :: [action, 'a stfun] => action
  enabled       :: action => stpred

(** concrete syntax **)

syntax
  (* Syntax for writing action expressions in arbitrary contexts *)
  "ACT"         :: lift => 'a                      ("(ACT _)")

  "_before"     :: lift => lift                    ("($_)"  [100] 99)
  "_after"      :: lift => lift                    ("(_$)"  [100] 99)
  "_unchanged"  :: lift => lift                    ("(unchanged _)" [100] 99)

  (*** Priming: same as "after" ***)
  "_prime"      :: lift => lift                    ("(_`)" [100] 99)

  "_SqAct"      :: [lift, lift] => lift            ("([_]'_(_))" [0,1000] 99)
  "_AnAct"      :: [lift, lift] => lift            ("(<_>'_(_))" [0,1000] 99)
  "_Enabled"    :: lift => lift                    ("(Enabled _)" [100] 100)

translations
  "ACT A"            =>   "(A::state*state => _)"
  "_before"          ==   "before"
  "_after"           ==   "after"
  "_prime"           =>   "_after"
  "_unchanged"       ==   "unch"
  "_SqAct"           ==   "SqAct"
  "_AnAct"           ==   "AnAct"
  "_Enabled"         ==   "enabled"
  "w |= [A]_v"       <=   "_SqAct A v w"
  "w |= <A>_v"       <=   "_AnAct A v w"
  "s |= Enabled A"   <=   "_Enabled A s"
  "w |= unchanged f" <=   "_unchanged f w"

rules
  unl_before    "(ACT $v) (s,t) == v s"
  unl_after     "(ACT v$) (s,t) == v t"

  unchanged_def "(s,t) |= unchanged v == (v t = v s)"
  square_def    "ACT [A]_v == ACT (A | unchanged v)"
  angle_def     "ACT <A>_v == ACT (A & ~ unchanged v)"

  enabled_def   "s |= Enabled A  ==  EX u. (s,u) |= A"
end


