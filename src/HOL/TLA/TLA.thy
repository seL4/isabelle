(* 
    File:        TLA/TLA.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: TLA
    Logic Image: HOL

The temporal level of TLA.
*)

TLA  =  Action + WF_Rel +

types
    behavior
    temporal = "behavior form"

arities
    behavior :: world

consts
  (* get first 2 states of behavior *)
  fst_st     :: "behavior => state"
  snd_st     :: "behavior => state"
  
  Init       :: "action => temporal"
                 (* define Box and Dmd for both actions and temporals *)
  Box        :: "('w::world) form => temporal"      ("([](_))" [40] 40)
  Dmd        :: "('w::world) form => temporal"      ("(<>(_))" [40] 40)
  "~>"       :: "[action,action] => temporal"       (infixr 22)
  stable     :: "action => temporal"
  WF         :: "[action,'a stfun] => temporal"    ("(WF'(_')'_(_))" [0,60] 55)
  SF         :: "[action,'a stfun] => temporal"    ("(SF'(_')'_(_))" [0,60] 55)

  (* Quantification over (flexible) state variables *)
  EEx        :: "('a stfun => temporal) => temporal"    (binder "EEX " 10)
  AAll       :: "('a stfun => temporal) => temporal"    (binder "AALL " 10)

translations
  "sigma |= Init(A)"      == "Init A sigma"
  "sigma |= Box(F)"       == "Box F sigma"
  "sigma |= Dmd(F)"       == "Dmd F sigma"
  "sigma |= F ~> G"       == "op ~> F G sigma"
  "sigma |= stable(A)"    == "stable A sigma"
  "sigma |= WF(A)_v"      == "WF A v sigma"
  "sigma |= SF(A)_v"      == "SF A v sigma"

rules
  dmd_def    "(<>F) == .~[].~F"
  boxact_def "([](F::action)) == ([] Init F)"
  leadsto    "P ~> Q == [](Init(P) .-> <>Q)"
  stable_def "stable P == [](P .-> P`)"

  WF_def     "WF(A)_v == <>[] $(Enabled(<A>_v)) .-> []<><A>_v"
  SF_def     "SF(A)_v == []<> $(Enabled(<A>_v)) .-> []<><A>_v"

  Init_def   "(sigma |= Init(F)) == ([[fst_st sigma, snd_st sigma]] |= F)"

(* The following axioms are written "polymorphically", not just for temporal formulas. *)
  normalT    "[](F .-> G) .-> ([]F .-> []G)"
  reflT      "[]F .-> F"         (* F::temporal *)
  transT     "[]F .-> [][]F"
  linT       "(<>F) .& (<>G) .-> (<>(F .& <>G)) .| (<>(G .& <>F))"   (* F,G::temporal *)
  discT      "[](F .-> <>(.~F .& <>F)) .-> (F .-> []<>F)"
  primeI     "[]P .-> Init(P`)"
  primeE     "[](Init(P) .-> []F) .-> Init(P`) .-> (F .-> []F)"
  indT       "[](Init(P) .& .~[]F .-> Init(P`) .& F) .-> Init(P) .-> []F"
  allT       "(RALL x. [](F(x))) .= ([](RALL x. F(x)))"

  necT       "F ==> []F"

(* Flexible quantification: refinement mappings, history variables *)
  aall_def      "(AALL x. F(x)) == .~ (EEX x. .~ F(x))"
  eexI          "F x .-> (EEX x. F x)"
  historyI      "[| sigma |= Init(I); sigma |= []N;
                    (!!h s t. (h s = ha s t) & I [[s,t]] --> HI(h)[[s,t]]);
                    (!!h s t. (h t = hc s t (h s)) & N [[s,t]] --> HN(h) [[s,t]])
                 |] ==> sigma |= (EEX h. Init(HI(h)) .& []HN(h))"
  eexE          "[| sigma |= (EEX x. F x);
		    (!!x. [| base_var x; (sigma |= F x) |] ==> (G sigma)::bool) 
		 |] ==> G sigma"

end

ML
