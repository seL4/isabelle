(* 
    File:        TLA/TLA.thy
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

    Theory Name: TLA
    Logic Image: HOL

The temporal level of TLA.
*)

TLA  =  Init +

consts
  (** abstract syntax **)
  Box        :: ('w::world) form => temporal
  Dmd        :: ('w::world) form => temporal
  leadsto    :: ['w::world form, 'v::world form] => temporal
  Stable     :: stpred => temporal
  WF         :: [action, 'a stfun] => temporal
  SF         :: [action, 'a stfun] => temporal

  (* Quantification over (flexible) state variables *)
  EEx        :: ('a stfun => temporal) => temporal       (binder "Eex " 10)
  AAll       :: ('a stfun => temporal) => temporal       (binder "Aall " 10)

  (** concrete syntax **)
syntax
  "_Box"     :: lift => lift                        ("([]_)" [40] 40)
  "_Dmd"     :: lift => lift                        ("(<>_)" [40] 40)
  "_leadsto" :: [lift,lift] => lift                 ("(_ ~> _)" [23,22] 22)
  "_stable"  :: lift => lift                        ("(stable/ _)")
  "_WF"      :: [lift,lift] => lift                 ("(WF'(_')'_(_))" [0,60] 55)
  "_SF"      :: [lift,lift] => lift                 ("(SF'(_')'_(_))" [0,60] 55)

  "_EEx"     :: [idts, lift] => lift                ("(3EEX _./ _)" [0,10] 10)
  "_AAll"    :: [idts, lift] => lift                ("(3AALL _./ _)" [0,10] 10)

translations
  "_Box"      ==   "Box"
  "_Dmd"      ==   "Dmd"
  "_leadsto"  ==   "leadsto"
  "_stable"   ==   "Stable"
  "_WF"       ==   "WF"
  "_SF"       ==   "SF"
  "_EEx v A"  ==   "Eex v. A"
  "_AAll v A" ==   "Aall v. A"

  "sigma |= []F"         <= "_Box F sigma"
  "sigma |= <>F"         <= "_Dmd F sigma"
  "sigma |= F ~> G"      <= "_leadsto F G sigma"
  "sigma |= stable P"    <= "_stable P sigma"
  "sigma |= WF(A)_v"     <= "_WF A v sigma"
  "sigma |= SF(A)_v"     <= "_SF A v sigma"
  "sigma |= EEX x. F"    <= "_EEx x F sigma"
  "sigma |= AALL x. F"    <= "_AAll x F sigma"

syntax (xsymbols)
  "_Box"     :: lift => lift                        ("(\\<box>_)" [40] 40)
  "_Dmd"     :: lift => lift                        ("(\\<diamond>_)" [40] 40)
  "_leadsto" :: [lift,lift] => lift                 ("(_ \\<leadsto> _)" [23,22] 22)
  "_EEx"     :: [idts, lift] => lift                ("(3\\<exists>\\<exists> _./ _)" [0,10] 10)
  "_AAll"    :: [idts, lift] => lift                ("(3\\<forall>\\<forall> _./ _)" [0,10] 10)

rules
  (* Definitions of derived operators *)
  dmd_def      "TEMP <>F  ==  TEMP ~[]~F"
  boxInit      "TEMP []F  ==  TEMP []Init F"
  leadsto_def  "TEMP F ~> G  ==  TEMP [](Init F --> <>G)"
  stable_def   "TEMP stable P  ==  TEMP []($P --> P$)"
  WF_def       "TEMP WF(A)_v  ==  TEMP <>[] Enabled(<A>_v) --> []<><A>_v"
  SF_def       "TEMP SF(A)_v  ==  TEMP []<> Enabled(<A>_v) --> []<><A>_v"
  aall_def     "TEMP (AALL x. F x)  ==  TEMP ~ (EEX x. ~ F x)"

(* Base axioms for raw TLA. *)
  normalT    "|- [](F --> G) --> ([]F --> []G)"    (* polymorphic *)
  reflT      "|- []F --> F"         (* F::temporal *)
  transT     "|- []F --> [][]F"     (* polymorphic *)
  linT       "|- <>F & <>G --> (<>(F & <>G)) | (<>(G & <>F))"
  discT      "|- [](F --> <>(~F & <>F)) --> (F --> []<>F)"
  primeI     "|- []P --> Init P`"
  primeE     "|- [](Init P --> []F) --> Init P` --> (F --> []F)"
  indT       "|- [](Init P & ~[]F --> Init P` & F) --> Init P --> []F"
  allT       "|- (ALL x. [](F x)) = ([](ALL x. F x))"

  necT       "|- F ==> |- []F"      (* polymorphic *)

(* Flexible quantification: refinement mappings, history variables *)
  eexI       "|- F x --> (EEX x. F x)"
  eexE       "[| sigma |= (EEX x. F x); basevars vs;
		 (!!x. [| basevars (x, vs); sigma |= F x |] ==> (G sigma)::bool) 
	      |] ==> G sigma"
  history    "|- EEX h. Init(h = ha) & [](!x. $h = #x --> h` = hb x)"
end
