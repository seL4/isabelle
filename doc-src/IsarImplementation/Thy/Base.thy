theory Base
imports Main
uses "../../antiquote_setup.ML"
begin

(* FIXME move to src/Pure/ML/ml_antiquote.ML *)
ML {*
  ML_Antiquote.inline "assert"
    (Scan.succeed "(fn b => if b then () else raise General.Fail \"Assertion failed\")")
*}

end
