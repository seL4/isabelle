
(* $Id$ *)

header {* Demonstrating the interface SVC *}

theory svc_test
imports SVC_Oracle
begin

syntax
  "<->" :: "[bool, bool] => bool"    (infixr 25)

translations
  "x <-> y" => "x = y"

end
