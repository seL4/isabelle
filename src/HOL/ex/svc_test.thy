
svc_test = SVC_Oracle +

syntax
    "<->"         :: [bool, bool] => bool                  (infixr 25)

translations
  "x <-> y" => "x = y"

end
