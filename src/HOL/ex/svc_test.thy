svc_test = Main +

syntax
    "<->"         :: [bool, bool] => bool                  (infixr 25)

translations
  "x <-> y" => "x = y"

end
