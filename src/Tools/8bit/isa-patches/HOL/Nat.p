syntax
  "Gmu"	:: (nat => bool) => nat				(binder "´" 10)

translations
  "´x.P"	== "LEAST x. P"
