types
('a, 'b) "л"          (infixr 5)

syntax
  "Ъ"		:: "['a::{}, 'a] => prop"       ("(_ Ъ/ _)"         [3, 2] 2)
  "кл"		:: "[prop, prop] => prop"	("(_ кл/ _)"        [2, 1] 1)
  "Gbigimpl"	:: "[asms, prop] => prop"	("((3Л _ М) кл/ _)" [0, 1] 1)
  "Gall"	:: "('a => prop) => prop"	(binder "Д"                0)

  "Glam"         :: "[idts, 'a::logic] => 'b::logic"  ("(3і_./ _)" 10)
  "Ы"           :: "['a, 'a] => bool"                 (infixl 50)
  "Gnot"        :: "bool => bool"                     ("ї _" [40] 40)
  "GEps"        :: "[pttrn, bool] => 'a"               ("(3®_./ _)" 10)
  "GAll"        :: "[idts, bool] => bool"             ("(3В_./ _)" 10)
  "GEx"         :: "[idts, bool] => bool"             ("(3Г_./ _)" 10)
  "GEx1"        :: "[idts, bool] => bool"             ("(3Г!_./ _)" 10)
  "А"           :: "[bool, bool] => bool"             (infixr 35)
  "Б"           :: "[bool, bool] => bool"             (infixr 30)
  "зи"          :: "[bool, bool] => bool"             (infixr 25)

translations
(type)  "x л y"	== (type) "x => y" 

(*  "іx.t"	=> "%x.t" *)

  "x Ы y"	== "x ~= y"
  "ї y"		== "~y"
  "®x.P"	== "@x.P"
  "Вx.P"	== "! x. P"
  "Гx.P"	== "? x. P"
  "Г!x.P"	== "?! x. P"
  "x А y"	== "x & y"
  "x Б y"	== "x | y"
  "x зи y"	== "x --> y"
