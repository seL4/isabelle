Vimage = Set +

consts
  "-``"          :: ['a => 'b, 'b set] => ('a set)   (infixr 90)

defs
  vimage_def     "f-``B           == {x. f(x) : B}"

end
