types

('a, 'b) "ò"          (infixr 20)

translations

(type)  "x ò y"	== (type) "x * y" 

  "³(x,y,zs).b"   == "split(³x.³(y,zs).b)"
  "³(x,y).b"      == "split(³x y.b)"

