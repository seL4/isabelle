types

('a, 'b) "è"          (infixr 5)

syntax
	Gfabs	:: "('a => 'b)=>('a -> 'b)"	(binder "¤" 10)

translations

(type)  "x è y"	== (type) "x -> y" 

