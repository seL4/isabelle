List = FOL +
types 	list 1
arities list	:: (term)term
consts	Nil	:: "'a list"
   	Cons	:: "['a, 'a list] => 'a list" 
end
