(* basic examples *)

Test = HOHH +

types nat
arities nat :: term

types 'a list
arities list :: (term) term

consts Nil   :: 'a list		 	 		 ("[]")
       Cons  :: 'a => 'a list => 'a list		 (infixr "#"  65)

syntax
  (* list Enumeration *)
  "@list"     :: args => 'a list                          ("[(_)]")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

types   person
arities person  :: term

consts  
	append  :: ['a list, 'a list, 'a list]		  => bool
	reverse :: ['a list, 'a list]			  => bool

	mappred	:: [('a => 'b => bool), 'a list, 'b list] => bool
	mapfun	:: [('a => 'b), 'a list, 'b list]	  => bool

	bob	:: person
	sue	:: person
	ned	:: person

	"23"	:: nat		("23")
	"24"	:: nat		("24")
	"25"	:: nat		("25")

	age	:: [person, nat]			  => bool

	eq	:: ['a, 'a]				  => bool

	empty	:: ['b]					  => bool
	add	:: ['a, 'b, 'b]				  => bool
	remove	:: ['a, 'b, 'b]				  => bool
	bag_appl:: ['a, 'a, 'a, 'a]			  => bool

rules   append	"append  []    xs  xs    ..
		 append (x#xs) ys (x#zs) :- append xs ys zs"
	reverse "reverse L1 L2 :- (!rev_aux. 
		  (!L.          rev_aux  []    L  L )..
		  (!X L1 L2 L3. rev_aux (X#L1) L2 L3 :- rev_aux L1 L2 (X#L3))
		  => rev_aux L1 L2 [])"

	mappred "mappred P  []     []    ..
		 mappred P (x#xs) (y#ys) :- P x y  &  mappred P xs ys"
	mapfun  "mapfun f  []     []      ..
		 mapfun f (x#xs) (f x#ys) :- mapfun f xs ys"

	age     "age bob 24 ..
		 age sue 23 ..
		 age ned 23"

	eq	"eq x x"

(* actual definitions of empty and add is hidden -> yields abstract data type *)

	bag_appl"bag_appl A B X Y:- (? S1 S2 S3 S4 S5.
				empty    S1    &
				add A    S1 S2 &
				add B    S2 S3 &
				remove X S3 S4 &
				remove Y S4 S5 &
				empty    S5)"
end
