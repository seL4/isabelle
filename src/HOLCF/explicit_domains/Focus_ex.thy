(*
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen

*)

(* Specification of the following loop back device


          g 
           --------------------
          |      -------       |
       x  |     |       |      |  y
    ------|---->|       |------| ----->        
          |  z  |   f   | z    |
          |  -->|       |---   |
          | |   |       |   |  |
          | |    -------    |  |
          | |               |  |
          |  <--------------   |
          |                    | 
           --------------------


First step: Notation in Agent Network Description Language (ANDL)
-----------------------------------------------------------------

agent f
	input  channel i1:'b i2: ('b,'c) tc
	output channel o1:'c o2: ('b,'c) tc
is
	Rf(i1,i2,o1,o2)  (left open in the example)
end f

agent g
	input  channel x:'b 
	output channel y:'c 
is network
	<y,z> = f`<x,z>
end network
end g


Remark: the type of the feedback depends at most on the types of the input and
        output of g. (No type miracles inside g)

Second step: Translation of ANDL specification to HOLCF Specification
---------------------------------------------------------------------

Specification of agent f ist translated to predicate is_f

is_f :: ('b stream * ('b,'c) tc stream -> 
		'c stream * ('b,'c) tc stream) => bool

is_f f  = ! i1 i2 o1 o2. 
	f`<i1,i2> = <o1,o2> --> Rf(i1,i2,o1,o2)

Specification of agent g is translated to predicate is_g which uses
predicate is_net_g

is_net_g :: ('b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) =>
	    'b stream => 'c stream => bool

is_net_g f x y = 
	? z. <y,z> = f`<x,z> &
	! oy hz. <oy,hz> = f`<x,hz> --> z << hz 


is_g :: ('b stream -> 'c stream) => bool

is_g g  = ? f. is_f f  & (! x y. g`x = y --> is_net_g f x y
	  
Third step: (show conservativity)
-----------

Suppose we have a model for the theory TH1 which contains the axiom

	? f. is_f f 

In this case there is also a model for the theory TH2 that enriches TH1 by
axiom

	? g. is_g g 

The result is proved by showing that there is a definitional extension
that extends TH1 by a definition of g.


We define:

def_g g  = 
         (? f. is_f f  & 
	      g = (LAM x. cfst`(f`<x,fix`(LAM k.csnd`(f`<x,k>))>)) )
	
Now we prove:

	(?f. is_f f ) --> (? g. is_g g) 

using the theorems

loopback_eq)	def_g = is_g			(real work) 

L1)		(? f. is_f f ) --> (? g. def_g g)  (trivial)

*)

Focus_ex = Stream +

types  tc 2

arities tc:: (pcpo,pcpo)pcpo

consts

is_f     ::
 "('b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) => bool"
is_net_g :: "('b stream *('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) =>
	    'b stream => 'c stream => bool"
is_g     :: "('b stream -> 'c stream) => bool"
def_g    :: "('b stream -> 'c stream) => bool"
Rf	 :: 
"('b stream * ('b,'c) tc stream * 'c stream * ('b,'c) tc stream) => bool"

defs

is_f		"is_f f == (! i1 i2 o1 o2.
			f`<i1,i2> = <o1,o2> --> Rf(i1,i2,o1,o2))"

is_net_g	"is_net_g f x y == (? z. 
			<y,z> = f`<x,z> &
			(! oy hz. <oy,hz> = f`<x,hz> --> z << hz))" 

is_g		"is_g g  == (? f.
			is_f f  & 
			(!x y. g`x = y --> is_net_g f x y))"


def_g		"def_g g == (? f.
			is_f f  & 
	      		g = (LAM x. cfst`(f`<x,fix`(LAM k.csnd`(f`<x,k>))>)))" 

end
