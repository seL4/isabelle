(*  Title:      HOLCF/Discrete0.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM

Discrete CPOs
*)

Discrete0 = Cont +

datatype 'a discr = Discr 'a

instance discr :: (term)sq_ord

defs
less_discr_def "((op <<)::('a::term)discr=>'a discr=>bool)  ==  op ="

end
