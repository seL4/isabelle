(*  Title:      HOLCF/Discrete0.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Discrete CPOs.
*)

Discrete0 = Cont + Datatype +

datatype 'a discr = Discr "'a :: term"

instance discr :: (term)sq_ord

defs
less_discr_def "((op <<)::('a::term)discr=>'a discr=>bool)  ==  op ="

end
