(*  Title:      HOLCF/Discrete0.thy
    ID:         $Id$
    Author:     Tobias Nipkow

Discrete CPOs.
*)

Discrete0 = Cont + Datatype +

datatype 'a discr = Discr "'a :: type"

instance discr :: (type) sq_ord

defs
less_discr_def "((op <<)::('a::type)discr=>'a discr=>bool)  ==  op ="

end
