(*  Title:      HOLCF/IOA/meta_theory/Compositionality.thy
    ID:        
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Compositionality of I/O automata
*) 

Compositionality = CompoTraces + 

rules 

compotraces
"[| compat_ioas A B; compat_ioas B A; 
    is_asig(asig_of A); is_asig(asig_of B)|] 
 ==> traces(A||B) = 
     {tr. (Filter (%a.a:act A)`tr : traces A &
      Filter (%a.a:act B)`tr : traces B &
      Forall (%x. x:ext(A||B)) tr)}"

end 