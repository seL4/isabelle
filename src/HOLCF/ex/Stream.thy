(*  Title: 	FOCUS/Stream.thy
    ID:         $ $
    Author: 	Franz Regensburger, David von Oheimb
    Copyright   1993, 1995 Technische Universitaet Muenchen

general Stream domain
*)

Stream = HOLCF + 

domain 'a stream = "&&" (ft::'a) (lazy rt::'a stream) (infixr 65)

end


