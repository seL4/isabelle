(*  Title:      ZF/AC/first.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Theory helpful in proofs using first element of a well ordered set
*)

first = Order +

consts

  first                   :: [i, i, i] => o

defs

  first_def                "first(u, X, R) 
                            == u:X & (ALL v:X. v~=u --> <u,v> : R)"
end
