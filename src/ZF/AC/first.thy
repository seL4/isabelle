(*  Title: 	ZF/AC/first.thy
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

Theory helpful in proofs using first element of a well ordered set
*)

first = Order +

consts

  first                   :: "[i, i, i] => o"
  exists_first            :: "[i, i] => o"

defs

  first_def                "first(u, X, R)   \
\			    == u:X & (ALL v:X. v~=u --> <u,v> : R)"

  exists_first_def         "exists_first(X,R)   \
\			    == EX u:X. first(u, X, R)"

end