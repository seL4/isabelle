(*  Title:      HOL/Lex/Prefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM
*)

Prefix = List +

arities list :: (term)ord

defs
        prefix_def     "xs <= zs  ==  ? ys. zs = xs@ys"
end
