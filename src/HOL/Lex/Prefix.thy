(*  Title:      HOL/Lex/Prefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM
*)

Prefix = Main +

instance list :: (term)ord

defs
        prefix_def        "xs <= zs  ==  ? ys. zs = xs@ys"

        strict_prefix_def "xs < zs  ==  xs <= zs & xs ~= (zs::'a list)"
  
end
