(*  Title:      Option.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Datatype 'a option
*)

Option = Arith +
datatype 'a option = None | Some('a)
end
