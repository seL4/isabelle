(*  Title:      HOLCF/IOA/ABP/Action.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

The set of all actions of the system
*)

Action =  Main +
datatype action = New  | Loc nat | Free nat        
end
