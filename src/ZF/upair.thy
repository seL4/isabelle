(*  Title:      ZF/upair.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

theory upair = ZF
files "Tools/typechk":

setup TypeCheck.setup
declare atomize_ball [symmetric, rulify]

end
