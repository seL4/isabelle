(*  Title:	IntPower.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Integer powers 
*)

IntPower = IntDiv + 

instance
  int :: {power}

primrec
  power_0   "p ^ 0 = Numeral1"
  power_Suc "p ^ (Suc n) = (p::int) * (p ^ n)"

end
