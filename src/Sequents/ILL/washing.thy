

(* code by Sara Kalvala, based on Paulson's LK 
                           and Moore's tisl.ML *)

washing = ILL +

consts

dollar,quarter,loaded,dirty,wet,clean        :: "o"			

  
rules


  change
  "dollar |- (quarter >< quarter >< quarter >< quarter)"

  load1
  "quarter , quarter , quarter , quarter , quarter |- loaded"

  load2
  "dollar , quarter |- loaded"

  wash
  "loaded , dirty |- wet"

  dry
  "wet, quarter , quarter , quarter |- clean"

end

  