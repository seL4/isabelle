(*  Title       : HyperPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Powers theory for hyperreals
*)

HyperPow = HRealAbs + HyperNat + RealPow +  

instance hypreal :: {power}

consts hpowr :: "[hypreal,nat] => hypreal"  
primrec
     hpowr_0   "r ^ 0       = 1hr"
     hpowr_Suc "r ^ (Suc n) = (r::hypreal) * (r ^ n)"

consts
  "pow"  :: [hypreal,hypnat] => hypreal     (infixr 80)

defs

  (* hypernatural powers of hyperreals *)
  hyperpow_def
  "(R::hypreal) pow (N::hypnat) 
      == Abs_hypreal(UN X:Rep_hypreal(R). UN Y: Rep_hypnat(N).
             hyprel^^{%n::nat. (X n) ^ (Y n)})"
end
