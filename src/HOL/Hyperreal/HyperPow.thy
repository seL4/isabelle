(*  Title       : HyperPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Powers theory for hyperreals
*)

HyperPow = HRealAbs + HyperNat + RealPow +  

(** First: hypnat is linearly ordered **)

instance hypnat :: order (hypnat_le_refl,hypnat_le_trans,hypnat_le_anti_sym,
                          hypnat_less_le)
instance hypnat :: linorder (hypnat_le_linear)

instance hypnat :: plus_ac0(hypnat_add_commute,hypnat_add_assoc,
                            hypnat_add_zero_left)


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
             hyprel``{%n::nat. (X n) ^ (Y n)})"
end
