signature Mask_sig =
sig
 datatype 'a binding = |-> of ('a * 'a)  (* infix 7 |->; *)

 type mask
 val ERR : mask

end
