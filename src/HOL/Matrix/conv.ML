exception Fail_conv;

fun orelsec conv1 conv2 ct = conv1 ct handle Fail_conv => conv2 ct

val allc = Thm.reflexive

fun thenc conv1 conv2 ct = 
    let 
	fun rhs_of t = snd (Thm.dest_comb (strip_imp_concl (cprop_of t)))
	    
	val eq = conv1 ct
    in
	Thm.transitive eq (conv2 (rhs_of eq))
    end

fun subc conv ct = 
    case term_of ct of
	_ $ _ => 
	let 
	    val (ct1, ct2) = Thm.dest_comb ct
	in
	    Thm.combination (conv ct1) (conv ct2)
	end
      | _ => allc ct

fun botc conv ct = thenc (subc (botc conv)) (orelsec conv allc) ct