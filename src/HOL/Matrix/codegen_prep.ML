structure codegen_prep = 
struct

exception Prepare_thms of string;

fun is_meta_eq th =
    let
	fun check ((Const ("==", _)) $ _ $ _) = true
	  | check _ = false
    in
	check (concl_of th)
    end

fun printty ty = 
    let
	fun immerse s [] = []
	  | immerse s [x] = [x]
	  | immerse s (x::xs) = x::s::(immerse s xs)

	fun py t = 
	    let
		val (name, args) =  dest_Type t
		val args' = map printty args
	    in
		concat (immerse "_" (name::args'))
	    end

	val (args, res) = strip_type ty
	val tystrs = map py (args@[res])
			  
	val s = "'"^(concat (immerse "_" tystrs))^"'"
    in
	s
    end

fun head_name th = 
    let val s = 
	    let
		val h = fst (strip_comb (hd (snd (strip_comb (concl_of th)))))
		val n = fst (dest_Const h)
		val ty = snd (dest_Const h)
		val hn = fst (dest_Const h)
	    in
		hn^"_"^(printty ty) handle _ => (writeln ("warning: polymorphic "^hn); hn)	
	    end
    in
	s
    end
	    
val mangle_id  = 
    let
	fun tr #"=" = "_eq_"
	  | tr #"." = "_"
	  | tr #" " = "_"
	  | tr #"<" = "_le_"
	  | tr #">" = "_ge_"
	  | tr #"(" = "_bro_"
	  | tr #")" = "_brc_"
	  | tr #"+" = "_plus_"
	  | tr #"*" = "_mult_"
	  | tr #"-" = "_minus_"
	  | tr #"|" = "_or_"
	  | tr #"&" = "_and_"
	  | tr x = Char.toString x
	fun m s = "simp_"^(String.translate tr s)
    in
	m
    end

fun group f [] = []
  | group f (x::xs) = 
    let
	val g = group f xs
	val key = f x
    in
	case assoc (g, key) of
	    NONE => (key, [x])::g
	  | SOME l => overwrite (g, (key, x::l))
    end
    
fun prepare_thms ths = 
    let
	val ths = (List.filter is_meta_eq ths) @ (map (standard o mk_meta_eq) (filter_out is_meta_eq ths))		      
	val _ = if forall Thm.no_prems ths then () else raise (Prepare_thms "premisse found")
	val thmgroups = group head_name ths
	val test_clashgroups = group (fn (a,b) => mangle_id a) thmgroups
	val _ = if (length thmgroups <> length test_clashgroups) then raise (Prepare_thms "clash after name mangling") else ()	
		
	fun prep (name, ths) = 
	    let
		val m = mangle_id name
			
	    in
		(m, true, ths)
	    end
	    
	val thmgroups = map prep thmgroups
    in
	(thmgroups)
    end
    
fun writestr filename s = 
    let 
	val f = TextIO.openOut filename
	val _ = TextIO.output(f, s)
	val _ = TextIO.closeOut f
    in 
	() 
    end
end
