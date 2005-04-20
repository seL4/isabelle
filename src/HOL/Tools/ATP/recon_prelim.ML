

Goal "A -->A";
by Auto_tac;
qed "foo";


val Mainsign = #sign (rep_thm foo);



val gcounter = ref 0; 


fun USYN_ERR func mesg = Utils.ERR {module = "USyntax", func = func, mesg = mesg};

fun dest_neg(Const("Not",_) $ M) = M
  | dest_neg _ = raise USYN_ERR "dest_neg" "not a negation";


fun iscomb a = if is_Free a then
			false
	      else if is_Var a then
			false
		else if USyntax.is_conj a then
			false
		else if USyntax.is_disj a then
			false
		else if USyntax.is_forall a then
			false
		else if USyntax.is_exists a then
			false
		else
			true;
fun getstring (Var (v,T)) = fst v
   |getstring (Free (v,T))= v;



fun alltrue [] = true
   |alltrue (true::xs) = true andalso (alltrue xs)
   |alltrue (false::xs) = false;

fun allfalse [] = true
   |allfalse (false::xs) = true andalso (allfalse xs)
   |allfalse (true::xs) = false;

fun not_empty [] = false 
    | not_empty _ = true;

fun twoisvar (a,b) = is_Var b;
fun twoisfree (a,b) = is_Free b;
fun twoiscomb (a,b) = iscomb b;

fun strequalfirst a (b,c) = (getstring a) = (getstring b);

fun fstequal a b = a = fst b;

fun takeout (i,[])  = []
   | takeout (i,(x::xs)) = if (i>0) then
                               (x::(takeout(i-1,xs)))
                           else
                               [];
		


(* Presumably here, we would allow is_Var f for doing HOL, i.e. can subst for propositions *)
fun is_Abs (Abs _) = true
  | is_Abs _ = false;
fun is_Bound (Bound _) = true
  | is_Bound _ = false;




fun is_hol_tm t =
                if (is_Free t) then 
                        true 
                else if (is_Var t) then
                        true
                else if (is_Const t) then
                        true
                else if (is_Abs t) then
                        true
                else if (is_Bound t) then
                        true
                else 
                        let val (f, args) = strip_comb t in
                            if ((is_Free f) orelse (is_Var f)) andalso (alltrue (map is_hol_tm args)) then 
                                true            (* should be is_const *)
                            else 
                                false
                       end;

fun is_hol_fm f =  if USyntax.is_neg f then
                        let val newf = USyntax.dest_neg f in
                            is_hol_fm newf
                        end
                    
               else if USyntax.is_disj f then
                        let val {disj1,disj2} = USyntax.dest_disj f in
                            (is_hol_fm disj1) andalso (is_hol_fm disj2)  (* shouldn't this be and ? *)
                        end 
               else if USyntax.is_conj f then
                        let val {conj1,conj2} = USyntax.dest_conj f in
                            (is_hol_fm conj1) andalso (is_hol_fm conj2)
                        end 
               else if (USyntax.is_forall f) then
                        let val {Body, Bvar} = USyntax.dest_forall f in
                            is_hol_fm Body
                        end
               else if (USyntax.is_exists f) then
                        let val {Body, Bvar} = USyntax.dest_exists f in
                            is_hol_fm Body
                        end
               else if (iscomb f) then
                        let val (P, args) = strip_comb f in
                            ((is_hol_tm P)) andalso (alltrue (map is_hol_fm args))
                        end
                else
                        is_hol_tm f;                              (* should be is_const, nee
d to check args *)
               

fun hol_literal t = 
   (is_hol_fm t) andalso 
   ( not ((USyntax.is_conj t) orelse (USyntax.is_disj t) orelse (USyntax.is_forall t) orelse (USyntax.is_exists t)));




(*PROBLEM HERE WITH THINGS THAT HAVE TWO RANDS e.g. P x y *)
fun getcombvar a = let val {Rand = rand, Rator = rator} = USyntax.dest_comb a in
			if (iscomb rand) then
				getcombvar rand
			else
				rand
		   end;



fun free2var v = let val thing = dest_Free v 
                     val (name,vtype) = thing
                     val index = (name,0) in
                     Var (index,vtype)
                 end;

fun var2free v = let val (index, tv) = dest_Var v 
                     val istr = fst index in
                     Free (istr,tv)
                 end;

fun  inlist v [] = false
    | inlist v (first::rest) = if first = v then
				true
			     else inlist v rest;

(*fun in_vars v [] = false
    | in_vars v ((a,b)::rest) = if v = a then
				  true
			       else if v = b then
				  true
			       else in_vars v rest;*)

fun in_vars v [] = false
    | in_vars v (a::rest) = if (fst v) = a then
				  true
			      
			       else in_vars v rest;

fun equalpair (a,b) (c,d) = if (a,b)= (c,d) then
					true
			    else if (a,b) = (d,c) then
					true
			    else false;


fun is_empty_seq thisseq =  case Seq.chop (1, thisseq) of
                             ([],_)   => true
                           |      _   => false

fun getnewenv thisseq = 
			   let val seqlist = Seq.list_of thisseq
			   val envpair =hd seqlist in
			   fst envpair 
			end;

fun getnewsubsts thisseq =  let val seqlist = Seq.list_of thisseq
			   val envpair =hd seqlist in
			   snd envpair 
			end;



fun prover s = prove_goal HOL.thy s (fn _ => [blast_tac HOL_cs 1]);


exception  powerError;

fun power (x, n) =  if x = 0 andalso n = 0 
                    then raise powerError
                    else  if n = 0 
                          then 1
                          else x * power (x, n-1);


fun get_tens n = power(10, (n-1))


fun digits_to_int [] posn  n = n
|   digits_to_int (x::xs) posn  n = let 
				        val digit_val = ((ord x) - 48)*(get_tens posn)
          		            in
                                        digits_to_int xs (posn -1 )(n + digit_val) 
         		            end;

fun int_of_string str = let 
			   val digits = explode str
                           val posn   = length digits
                        in 
		            digits_to_int digits posn 0
                        end
                	
 
exception ASSERTION of string;
