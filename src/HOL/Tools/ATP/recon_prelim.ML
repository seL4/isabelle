
open Goals;
open Unify;
open USyntax;
open Utils;
open Envir;
open Tfl;
open Rules;

goal Main.thy "A -->A";
by Auto_tac;
qed "foo";


val Mainsign = #sign (rep_thm foo);



(*val myhol = sign_of thy;*)

val myenv = empty 0;


val gcounter = ref 0; 
      
exception NOMATES;
exception UNMATEABLE;
exception NOTSOME;
exception UNSPANNED;

fun USYN_ERR func mesg = Utils.ERR {module = "USyntax", func = func, mesg = mesg};

fun dest_neg(Const("Not",_) $ M) = M
  | dest_neg _ = raise USYN_ERR "dest_neg" "not a negation";

fun is_abs t = can dest_abs t;
fun is_comb t = can dest_comb t;

fun iscomb a = if is_Free a then
			false
	      else if is_Var a then
			false
		else if is_conj a then
			false
		else if is_disj a then
			false
		else if is_forall a then
			false
		else if is_exists a then
			false
		else
			true;
fun getstring (Var (v,T)) = fst v
   |getstring (Free (v,T))= v;


fun getindexstring ((a:string),(b:int))= a;  

fun getstrings (a,b) = let val astring = getstring a
                           val bstring = getstring b in
                           (astring,bstring)
                       end;


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

fun is_hol_fm f =  if is_neg f then
                        let val newf = dest_neg f in
                            is_hol_fm newf
                        end
                    
               else if is_disj f then
                        let val {disj1,disj2} = dest_disj f in
                            (is_hol_fm disj1) andalso (is_hol_fm disj2)  (* shouldn't this be and ? *)
                        end 
               else if is_conj f then
                        let val {conj1,conj2} = dest_conj f in
                            (is_hol_fm conj1) andalso (is_hol_fm conj2)
                        end 
               else if (is_forall f) then
                        let val {Body, Bvar} = dest_forall f in
                            is_hol_fm Body
                        end
               else if (is_exists f) then
                        let val {Body, Bvar} = dest_exists f in
                            is_hol_fm Body
                        end
               else if (iscomb f) then
                        let val (P, args) = strip_comb f in
                            ((is_hol_tm P)) andalso (alltrue (map is_hol_fm args))
                        end
                else
                        is_hol_tm f;                              (* should be is_const, nee
d to check args *)
               

fun hol_literal t =  (is_hol_fm t) andalso ( not ((is_conj t) orelse (is_disj t) orelse (is_forall t) orelse (is_exists t)));




(*PROBLEM HERE WITH THINGS THAT HAVE TWO RANDS e.g. P x y *)
fun getcombvar a = let val {Rand = rand, Rator = rator} = dest_comb a in
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

fun readnewenv thisenv =let val seqlist = Seq.list_of thisenv
			   val envpair = hd seqlist
			   val env = fst envpair
			   val envlist = alist_of env in
			hd envlist
			end;


fun readenv thisenv = let val envlist = alist_of thisenv in
			
				hd envlist
			end;





fun prover s = prove_goal HOL.thy s (fn _ => [blast_tac HOL_cs 1]);

fun oneofthree (a,b,c) = a;

fun twoofthree (a,b,c) = b;

fun threeofthree (a,b,c) = c;

val my_simps = map prover
 [ "(x=x) = True",
    "(~ ~ P) = P",
   "(~P) ~= P", "P ~= (~P)", "(P ~= Q) = (P = (~Q))",
   
   "(P | P) = P", "(P | (P | Q)) = (P | Q)",
   "((~P) = (~Q)) = (P=Q)" ];


(*val myss = HOL_basic_ss addsimps (my_simps@[not_all, not_ex, de_Morgan_conj, de_Morgan_disj, U_def, intersect_def, setEq_def, proposEq_def, hashset_def, subset_def]@ex_simps @ all_simps);

*)

(*--------------------------*)
(* NNF stuff from meson_tac *)
(*--------------------------*)


(*Prove theorems using fast_tac*)
fun prove_fun s = 
    prove_goal HOL.thy s
         (fn prems => [ cut_facts_tac prems 1, Fast_tac 1 ]);

(*------------------------------------------------------------------------*)
(* Renaming all the bound vars in the term - sort of fake `Skolemisation' *)
(*------------------------------------------------------------------------*)
fun mygenvar ty thisenv =
  let val count = !gcounter
      val genstring = "GEN"^(string_of_int count)^"VAR" in
	    	gcounter := count + 1;
              	genvar genstring (thisenv,ty)
  end;  

fun renameBounds t thisenv = if (is_Var t) orelse (is_Free t) orelse (iscomb t) then
			t
	 	
		else if is_forall t then
			let val {Body, Bvar} = dest_forall t 
                            val newvarenv = mygenvar(type_of Bvar) thisenv
                            val newvar = snd(newvarenv)
                            val newbod = subst_free [(Bvar,newvar)] Body
                            val newbod2 = renameBounds newbod thisenv in
                            mk_forall{Body = newbod2, Bvar = newvar}
                        end
		else if is_exists t then
                        let val {Body, Bvar} =dest_exists t 
			    val newvarenv = mygenvar(type_of Bvar) thisenv
                            val newvar = snd(newvarenv)
                            val newbod = subst_free [(Bvar,newvar)] Body
                            val newbod2 = renameBounds newbod thisenv in
                            mk_exists{Body = newbod2, Bvar = newvar}    
			end
		else if is_conj t then
			let val {conj1,conj2} = dest_conj t
			    val vpl = renameBounds conj1 thisenv
			    val vpr = renameBounds conj2 thisenv in
		            mk_conj {conj1 = vpl, conj2 = vpr}
			end
		else 
			let val {disj1, disj2} = dest_disj t 
			    val vpl = renameBounds disj1 thisenv
			    val  vpr = renameBounds disj2  thisenv in
			    mk_disj {disj1 = vpl,disj2= vpr}  
			end;
                	

(*-----------------*)
(* from hologic.ml *)
(*-----------------*)
val boolT = Type ("bool", []);

val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun eq_const T = Const ("op =", [T, T] ---> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
 | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);


(*-----------------------------------------------------------------------*)
(* Making a THM from a subgoal and other such things                     *)
(*-----------------------------------------------------------------------*)

fun thmfromgoal goalnum = let val mygoal = getgoal goalnum
                              val  mycgoal = cterm_of Mainsign mygoal in
                              assume mycgoal
                          end;

fun termfromgoal goalnum = let val mygoal = getgoal goalnum
                               val {Rand = myra, Rator = myrat} = dest_comb mygoal in
                               myra
                           end;

fun thmfromterm t = let val propterm = mk_Trueprop t 
                        val mycterm = cterm_of Mainsign propterm in
                        assume mycterm
                    end;

fun termfromthm t = let val conc = concl_of t 
                        val {Rand = myra, Rator = myrat} = dest_comb conc in
                        myra
                    end;

fun goalfromterm t = let val pterm = mk_Trueprop t  
                         val ct = cterm_of Mainsign  pterm in
                         goalw_cterm [] ct
                     end;

fun termfromgoalimp goalnum = let val mygoal = getgoal goalnum
                               val {Rand = myra1, Rator = myrat1} = dest_comb mygoal 
                               val  {Rand = myra, Rator = myrat} = dest_comb myra1 in
                               myra
                           end;


fun mkvars (a,b:term) = let val thetype = type_of b 
                           val stringa =( fst a)
                            val newa = Free (stringa, thetype) in
                            (newa,b)
                        end;

fun glue [] thestring = thestring
  |glue (""::[]) thestring = thestring 
  |glue (a::[]) thestring = thestring^" "^a 
  |glue (a::rest) thestring = let val newstring = thestring^" "^a in
                                 glue rest newstring
                             end;

exception STRINGEXCEP;
 
fun getvstring (Var (v,T)) = fst v
   |getvstring (Free (v,T))= v;

  
fun getindexstring ((a:string),(b:int))= a;  

fun getstrings (a,b) = let val astring = getstring a
                           val bstring = getstring b in
                           (astring,bstring)
                       end;
(*
fun getvstrings (a,b) = let val astring = getvstring a
                           val bstring = getvstring b in
                           (astring,bstring)
                       end;
*)
 


(*------------------------------------------------------------------------*)
(* Renaming all the bound vars in the term - sort of fake `Skolemisation' *)
(*------------------------------------------------------------------------*)
fun mygenvar ty thisenv =
  let val count = !gcounter
      val genstring = "GEN"^(string_of_int count)^"VAR" in
	    	gcounter := count + 1;
              	genvar genstring (thisenv,ty)
  end;  

fun renameBounds t thisenv = if (is_Var t) orelse (is_Free t) orelse (iscomb t) then
			t
	 	
		else if is_forall t then
			let val {Body, Bvar} = dest_forall t 
                            val newvarenv = mygenvar(type_of Bvar) thisenv
                            val newvar = snd(newvarenv)
                            val newbod = subst_free [(Bvar,newvar)] Body
                            val newbod2 = renameBounds newbod thisenv in
                            mk_forall{Body = newbod2, Bvar = newvar}
                        end
		else if is_exists t then
                        let val {Body, Bvar} =dest_exists t 
			    val newvarenv = mygenvar(type_of Bvar) thisenv
                            val newvar = snd(newvarenv)
                            val newbod = subst_free [(Bvar,newvar)] Body
                            val newbod2 = renameBounds newbod thisenv in
                            mk_exists{Body = newbod2, Bvar = newvar}    
			end
		else if is_conj t then
			let val {conj1,conj2} = dest_conj t
			    val vpl = renameBounds conj1 thisenv
			    val vpr = renameBounds conj2 thisenv in
		            mk_conj {conj1 = vpl, conj2 = vpr}
			end
		else 
			let val {disj1, disj2} = dest_disj t 
			    val vpl = renameBounds disj1 thisenv
			    val  vpr = renameBounds disj2  thisenv in
			    mk_disj {disj1 = vpl,disj2= vpr}  
			end;
                	


exception VARFORM_PROBLEM;
		
fun varform t = if (hol_literal t) then
			t
	 	
		else if is_forall t then
			let val {Body, Bvar} = dest_forall t 
         (* need to subst schematic vars for Bvar here, e.g. x becomes ?x *)
                         val newB = free2var Bvar
                         val newBody = subst_free[(Bvar, newB)] Body in
			    varform newBody
			end
		else if is_exists t then
        (* Shouldn't really be any exists in term due to Skolemisation*)
			let val {Body, Bvar} =dest_exists t in
			    varform Body
			end
		else if is_conj t then
			let val {conj1,conj2} = dest_conj t
			    val vpl = varform conj1 
			    val vpr = varform conj2 in
		            mk_conj {conj1 = vpl, conj2 = vpr}
			end
		else if is_disj t then
			let val {disj1, disj2} = dest_disj t 
			    val vpl = varform disj1
			    val  vpr = varform disj2 in
			    mk_disj {disj1 = vpl,disj2= vpr}  
			end
                else
                        raise VARFORM_PROBLEM;
                	
 
exception ASSERTION of string;