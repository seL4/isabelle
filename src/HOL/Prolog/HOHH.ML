(*  Title:    HOL/Prolog/HOHH.ML
    ID:       $Id$
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

open HOHH;

exception not_HOHH;

fun isD t = case t of 
    Const("Trueprop",_)$t     => isD t
  | Const("op &"  ,_)$l$r     => isD l andalso isD r
  | Const("op -->",_)$l$r     => isG l andalso isD r
  | Const(   "==>",_)$l$r     => isG l andalso isD r
  | Const("All",_)$Abs(s,_,t) => isD t
  | Const("all",_)$Abs(s,_,t) => isD t
  | Const("op |",_)$_$_       => false
  | Const("Ex" ,_)$_          => false
  | Const("not",_)$_          => false
  | Const("True",_)           => false
  | Const("False",_)          => false
  | l $ r                     => isD l
  | Const _ (* rigid atom *)  => true
  | Bound _ (* rigid atom *)  => true
  | Free  _ (* rigid atom *)  => true
  | _    (* flexible atom,
	    anything else *)  => false
and
    isG t = case t of
    Const("Trueprop",_)$t     => isG t
  | Const("op &"  ,_)$l$r     => isG l andalso isG r
  | Const("op |"  ,_)$l$r     => isG l andalso isG r
  | Const("op -->",_)$l$r     => isD l andalso isG r
  | Const(   "==>",_)$l$r     => isD l andalso isG r
  | Const("All",_)$Abs(_,_,t) => isG t
  | Const("all",_)$Abs(_,_,t) => isG t
  | Const("Ex" ,_)$Abs(_,_,t) => isG t
  | Const("True",_)           => true
  | Const("not",_)$_          => false
  | Const("False",_)          => false
  | _ (* atom *)	      => true;

val check_HOHH_tac1 = PRIMITIVE (fn thm => 
	if isG (concl_of thm) then thm else raise not_HOHH);
val check_HOHH_tac2 = PRIMITIVE (fn thm => 
	if forall isG (prems_of thm) then thm else raise not_HOHH);
fun check_HOHH thm  = (if isD (concl_of thm) andalso forall isG (prems_of thm) 
			then thm else raise not_HOHH);

fun atomizeD thm = let 
    fun at  thm = case concl_of thm of
      _$(Const("All" ,_)$Abs(s,_,_))=> at(thm RS (read_instantiate [("x",
					"?"^(if s="P" then "PP" else s))] spec))
    | _$(Const("op &",_)$_$_)       => at(thm RS conjunct1)@at(thm RS conjunct2)
    | _$(Const("op -->",_)$_$_)     => at(thm RS mp)
    | _				    => [thm]
in map zero_var_indexes (at thm) end;

val atomize_ss = empty_ss setmksimps (mksimps mksimps_pairs) addsimps [
	all_conj_distrib, (* "(! x. P x & Q x) = ((! x. P x) & (! x. Q x))" *)
	imp_conjL RS sym, (* "(D :- G1 :- G2) = (D :- G1 & G2)" *)
	imp_conjR,	  (* "(D1 & D2 :- G) = ((D1 :- G) & (D2 :- G))" *)
	imp_all];	  (* "((!x. D) :- G) = (!x. D :- G)" *)

(*val hyp_resolve_tac = METAHYPS (fn prems => 
				  resolve_tac (flat (map atomizeD prems)) 1);
  -- is nice, but cannot instantiate unknowns in the assumptions *)
fun hyp_resolve_tac i st = let
	fun ap (Const("All",_)$Abs(_,_,t))=(case ap t of (k,a,t) => (k+1,a  ,t))
	|   ap (Const("op -->",_)$_$t)    =(case ap t of (k,_,t) => (k,true ,t))
	|   ap t			  = 			    (0,false,t);
(*
	fun rep_goal (Const ("all",_)$Abs (_,_,t)) = rep_goal t
	|   rep_goal (Const ("==>",_)$s$t)	   = 
			(case rep_goal t of (l,t) => (s::l,t))
	|   rep_goal t				   = ([]  ,t);
	val (prems, Const("Trueprop", _)$concl) = rep_goal 
						(#3(dest_state (st,i)));
*)
	val subgoal = #3(dest_state (st,i));
	val prems = Logic.strip_assums_hyp subgoal;
	val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal);
	fun drot_tac k i = DETERM (rotate_tac k i);
	fun spec_tac 0 i = all_tac
	|   spec_tac k i = EVERY' [dtac spec, drot_tac ~1, spec_tac (k-1)] i;
	fun dup_spec_tac k i = if k = 0 then all_tac else EVERY'
		      [DETERM o (etac all_dupE), drot_tac ~2, spec_tac (k-1)] i;
	fun same_head _ (Const (x,_)) (Const (y,_)) = x = y
	|   same_head k (s$_)         (t$_)	    = same_head k s t
	|   same_head k (Bound i)     (Bound j)	    = i = j + k
	|   same_head _ _             _             = true;
	fun mapn f n []      = []
	|   mapn f n (x::xs) = f n x::mapn f (n+1) xs;
	fun pres_tac (k,arrow,t) n i = drot_tac n i THEN (
		if same_head k t concl
		then dup_spec_tac k i THEN 
		     (if arrow then etac mp i THEN drot_tac (~n) i else atac i)
		else no_tac);
	val ptacs = mapn (fn n => fn t => 
			  pres_tac (ap (HOLogic.dest_Trueprop t)) n i) 0 prems;
	in foldl (op APPEND) (no_tac, ptacs) st end;

fun ptac prog = let
  val proga = flat (map atomizeD prog)			(* atomize the prog *)
  in	(REPEAT_DETERM1 o FIRST' [
		rtac TrueI,			(* "True" *)
		rtac conjI,			(* "[| P; Q |] ==> P & Q" *)
		rtac allI,			(* "(!!x. P x) ==> ! x. P x" *)
		rtac exI,			(* "P x ==> ? x. P x" *)
		rtac impI THEN'			(* "(P ==> Q) ==> P --> Q" *)
		  asm_full_simp_tac atomize_ss THEN'	(* atomize the asms *)
		  (REPEAT_DETERM o (etac conjE))	(* split the asms *)
		]) 
	ORELSE' resolve_tac [disjI1,disjI2]	(* "P ==> P | Q","Q ==> P | Q"*)
	ORELSE' ((resolve_tac proga APPEND' hyp_resolve_tac)
		 THEN' (fn _ => check_HOHH_tac2))
end;

fun prolog_tac prog = check_HOHH_tac1 THEN 
		      DEPTH_SOLVE (ptac (map check_HOHH prog) 1);

val prog_HOHH = [];
