(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

structure ReconOrderClauses =
struct

(*----------------------------------------------*)
(* Reorder clauses for use in binary resolution *)
(*----------------------------------------------*)

fun remove_nth n [] = []
|   remove_nth n xs = (List.take (xs, n-1)) @ (List.drop (xs, n))

(*Differs from List.nth: it counts from 1 rather than from 0*)
fun get_nth n (x::xs) = hd (Library.drop (n-1, x::xs))


exception Not_in_list;  


fun numlist 0 = []
|   numlist n = (numlist (n - 1))@[n]


fun last(x::xs) = if xs=[] then x else last xs
fun butlast []= []
|   butlast(x::xs) = if xs=[] then [] else (x::(butlast xs))


fun minus a b = b - a;


(* code to rearrange clauses so that they're the same as the parsed in SPASS version *)

 fun takeUntil ch [] res  = (res, [])
 |   takeUntil ch (x::xs) res = if   x = ch 
                                then
                                     (res, xs)
                                else
                                     takeUntil ch xs (res@[x]);

fun contains_eq str = "=" mem str 

fun eq_not_neq str = let val uptoeq = fst(takeUntil "=" str [])
                     in (last uptoeq) <> "~" end
                   
fun get_eq_strs str =  if eq_not_neq  str   (*not an inequality *)
                       then 
                           let val (left, right) = takeUntil "=" str []
                           in
                               (butlast left, tl right)
                           end
                       else                  (* is an inequality *)
                           let val (left, right) = takeUntil "~" str []
                           in 
                              (butlast left, tl (tl right))
                           end
                


fun switch_equal a x = let val (a_lhs, a_rhs) = get_eq_strs a
                           val (x_lhs, x_rhs) = get_eq_strs x
                       in
                           (a_lhs = x_rhs) andalso (a_rhs = x_lhs)
                       end

fun equal_pair (a,b) = equal a b

fun is_var_pair (a,b) vars = (a mem vars) andalso (b mem vars)

fun var_equiv vars (a,b)  = (equal_pair (a,b)) orelse (is_var_pair (a,b) vars)

fun all_true [] = false
|   all_true xs = let val falselist = List.filter (equal false ) xs 
                  in
                      falselist = []
                  end



fun var_pos_eq vars x y = 
    String.size x = String.size y andalso
    let val xs = explode x
	val ys = explode y
	val xsys = ListPair.zip (xs,ys)
	val are_var_pairs = map (var_equiv vars) xsys
    in
	all_true are_var_pairs 
    end;

fun pos_in_list a [] allvars (pos_num, symlist, nsymlist) =  raise Not_in_list
  | pos_in_list a (x::[]) allvars (pos_num , symlist, nsymlist) = 
      let val y = explode x 
	  val b = explode a
      in
	 if  b = y
	 then 
	      (pos_num, symlist, nsymlist)
	 else 
	      if (var_pos_eq allvars  a x) 
	      then  (* Equal apart from meta-vars having different names *)
		  (pos_num, symlist, nsymlist)
	      else 
		  if (contains_eq b) andalso (contains_eq y)
		  then 
		      if (eq_not_neq b) andalso (eq_not_neq y)  andalso (switch_equal b y )          
		      then (* both are equalities and equal under sym*) 
			  (pos_num, (pos_num::symlist), nsymlist)  (* add pos to symlist *)                                                                    
			  else 
			  if not(eq_not_neq b) andalso not(eq_not_neq y) andalso  (switch_equal b y)
			   then (* if they're equal under not_sym *)
			       (pos_num, (symlist), (pos_num::nsymlist))(* add pos to nsymlist *)
			   else 
				raise Not_in_list
		  else 
		       raise Not_in_list
      end   
  | pos_in_list a (x::xs) allvars (pos_num, symlist, nsymlist) = 
      let val y = explode x 
	  val b = explode a
      in
	 if  b = y
	 then 
	      (pos_num, symlist, nsymlist)
	 
	 else
	       if (var_pos_eq allvars  a x) (* Equal apart from meta-vars having different names *)
	       then 
		  (pos_num, symlist, nsymlist)
	       else 
		   if (contains_eq b) andalso (contains_eq y)
		   then 
		       if (eq_not_neq b) andalso (eq_not_neq y)  andalso (switch_equal b y )   (* both are equalities and equal under sym*)        
		       then 
			   (pos_num, (pos_num::symlist), nsymlist)  (* add pos to symlist *)                                                                    else 
			   if not(eq_not_neq b) andalso not(eq_not_neq y) andalso  (switch_equal b y )  (* if they're equal under not_sym *)
			   then 
				(pos_num, (symlist), (pos_num::nsymlist))(* add pos to nsymlist *)
			   else 
				pos_in_list a xs allvars((pos_num + 1), symlist, nsymlist)
		   else 
			 pos_in_list a xs allvars((pos_num + 1), symlist, nsymlist)
		   
      end;


    (* in
	if  b = y
	then 
	     (pos_num, symlist, nsymlist)
	else if (contains_eq b) andalso (contains_eq y)
	     then if (eq_not_neq b) andalso (eq_not_neq y) (* both are equalities*)
		  then if (switch_equal b y )              (* if they're equal under sym *)
		       then 
			   (pos_num, (pos_num::symlist), nsymlist)  (* add pos to symlist *)
		       else 
			     pos_in_list a xs ((pos_num + 1), symlist, nsymlist)
		  else if not(eq_not_neq b) andalso not(eq_not_neq y)  (* both are inequalities *)
		       then if (switch_equal b y )  (* if they're equal under not_sym *)
			    then 
				(pos_num, (symlist), (pos_num::nsymlist))(* add pos to nsymlist *)
			    else 
				     pos_in_list a xs ((pos_num + 1), symlist, nsymlist)
		       else
			      pos_in_list a xs ((pos_num + 1), symlist, nsymlist)
		   else  
			   pos_in_list a xs ((pos_num + 1), symlist, nsymlist)
	      else 
		      pos_in_list a xs ((pos_num + 1), symlist, nsymlist)
     end   

    *)


(* checkorder Spass Isabelle [] *)

fun checkorder [] strlist allvars (numlist, symlist, not_symlist) =
      (numlist,symlist, not_symlist)
|   checkorder (x::xs) strlist allvars (numlist, symlist, not_symlist) =  
         let val (posnum, symlist', not_symlist') = 
               pos_in_list x strlist allvars (0, symlist, not_symlist) 
         in
             checkorder xs  strlist allvars ((numlist@[posnum]), symlist', not_symlist') 
         end

fun is_digit ch =
    ( ch >=  "0" andalso ch <=  "9")


fun is_alpha ch =
    (ch >=  "A" andalso  ch <=  "Z") orelse
    (ch >=  "a" andalso ch <=  "z")


fun is_alpha_space_or_neg_or_eq ch =
    (ch = "~") orelse (is_alpha ch) orelse ( ch = " ")orelse ( ch = "=")

fun lit_string sg t = 
    let val termstr = Sign.string_of_term sg t
	val exp_term = explode termstr
    in
	implode(List.filter is_alpha_space_or_neg_or_eq exp_term)
    end

fun get_meta_lits thm = map (lit_string (sign_of_thm thm)) (prems_of thm)


fun is_alpha_space_or_neg_or_eq_or_bracket ch =
   is_alpha_space_or_neg_or_eq ch orelse (ch= "(") orelse (ch = ")")

fun lit_string_bracket sg t = 
    let val termstr = Sign.string_of_term sg t
	val exp_term = explode termstr
    in
	implode(List.filter  is_alpha_space_or_neg_or_eq_or_bracket exp_term)
    end;

fun get_meta_lits_bracket thm = 
    map (lit_string_bracket (sign_of_thm thm)) (prems_of thm)

      
fun apply_rule rule [] thm = thm
|   apply_rule rule  (x::xs) thm = let val thm' = rule RSN ((x+1),thm)
                                  in
                                      apply_rule rule xs thm'
                                  end



(* resulting thm, clause-strs in spass order, vars *)

fun rearrange_clause thm res_strlist allvars = 
    let val isa_strlist = get_meta_lits thm 
        (* change this to use Jia's code to get same looking thing as isastrlist? *)
	val (posns, symlist, not_symlist) = checkorder res_strlist isa_strlist allvars([],[],[])
	val symmed = apply_rule sym symlist thm
	val not_symmed = apply_rule not_sym not_symlist symmed
    in
       ((rearrange_prems posns not_symmed), posns, symlist,not_symlist)
    end
    
end;

