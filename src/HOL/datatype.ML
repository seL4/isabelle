(* Title:       HOL/datatype.ML
   ID:          $Id$
   Author:      Max Breitling, Carsten Clasohm, Tobias Nipkow, Norbert Voelker
   Copyright 1995 TU Muenchen
*)


(*used for constructor parameters*)
datatype dt_type = dtVar of string |
  dtTyp of dt_type list * string |
  dtRek of dt_type list * string;

structure Datatype =
struct
local 

val mysort = sort;
open ThyParse HOLogic;
exception Impossible;
exception RecError of string;

val is_dtRek = (fn dtRek _ => true  |  _  => false);
fun opt_parens s = if s = "" then "" else enclose "(" ")" s; 

(* ----------------------------------------------------------------------- *)
(* Derivation of the primrec combinator application from the equations     *)

(* substitute fname(ls,xk,rs) by yk(ls,rs) in t for (xk,yk) in pairs  *) 

fun subst_apps (_,_) [] t = t
  | subst_apps (fname,rpos) pairs t =
    let 
    fun subst (Abs(a,T,t)) = Abs(a,T,subst t)
      | subst (funct $ body) = 
	let val (f,b) = strip_comb (funct$body)
	in 
	  if is_Const f andalso fst(dest_Const f) = fname 
	    then 
	      let val (ls,rest) = (take(rpos,b), drop(rpos,b));
		val (xk,rs) = (hd rest,tl rest)
		  handle LIST _ => raise RecError "not enough arguments \
		   \ in recursive application on rhs"
              in 
		(case assoc (pairs,xk) of 
		   None => raise RecError 
		     ("illegal occurence of " ^ fname ^ " on rhs")
		 | Some(U) => list_comb(U,map subst (ls @ rs)))
	      end
	  else list_comb(f, map subst b)
	end
      | subst(t) = t
    in subst t end;
  
(* abstract rhs *)

fun abst_rec (fname,rpos,tc,ls,cargs,rs,rhs) =       
  let val rargs = (map fst o 
		   (filter (fn (a,T) => is_dtRek T))) (cargs ~~ tc);
      val subs = map (fn (s,T) => (s,dummyT))
	           (rev(rename_wrt_term rhs rargs));
      val subst_rhs = subst_apps (fname,rpos)
	                (map Free rargs ~~ map Free subs) rhs;
  in 
      list_abs_free (cargs @ subs @ ls @ rs, subst_rhs) 
  end;

(* parsing the prim rec equations *)

fun dest_eq ( Const("Trueprop",_) $ (Const ("op =",_) $ lhs $ rhs))
                 = (lhs, rhs)
   | dest_eq _ = raise RecError "not a proper equation"; 

fun dest_rec eq = 
  let val (lhs,rhs) = dest_eq eq; 
    val (name,args) = strip_comb lhs; 
    val (ls',rest)  = take_prefix is_Free args; 
    val (middle,rs') = take_suffix is_Free rest;
    val rpos = length ls';
    val (c,cargs') = strip_comb (hd middle)
      handle LIST "hd" => raise RecError "constructor missing";
    val (ls,cargs,rs) = (map dest_Free ls', map dest_Free cargs'
			 , map dest_Free rs')
      handle TERM ("dest_Free",_) => 
	  raise RecError "constructor has illegal argument in pattern";
  in 
    if length middle > 1 then 
      raise RecError "more than one non-variable in pattern"
    else if not(null(findrep (map fst (ls @ rs @ cargs)))) then 
      raise RecError "repeated variable name in pattern" 
	 else (fst(dest_Const name) handle TERM _ => 
	       raise RecError "function is not declared as constant in theory"
		 ,rpos,ls,fst( dest_Const c),cargs,rs,rhs)
  end; 

(* check function specified for all constructors and sort function terms *)

fun check_and_sort (n,its) = 
  if length its = n 
    then map snd (mysort (fn ((i : int,_),(j,_)) => i<j) its)
  else raise error "Primrec definition error:\n\
   \Please give an equation for every constructor";

(* translate rec equations into function arguments suitable for rec comb *)
(* theory parameter needed for printing error messages                   *) 

fun trans_recs _ _ [] = error("No primrec equations.")
  | trans_recs thy cs' (eq1::eqs) = 
    let val (name1,rpos1,ls1,_,_,_,_) = dest_rec eq1
      handle RecError s =>
	error("Primrec definition error: " ^ s ^ ":\n" 
	      ^ "   " ^ Sign.string_of_term (sign_of thy) eq1);
      val tcs = map (fn (_,c,T,_,_) => (c,T)) cs';  
      val cs = map fst tcs;
      fun trans_recs' _ [] = []
        | trans_recs' cis (eq::eqs) = 
	  let val (name,rpos,ls,c,cargs,rs,rhs) = dest_rec eq; 
	    val tc = assoc(tcs,c);
	    val i = (1 + find (c,cs))  handle LIST "find" => 0; 
	  in
	  if name <> name1 then 
	    raise RecError "function names inconsistent"
	  else if rpos <> rpos1 then 
	    raise RecError "position of rec. argument inconsistent"
	  else if i = 0 then 
	    raise RecError "illegal argument in pattern" 
	  else if i mem cis then
	    raise RecError "constructor already occured as pattern "
	       else (i,abst_rec (name,rpos,the tc,ls,cargs,rs,rhs))
		     :: trans_recs' (i::cis) eqs 
	  end
	  handle RecError s =>
	        error("Primrec definition error\n" ^ s ^ "\n" 
		      ^ "   " ^ Sign.string_of_term (sign_of thy) eq);
    in (  name1, ls1
	, check_and_sort (length cs, trans_recs' [] (eq1::eqs)))
    end ;

in
  fun add_datatype (typevars, tname, cons_list') thy = 
    let
      fun typid(dtRek(_,id)) = id
        | typid(dtVar s) = implode (tl (explode s))
        | typid(dtTyp(_,id)) = id;

      fun index_vnames(vn::vns,tab) =
            (case assoc(tab,vn) of
               None => if vn mem vns
                       then (vn^"1") :: index_vnames(vns,(vn,2)::tab)
                       else vn :: index_vnames(vns,tab)
             | Some(i) => (vn^(string_of_int i)) ::
                          index_vnames(vns,(vn,i+1)::tab))
        | index_vnames([],tab) = [];

      fun mk_var_names types = index_vnames(map typid types,[]);

      (*search for free type variables and convert recursive *)
      fun analyse_types (cons, types, syn) =
	let fun analyse(t as dtVar v) =
                  if t mem typevars then t
                  else error ("Free type variable " ^ v ^ " on rhs.")
	      | analyse(dtTyp(typl,s)) =
		  if tname <> s then dtTyp(analyses typl, s)
                  else if typevars = typl then dtRek(typl, s)
                       else error (s ^ " used in different ways")
	      | analyse(dtRek _) = raise Impossible
	    and analyses ts = map analyse ts;
	in (cons, Syntax.const_name cons syn, analyses types,
            mk_var_names types, syn)
        end;

     (*test if all elements are recursive, i.e. if the type is empty*)
      
      fun non_empty (cs : ('a * 'b * dt_type list * 'c *'d) list) = 
	not(forall (exists is_dtRek o #3) cs) orelse
	error("Empty datatype not allowed!");

      val cons_list = map analyse_types cons_list';
      val dummy = non_empty cons_list;
      val num_of_cons = length cons_list;

     (* Auxiliary functions to construct argument and equation lists *)

     (*generate 'var_n, ..., var_m'*)
      fun Args(var, delim, n, m) = 
	space_implode delim (map (fn n => var^string_of_int(n)) (n upto m));

      fun C_exp name vns = name ^ opt_parens(space_implode ") (" vns);

     (*Arg_eqs([x1,...,xn],[y1,...,yn]) = "x1 = y1 & ... & xn = yn" *)
      fun arg_eqs vns vns' =
        let fun mkeq(x,x') = x ^ "=" ^ x'
        in space_implode " & " (map mkeq (vns~~vns')) end;

     (*Pretty printers for type lists;
       pp_typlist1: parentheses, pp_typlist2: brackets*)
      fun pp_typ (dtVar s) = "(" ^ s ^ "::term)"
        | pp_typ (dtTyp (typvars, id)) =
	  if null typvars then id else (pp_typlist1 typvars) ^ id
        | pp_typ (dtRek (typvars, id)) = (pp_typlist1 typvars) ^ id
      and
	pp_typlist' ts = commas (map pp_typ ts)
      and
	pp_typlist1 ts = if null ts then "" else parens (pp_typlist' ts);

      fun pp_typlist2 ts = if null ts then "" else brackets (pp_typlist' ts);

     (* Generate syntax translation for case rules *)
      fun calc_xrules c_nr y_nr ((_, name, _, vns, _) :: cs) = 
	let val arity = length vns;
	  val body  = "z" ^ string_of_int(c_nr);
	  val args1 = if arity=0 then ""
		      else " " ^ Args ("y", " ", y_nr, y_nr+arity-1);
	  val args2 = if arity=0 then ""
		      else "(% " ^ Args ("y", " ", y_nr, y_nr+arity-1) 
			^ ". ";
	  val (rest1,rest2) = 
	    if null cs then ("","")
	    else let val (h1, h2) = calc_xrules (c_nr+1) (y_nr+arity) cs
	    in (" | " ^ h1, " " ^ h2) end;
	in (name ^ args1 ^ " => " ^ body ^ rest1,
            args2 ^ body ^ (if args2 = "" then "" else ")") ^ rest2)
        end
        | calc_xrules _ _ [] = raise Impossible;
      
      val xrules =
	let val (first_part, scnd_part) = calc_xrules 1 1 cons_list
	in [("logic", "case x of " ^ first_part) <->
	     ("logic", tname ^ "_case " ^ scnd_part ^ " x")]
	end;

     (*type declarations for constructors*)
      fun const_type (id, _, typlist, _, syn) =
	(id,  
	 (if null typlist then "" else pp_typlist2 typlist ^ " => ") ^
	    pp_typlist1 typevars ^ tname, syn);


      fun assumpt (dtRek _ :: ts, v :: vs ,found) =
	let val h = if found then ";P(" ^ v ^ ")" else "[| P(" ^ v ^ ")"
	in h ^ (assumpt (ts, vs, true)) end
        | assumpt (t :: ts, v :: vs, found) = assumpt (ts, vs, found)
      | assumpt ([], [], found) = if found then "|] ==>" else ""
        | assumpt _ = raise Impossible;

      fun t_inducting ((_, name, types, vns, _) :: cs) =
	let
	  val h = if null types then " P(" ^ name ^ ")"
		  else " !!" ^ (space_implode " " vns) ^ "." ^
		    (assumpt (types, vns, false)) ^
                    "P(" ^ C_exp name vns ^ ")";
	  val rest = t_inducting cs;
	in if rest = "" then h else h ^ "; " ^ rest end
        | t_inducting [] = "";

      fun t_induct cl typ_name =
        "[|" ^ t_inducting cl ^ "|] ==> P(" ^ typ_name ^ ")";

      fun gen_typlist typevar f ((_, _, ts, _, _) :: cs) =
	let val h = if (length ts) > 0
		      then pp_typlist2(f ts) ^ "=>"
		    else ""
	in h ^ typevar ^  "," ^ (gen_typlist typevar f cs) end
        | gen_typlist _ _ [] = "";


(* -------------------------------------------------------------------- *)
(* The case constant and rules 	        				*)
 		
      val t_case = tname ^ "_case";

      fun case_rule n (id, name, _, vns, _) =
	let val args = if vns = [] then "" else " " ^ space_implode " " vns
	in (t_case ^ "_" ^ id,
	    t_case ^ " " ^ Args("f", " ", 1, num_of_cons)
	    ^ " (" ^ name ^ args ^ ") = f"^string_of_int(n) ^ args)
	end

      fun case_rules n (c :: cs) = case_rule n c :: case_rules(n+1) cs
        | case_rules _ [] = [];

      val datatype_arity = length typevars;

      val types = [(tname, datatype_arity, NoSyn)];

      val arities = 
        let val term_list = replicate datatype_arity termS;
        in [(tname, term_list, termS)] 
	end;

      val datatype_name = pp_typlist1 typevars ^ tname;

      val new_tvar_name = variant (map (fn dtVar s => s) typevars) "'z";

      val case_const =
	(t_case,
	 "[" ^ gen_typlist new_tvar_name I cons_list 
	 ^  pp_typlist1 typevars ^ tname ^ "] =>" ^ new_tvar_name^"::term",
	 NoSyn);

      val rules_case = case_rules 1 cons_list;

(* -------------------------------------------------------------------- *)
(* The prim-rec combinator						*) 

      val t_rec = tname ^ "_rec"

(* adding type variables for dtRek types to end of list of dt_types      *)   

      fun add_reks ts = 
	ts @ map (fn _ => dtVar new_tvar_name) (filter is_dtRek ts); 

(* positions of the dtRek types in a list of dt_types, starting from 1  *)
      fun rek_vars ts vns = map snd (filter (is_dtRek o fst) (ts ~~ vns))

      fun rec_rule n (id,name,ts,vns,_) = 
	let val args = opt_parens(space_implode ") (" vns)
	  val fargs = opt_parens(Args("f", ") (", 1, num_of_cons))
	  fun rarg vn = t_rec ^ fargs ^ " (" ^ vn ^ ")"
	  val rargs = opt_parens(space_implode ") ("
                                 (map rarg (rek_vars ts vns)))
	in
	  (t_rec ^ "_" ^ id,
	   t_rec ^ fargs ^ " (" ^ name ^ args ^ ") = f"
	   ^ string_of_int(n) ^ args ^ rargs)
	end

      fun rec_rules n (c::cs) = rec_rule n c :: rec_rules (n+1) cs 
	| rec_rules _ [] = [];

      val rec_const =
	(t_rec,
	 "[" ^ (gen_typlist new_tvar_name add_reks cons_list) 
	 ^ (pp_typlist1 typevars) ^ tname ^ "] =>" ^ new_tvar_name^"::term",
	 NoSyn);

      val rules_rec = rec_rules 1 cons_list

(* -------------------------------------------------------------------- *)
      val consts = 
	map const_type cons_list
	@ (if num_of_cons < dtK then []
	   else [(tname ^ "_ord", datatype_name ^ "=>nat", NoSyn)])
	@ [case_const,rec_const];


      fun Ci_ing ((id, name, _, vns, _) :: cs) =
	   if null vns then Ci_ing cs
	   else let val vns' = variantlist(vns,vns)
                in ("inject_" ^ id,
		    "(" ^ (C_exp name vns) ^ "=" ^ (C_exp name vns')
		    ^ ") = (" ^ (arg_eqs vns vns') ^ ")") :: (Ci_ing cs)
                end
	| Ci_ing [] = [];

      fun Ci_negOne (id1,name1,_,vns1,_) (id2,name2,_,vns2,_) =
            let val vns2' = variantlist(vns2,vns1)
                val ax = C_exp name1 vns1 ^ "~=" ^ C_exp name2 vns2'
	in (id1 ^ "_not_" ^ id2, ax) end;

      fun Ci_neg1 [] = []
	| Ci_neg1 (c1::cs) = (map (Ci_negOne c1) cs) @ Ci_neg1 cs;

      fun suc_expr n = 
	if n=0 then "0" else "Suc(" ^ suc_expr(n-1) ^ ")";

      fun Ci_neg2() =
	let val ord_t = tname ^ "_ord";
	  val cis = cons_list ~~ (0 upto (num_of_cons - 1))
	  fun Ci_neg2equals ((id, name, _, vns, _), n) =
	    let val ax = ord_t ^ "(" ^ (C_exp name vns) ^ ") = " ^ (suc_expr n)
	    in (ord_t ^ "_" ^ id, ax) end
	in (ord_t ^ "_distinct", ord_t^"(x) ~= "^ord_t^"(y) ==> x ~= y") ::
	  (map Ci_neg2equals cis)
	end;

      val rules_distinct = if num_of_cons < dtK then Ci_neg1 cons_list
			   else Ci_neg2();

      val rules_inject = Ci_ing cons_list;

      val rule_induct = (tname ^ "_induct", t_induct cons_list tname);

      val rules = rule_induct ::
	(rules_inject @ rules_distinct @ rules_case @ rules_rec);

      fun add_primrec eqns thy =
	let val rec_comb = Const(t_rec,dummyT)
	  val teqns = map (fn neq => snd(read_axm (sign_of thy) neq)) eqns
	  val (fname,ls,fns) = trans_recs thy cons_list teqns
	  val rhs = 
	    list_abs_free
	    (ls @ [(tname,dummyT)]
	     ,list_comb(rec_comb
			, fns @ map Bound (0 ::(length ls downto 1))));
          val sg = sign_of thy;
          val defpair =  mk_defpair (Const(fname,dummyT),rhs)
	  val defpairT as (_, _ $ Const(_,T) $ _ ) = inferT_axm sg defpair;
	  val varT = Type.varifyT T;
          val ftyp = the (Sign.const_type sg fname);
	in
	  if Type.typ_instance (#tsig(Sign.rep_sg sg), ftyp, varT)
	  then add_defs_i [defpairT] thy
	  else error("Primrec definition error: \ntype of " ^ fname 
		     ^ " is not instance of type deduced from equations")
	end;

    in
      store_datatype (tname, map (fn (x,_,_) => x) cons_list');
      (thy |> add_types types
           |> add_arities arities
           |> add_consts consts
           |> add_trrules xrules
           |> add_axioms rules, add_primrec)
    end
end
end

(*
Informal description of functions used in datatype.ML for the Isabelle/HOL
implementation of prim. rec. function definitions. (N. Voelker, Feb. 1995) 

* subst_apps (fname,rpos) pairs t:
   substitute the term 
       fname(ls,xk,rs) 
   by 
      yk(ls,rs) 
   in t for (xk,yk) in pairs, where rpos = length ls. 
   Applied with : 
     fname = function name 
     rpos = position of recursive argument 
     pairs = list of pairs (xk,yk), where 
          xk are the rec. arguments of the constructor in the pattern,
          yk is a variable with name derived from xk 
     t = rhs of equation 

* abst_rec (fname,rpos,tc,ls,cargs,rs,rhs)
  - filter recursive arguments from constructor arguments cargs,
  - perform substitutions on rhs, 
  - derive list subs of new variable names yk for use in subst_apps, 
  - abstract rhs with respect to cargs, subs, ls and rs. 

* dest_eq t 
  destruct a term denoting an equation into lhs and rhs. 

* dest_req eq 
  destruct an equation of the form 
      name (vl1..vlrpos, Ci(vi1..vin), vr1..vrn) = rhs
  into 
  - function name  (name) 
  - position of the first non-variable parameter  (rpos)
  - the list of first rpos parameters (ls = [vl1..vlrpos]) 
  - the constructor (fst( dest_Const c) = Ci)
  - the arguments of the constructor (cargs = [vi1..vin])
  - the rest of the variables in the pattern (rs = [vr1..vrn])
  - the right hand side of the equation (rhs).  
 
* check_and_sort (n,its)
  check that  n = length its holds, and sort elements of its by 
  first component. 

* trans_recs thy cs' (eq1::eqs)
  destruct eq1 into name1, rpos1, ls1, etc.. 
  get constructor list with and without type (tcs resp. cs) from cs',  
  for every equation:  
    destruct it into (name,rpos,ls,c,cargs,rs,rhs)
    get typed constructor tc from c and tcs 
    determine the index i of the constructor 
    check function name and position of rec. argument by comparison
    with first equation 
    check for repeated variable names in pattern
    derive function term f_i which is used as argument of the rec. combinator
    sort the terms f_i according to i and return them together
      with the function name and the parameter of the definition (ls). 

* Application:

  The rec. combinator is applied to the function terms resulting from
  trans_rec. This results in a function which takes the recursive arg. 
  as first parameter and then the arguments corresponding to ls. The
  order of parameters is corrected by setting the rhs equal to 

  list_abs_free
	    (ls @ [(tname,dummyT)]
	     ,list_comb(rec_comb
			, fns @ map Bound (0 ::(length ls downto 1))));

  Note the de-Bruijn indices counting the number of lambdas between the
  variable and its binding. 
*)
