(*  Title:      HOL/Tools/svc_funcs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Translation and abstraction functions for the interface to SVC

Based upon the work of Søren T. Heilmann

Integers and naturals are translated as follows:
  In a positive context, replace x<y by x+1<=y
  In a negative context, replace x<=y by x<y+1
  In a negative context, replace x=y by x<y+1 & y<x+1
Biconditionals (if-and-only-iff) are expanded if they require such translations
  in either operand.

For each variable of type nat, an assumption is added that it is non-negative.
*)

structure Svc =
struct
 val trace = ref false;

 datatype expr =
     bracketed_expr of expr
   | ref_def_expr of string * expr
   | ref_expr of string
   | typed_expr of Type * expr
   | buildin_expr of string * expr list
   | interp_expr of string * expr list
   | uninterp_expr of string * expr list
   | false_expr 
   | true_expr
   | distinct_expr of string
   | int_expr of int
   | rat_expr of int * int
 and Type = 
     simple_type of string
   | array_type of Type * Type
   | record_type of (expr * Type) list
   | bitvec_type of int;

 open BasisLibrary

 fun toString t =
     let fun signedInt i = 
	 if i < 0 then "-" ^ Int.toString (~i)
	 else Int.toString i
	 fun ut(simple_type s) = s ^ " "
	   | ut(array_type(t1, t2)) = "ARRAY " ^ (ut t1) ^ (ut t2)
	   | ut(record_type fl) = 
	     "RECORD" ^ 
	     (foldl (fn (a, (d, t)) => a ^ (ue d) ^ (ut t)) (" ", fl))
	   | ut(bitvec_type n) = "BITVEC " ^ (Int.toString n) ^ " "
	 and ue(bracketed_expr e) = "(" ^ (ue e) ^ ") "
	   | ue(ref_def_expr(r, e)) = "$" ^ r ^ ":" ^ (ue e)
	   | ue(ref_expr r) = "$" ^ r ^ " "
	   | ue(typed_expr(t, e)) = (ut t) ^ (ue e)
	   | ue(buildin_expr(s, l)) = 
	     "(" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
	   | ue(interp_expr(s, l)) = 
	     "{" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ "} "
	   | ue(uninterp_expr(s, l)) = 
	     "(" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
	   | ue(false_expr) = "FALSE "
	   | ue(true_expr) = "TRUE "
	   | ue(distinct_expr s) = "@" ^ s ^ " "
	   | ue(int_expr i) = (signedInt i) ^ " "
	   | ue(rat_expr(i, j)) = (signedInt i) ^ "|" ^ (signedInt j) ^ " "
     in
	 ue t
     end;

 fun valid e = 
  let val svc_home = getenv "SVC_HOME" 
      val svc_machine = getenv "SVC_MACHINE"
      val check_valid = if svc_home = ""
	                then error "Environment variable SVC_HOME not set"
			else if svc_machine = ""
	                then error "Environment variable SVC_MACHINE not set"
			else svc_home ^ "/" ^ svc_machine ^ "/bin/check_valid"
      val svc_input = toString e
      val _ = if !trace then writeln ("Calling SVC:\n" ^ svc_input) else ()
      val svc_input_file  = File.tmp_path (Path.basic "SVM_in");
      val svc_output_file = File.tmp_path (Path.basic "SVM_out");
      val _ = (File.write svc_input_file svc_input;
	       execute (check_valid ^ " -dump-result " ^ 
			File.sysify_path svc_output_file ^
			" " ^ File.sysify_path svc_input_file ^ 
			"> /dev/null 2>&1"))
      val svc_output = File.read svc_output_file
	               handle _ => error "SVC returned no output"
      val _ = if !trace then writeln ("SVC Returns:\n" ^ svc_output) else ()
  in
      String.isPrefix "VALID" svc_output
  end

 (*New exception constructor for passing arguments to the oracle*)
 exception OracleExn of term;

 fun apply c args =
     let val (ts, bs) = ListPair.unzip args
     in  (list_comb(c,ts), exists I bs)  end;

 fun is_intnat T = T = HOLogic.intT orelse T = HOLogic.natT;
 
 (*Determining whether the biconditionals must be unfoled: if there are
   int or nat comparisons below*)
 val iff_tag =
   let fun tag t =
	 let val (c,ts) = strip_comb t
	 in  case c of
	     Const("op &", _)   => apply c (map tag ts)
	   | Const("op |", _)   => apply c (map tag ts)
	   | Const("op -->", _) => apply c (map tag ts)
	   | Const("Not", _)    => apply c (map tag ts)
	   | Const("True", _)   => (c, false)
	   | Const("False", _)  => (c, false)
	   | Const("op =", Type ("fun", [T,_])) => 
		 if T = HOLogic.boolT then
		     (*biconditional: with int/nat comparisons below?*)
		     let val [t1,t2] = ts
			 val (u1,b1) = tag t1
			 and (u2,b2) = tag t2
			 val cname = if b1 orelse b2 then "unfold" else "keep"
		     in 
			(Const ("SVC_Oracle.iff_" ^ cname, dummyT) $ u1 $ u2,
			 b1 orelse b2)
		     end
		 else (*numeric equality*)          (t, is_intnat T)
	   | Const("op <", Type ("fun", [T,_]))  => (t, is_intnat T)
	   | Const("op <=", Type ("fun", [T,_])) => (t, is_intnat T)
	   | _ => (t, false)
	 end
   in #1 o tag end;


 (*Map expression e to 0<=a --> e, where "a" is the name of a nat variable*)
 fun add_nat_var (a, e) = 
     buildin_expr("=>", [buildin_expr("<=", [int_expr 0, 
					     uninterp_expr (a, [])]),
			 e]);

 (*Translate an Isabelle formula into an SVC expression
   pos ["positive"]: true if an assumption, false if a goal*)
 fun expr_of pos t =
  let
    val params = rev (rename_wrt_term t (Term.strip_all_vars t))
    and body   = Term.strip_all_body t
    val nat_vars = ref ([] : string list)
    (*translation of a variable: record all natural numbers*)
    fun trans_var (a,T) =
	(if T = HOLogic.natT then nat_vars := (a ins_string (!nat_vars))
	                     else ();
         uninterp_expr (a, []))
    fun var (Free(a,T))      = trans_var ("F_" ^ a, T)
      | var (Var((a, 0), T)) = trans_var (a, T)
      | var (Bound i)        = 
          let val (a,T) = List.nth (params, i)
	  in  trans_var ("B_" ^ a, T)  end
      | var (t $ Bound _)    = var t    (*removing a parameter from a Var*)
      | var t = raise OracleExn t;
    (*translation of a literal*)
    fun lit (Const("Numeral.number_of", _) $ w) = NumeralSyntax.dest_bin w
      | lit (Const("0", _)) = 0
      | lit (Const("RealDef.0r", _)) = 0
      | lit (Const("RealDef.1r", _)) = 1
    (*translation of a literal expression [no variables]*)
    fun litExp (Const("op +", T) $ x $ y) = (litExp x) + (litExp y)
      | litExp (Const("op -", T) $ x $ y) = (litExp x) - (litExp y)
      | litExp (Const("op *", T) $ x $ y) = (litExp x) * (litExp y)
      | litExp (Const("uminus", _) $ x)   = ~(litExp x)
      | litExp t = lit t 
		handle Match => raise OracleExn t
    (*translation of a real/rational expression*)
    fun suc t = interp_expr("+", [int_expr 1, t])
    fun tm (Const("Suc", T) $ x) = suc (tm x)
      | tm (Const("op +", T) $ x $ y) = interp_expr("+", [tm x, tm y])
      | tm (Const("op -", _) $ x $ y) = 
	  interp_expr("+", [tm x, interp_expr("*", [int_expr ~1, tm y])])
      | tm (Const("op *", _) $ x $ y) = interp_expr("*", [tm x, tm y])
      | tm (Const("op /", _) $ x $ y) = 
	  interp_expr("*", [tm x, rat_expr(1, litExp y)])
      | tm (Const("uminus", _) $ x) = interp_expr("*", [int_expr ~1, tm x])
      | tm t = int_expr (lit t) 
	       handle Match => var t
    (*translation of a formula*)
    and fm pos (Const("op &", _) $ p $ q) =  
	    buildin_expr("AND", [fm pos p, fm pos q])
      | fm pos (Const("op |", _) $ p $ q) =  
	    buildin_expr("OR", [fm pos p, fm pos q])
      | fm pos (Const("op -->", _) $ p $ q) =  
	    buildin_expr("=>", [fm (not pos) p, fm pos q])
      | fm pos (Const("Not", _) $ p) =  
	    buildin_expr("NOT", [fm (not pos) p])
      | fm pos (Const("True", _)) = true_expr
      | fm pos (Const("False", _)) = false_expr
      | fm pos (Const("SVC_Oracle.iff_keep", _) $ p $ q) = 
	     (*polarity doesn't matter*)
	    buildin_expr("=", [fm pos p, fm pos q]) 
      | fm pos (Const("SVC_Oracle.iff_unfold", _) $ p $ q) = 
	    buildin_expr("AND",   (*unfolding uses both polarities*)
			 [buildin_expr("=>", [fm (not pos) p, fm pos q]),
			  buildin_expr("=>", [fm (not pos) q, fm pos p])])
      | fm pos (t as Const("op =", Type ("fun", [T,_])) $ x $ y) = 
	    let val tx = tm x and ty = tm y
		in if pos orelse T = HOLogic.realT then
		       buildin_expr("=", [tx, ty])
		   else if is_intnat T then
		       buildin_expr("AND", 
				    [buildin_expr("<", [tx, suc ty]), 
				     buildin_expr("<", [ty, suc tx])])
		   else raise OracleExn t
	    end
	(*inequalities: possible types are nat, int, real*)
      | fm pos (t as Const("op <",  Type ("fun", [T,_])) $ x $ y) = 
	    if not pos orelse T = HOLogic.realT then
		buildin_expr("<", [tm x, tm y])
	    else if is_intnat T then
		buildin_expr("<=", [suc (tm x), tm y])
	    else raise OracleExn t
      | fm pos (t as Const("op <=",  Type ("fun", [T,_])) $ x $ y) = 
	    if pos orelse T = HOLogic.realT then
		buildin_expr("<=", [tm x, tm y])
	    else if is_intnat T then
		buildin_expr("<", [tm x, suc (tm y)])
	    else raise OracleExn t
      | fm pos t = var t;
      (*entry point, and translation of a meta-formula*)
      fun mt pos ((c as Const("Trueprop", _)) $ p) = fm pos (iff_tag p)
	| mt pos ((c as Const("==>", _)) $ p $ q) = 
	    buildin_expr("=>", [mt (not pos) p, mt pos q])
	| mt pos t = fm pos (iff_tag t)  (*it might be a formula*)

      val body_e = mt pos body  (*evaluate now to assign into !nat_vars*)
  in 
     foldr add_nat_var (!nat_vars, body_e) 
  end;


 (*Generalize an Isabelle formula, replacing by Vars
   all subterms not intelligible to SVC.  
   Do not present "raw" terms to expr_of; the translation could be unsound!*)
 fun abstract t =
  let
    val params = Term.strip_all_vars t
    and body   = Term.strip_all_body t
    val Us = map #2 params
    val nPar = length params
    val vname = ref "V_a"
    val pairs = ref ([] : (term*term) list)
    fun insert t = 
	let val T = fastype_of t
	    val v = Unify.combound (Var ((!vname,0), Us--->T),
				    0, nPar)
	in  vname := bump_string (!vname); 
	    pairs := (t, v) :: !pairs;
	    v
	end;
    fun replace t = 
	case t of
	    Free _  => t  (*but not existing Vars, lest the names clash*)
	  | Bound _ => t
	  | _ => (case gen_assoc (op aconv) (!pairs, t) of
		      Some v => v
		    | None   => insert t)
    (*abstraction of a real/rational expression*)
    fun rat ((c as Const("op +", _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const("op -", _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const("op /", _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const("op *", _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const("uminus", _)) $ x) = c $ (rat x)
      | rat ((c as Const("RealDef.0r", _))) = c
      | rat ((c as Const("RealDef.1r", _))) = c 
      | rat (t as Const("Numeral.number_of", _) $ w) = t
      | rat t = replace t
    (*abstraction of an integer expression: no div, mod*)
    fun int ((c as Const("op +", _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const("op -", _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const("op *", _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const("uminus", _)) $ x) = c $ (int x)
      | int (t as Const("Numeral.number_of", _) $ w) = t
      | int t = replace t
    (*abstraction of a natural number expression: no minus*)
    fun nat ((c as Const("op +", _)) $ x $ y) = c $ (nat x) $ (nat y)
      | nat ((c as Const("op *", _)) $ x $ y) = c $ (nat x) $ (nat y)
      | nat ((c as Const("Suc", _)) $ x) = c $ (nat x)
      | nat (t as Const("0", _)) = t
      | nat (t as Const("Numeral.number_of", _) $ w) = t
      | nat t = replace t
    (*abstraction of a relation: =, <, <=*)
    fun rel (T, c $ x $ y) =
	    if T = HOLogic.realT then c $ (rat x) $ (rat y)
	    else if T = HOLogic.intT then c $ (int x) $ (int y)
	    else if T = HOLogic.natT then c $ (nat x) $ (nat y)
	    else if T = HOLogic.boolT then c $ (fm x) $ (fm y)
	    else replace (c $ x $ y)   (*non-numeric comparison*)
    (*abstraction of a formula*)
    and fm ((c as Const("op &", _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const("op |", _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const("op -->", _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const("Not", _)) $ p) = c $ (fm p)
      | fm ((c as Const("True", _))) = c
      | fm ((c as Const("False", _))) = c
      | fm (t as Const("op =", Type ("fun", [T,_])) $ x $ y) = rel (T, t)
      | fm (t as Const("op <", Type ("fun", [T,_])) $ x $ y) = rel (T, t)
      | fm (t as Const("op <=", Type ("fun", [T,_])) $ x $ y) = rel (T, t)
      | fm t = replace t
    (*entry point, and abstraction of a meta-formula*)
    fun mt ((c as Const("Trueprop", _)) $ p) = c $ (fm p)
      | mt ((c as Const("==>", _)) $ p $ q)  = c $ (mt p) $ (mt q)
      | mt t = fm t  (*it might be a formula*)
  in (list_all (params, mt body), !pairs) end;

 (*The oracle proves not the original formula but the abstracted version*)
 fun oracle (sign, OracleExn P) = 
   let val (absP, _) = abstract P
       val dummy = if !trace then writeln ("Subgoal abstracted to\n" ^
					   Sign.string_of_term sign absP)
                   else ()
   in
       if valid (expr_of false absP) then absP
       else raise OracleExn P
   end;

end;
