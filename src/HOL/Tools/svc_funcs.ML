(*  Title:      HOL/Tools/svc_funcs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Translation functions for the interface to SVC

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
     Buildin of string * expr list
   | Interp of string * expr list
   | UnInterp of string * expr list
   | FalseExpr 
   | TrueExpr
   | Int of int
   | Rat of int * int;

 open BasisLibrary

 fun signedInt i = 
     if i < 0 then "-" ^ Int.toString (~i)
     else Int.toString i;
	 
 fun is_intnat T = T = HOLogic.intT orelse T = HOLogic.natT;
 
 fun is_numeric T = is_intnat T orelse T = HOLogic.realT;
 
 fun is_numeric_op T = is_numeric (domain_type T);

 fun toString t =
     let fun ue (Buildin(s, l)) = 
	     "(" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
	   | ue (Interp(s, l)) = 
	     "{" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ "} "
	   | ue (UnInterp(s, l)) = 
	     "(" ^ s ^ (foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
	   | ue (FalseExpr) = "FALSE "
	   | ue (TrueExpr)  = "TRUE "
	   | ue (Int i)     = (signedInt i) ^ " "
	   | ue (Rat(i, j)) = (signedInt i) ^ "|" ^ (signedInt j) ^ " "
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
  in
      if ! trace then writeln ("SVC Returns:\n" ^ svc_output)
      else (File.rm svc_input_file; File.rm svc_output_file);
      String.isPrefix "VALID" svc_output
  end

 (*New exception constructor for passing arguments to the oracle*)
 exception OracleExn of term;

 fun apply c args =
     let val (ts, bs) = ListPair.unzip args
     in  (list_comb(c,ts), exists I bs)  end;

 (*Determining whether the biconditionals must be unfolded: if there are
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
		 else (*might be numeric equality*) (t, is_intnat T)
	   | Const("op <", Type ("fun", [T,_]))  => (t, is_intnat T)
	   | Const("op <=", Type ("fun", [T,_])) => (t, is_intnat T)
	   | _ => (t, false)
	 end
   in #1 o tag end;

 (*Map expression e to 0<=a --> e, where "a" is the name of a nat variable*)
 fun add_nat_var (a, e) = 
     Buildin("=>", [Buildin("<=", [Int 0, UnInterp (a, [])]),
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
         UnInterp (a, []))
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
    fun litExp (Const("op +", T) $ x $ y) = 
	  if is_numeric_op T then (litExp x) + (litExp y)
          else raise OracleExn t
      | litExp (Const("op -", T) $ x $ y) = 
	  if is_numeric_op T then (litExp x) - (litExp y)
          else raise OracleExn t
      | litExp (Const("op *", T) $ x $ y) = 
	  if is_numeric_op T then (litExp x) * (litExp y)
          else raise OracleExn t
      | litExp (Const("uminus", T) $ x)   = 
	  if is_numeric_op T then ~(litExp x)
          else raise OracleExn t
      | litExp t = lit t 
		   handle Match => raise OracleExn t
    (*translation of a real/rational expression*)
    fun suc t = Interp("+", [Int 1, t])
    fun tm (Const("Suc", T) $ x) = suc (tm x)
      | tm (Const("op +", T) $ x $ y) = 
	  if is_numeric_op T then Interp("+", [tm x, tm y])
          else raise OracleExn t
      | tm (Const("op -", T) $ x $ y) = 
	  if is_numeric_op T then 
	      Interp("+", [tm x, Interp("*", [Int ~1, tm y])])
          else raise OracleExn t
      | tm (Const("op *", T) $ x $ y) = 
	  if is_numeric_op T then Interp("*", [tm x, tm y])
          else raise OracleExn t
      | tm (Const("RealDef.rinv", T) $ x) = 
	  if domain_type T = HOLogic.realT then 
	      Rat(1, litExp x)
          else raise OracleExn t
      | tm (Const("uminus", T) $ x) = 
	  if is_numeric_op T then Interp("*", [Int ~1, tm x])
          else raise OracleExn t
      | tm t = Int (lit t) 
	       handle Match => var t
    (*translation of a formula*)
    and fm pos (Const("op &", _) $ p $ q) =  
	    Buildin("AND", [fm pos p, fm pos q])
      | fm pos (Const("op |", _) $ p $ q) =  
	    Buildin("OR", [fm pos p, fm pos q])
      | fm pos (Const("op -->", _) $ p $ q) =  
	    Buildin("=>", [fm (not pos) p, fm pos q])
      | fm pos (Const("Not", _) $ p) =  
	    Buildin("NOT", [fm (not pos) p])
      | fm pos (Const("True", _)) = TrueExpr
      | fm pos (Const("False", _)) = FalseExpr
      | fm pos (Const("SVC_Oracle.iff_keep", _) $ p $ q) = 
	     (*polarity doesn't matter*)
	    Buildin("=", [fm pos p, fm pos q]) 
      | fm pos (Const("SVC_Oracle.iff_unfold", _) $ p $ q) = 
	    Buildin("AND",   (*unfolding uses both polarities*)
			 [Buildin("=>", [fm (not pos) p, fm pos q]),
			  Buildin("=>", [fm (not pos) q, fm pos p])])
      | fm pos (t as Const("op =", Type ("fun", [T,_])) $ x $ y) = 
	    let val tx = tm x and ty = tm y
		in if pos orelse T = HOLogic.realT then
		       Buildin("=", [tx, ty])
		   else if is_intnat T then
		       Buildin("AND", 
				    [Buildin("<", [tx, suc ty]), 
				     Buildin("<", [ty, suc tx])])
		   else raise OracleExn t
	    end
	(*inequalities: possible types are nat, int, real*)
      | fm pos (t as Const("op <",  Type ("fun", [T,_])) $ x $ y) = 
	    if not pos orelse T = HOLogic.realT then
		Buildin("<", [tm x, tm y])
	    else if is_intnat T then
		Buildin("<=", [suc (tm x), tm y])
	    else raise OracleExn t
      | fm pos (t as Const("op <=",  Type ("fun", [T,_])) $ x $ y) = 
	    if pos orelse T = HOLogic.realT then
		Buildin("<=", [tm x, tm y])
	    else if is_intnat T then
		Buildin("<", [tm x, suc (tm y)])
	    else raise OracleExn t
      | fm pos t = var t;
      (*entry point, and translation of a meta-formula*)
      fun mt pos ((c as Const("Trueprop", _)) $ p) = fm pos (iff_tag p)
	| mt pos ((c as Const("==>", _)) $ p $ q) = 
	    Buildin("=>", [mt (not pos) p, mt pos q])
	| mt pos t = fm pos (iff_tag t)  (*it might be a formula*)

      val body_e = mt pos body  (*evaluate now to assign into !nat_vars*)
  in 
     foldr add_nat_var (!nat_vars, body_e) 
  end;


 (*The oracle proves the given formula t, if possible*)
 fun oracle (sign, OracleExn t) = 
   let val dummy = if !trace then writeln ("Subgoal abstracted to\n" ^
					   Sign.string_of_term sign t)
                   else ()
   in
       if valid (expr_of false t) then t
       else raise OracleExn t
   end;

end;
