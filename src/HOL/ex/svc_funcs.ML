(*  Title:      HOL/ex/svc_funcs.ML
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Translation functions for the interface to SVC.

Based upon the work of Soren T. Heilmann

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
 val trace = Unsynchronized.ref false;

 datatype expr =
     Buildin of string * expr list
   | Interp of string * expr list
   | UnInterp of string * expr list
   | FalseExpr
   | TrueExpr
   | Int of int
   | Rat of int * int;

 fun is_intnat T = T = HOLogic.intT orelse T = HOLogic.natT;

 fun is_numeric T = is_intnat T orelse T = HOLogic.realT;

 fun is_numeric_op T = is_numeric (domain_type T);

 fun toString t =
     let fun ue (Buildin(s, l)) =
             "(" ^ s ^ (Library.foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
           | ue (Interp(s, l)) =
             "{" ^ s ^ (Library.foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ "} "
           | ue (UnInterp(s, l)) =
             "(" ^ s ^ (Library.foldl (fn (a, b) => a ^ " " ^ (ue b)) ("", l)) ^ ") "
           | ue (FalseExpr) = "FALSE "
           | ue (TrueExpr)  = "TRUE "
           | ue (Int i)     = signed_string_of_int i ^ " "
           | ue (Rat(i, j)) = signed_string_of_int i ^ "|" ^ signed_string_of_int j ^ " "
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
      val _ = if !trace then tracing ("Calling SVC:\n" ^ svc_input) else ()
      val svc_input_file  = File.tmp_path (Path.basic "SVM_in");
      val svc_output_file = File.tmp_path (Path.basic "SVM_out");
      val _ = (File.write svc_input_file svc_input;
               #1 (system_out (check_valid ^ " -dump-result " ^
                        File.shell_path svc_output_file ^
                        " " ^ File.shell_path svc_input_file ^
                        ">/dev/null 2>&1")))
      val svc_output =
        (case try File.read svc_output_file of
          SOME out => out
        | NONE => error "SVC returned no output");
  in
      if ! trace then tracing ("SVC Returns:\n" ^ svc_output)
      else (File.rm svc_input_file; File.rm svc_output_file);
      String.isPrefix "VALID" svc_output
  end

 fun fail t = raise TERM ("SVC oracle", [t]);

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
           | Const(@{const_name HOL.less}, Type ("fun", [T,_]))  => (t, is_intnat T)
           | Const(@{const_name HOL.less_eq}, Type ("fun", [T,_])) => (t, is_intnat T)
           | _ => (t, false)
         end
   in #1 o tag end;

 (*Map expression e to 0<=a --> e, where "a" is the name of a nat variable*)
 fun add_nat_var a e =
     Buildin("=>", [Buildin("<=", [Int 0, UnInterp (a, [])]),
                    e]);

 fun param_string [] = ""
   | param_string is = "_" ^ space_implode "_" (map string_of_int is)

 (*Translate an Isabelle formula into an SVC expression
   pos ["positive"]: true if an assumption, false if a goal*)
 fun expr_of pos t =
  let
    val params = rev (Term.rename_wrt_term t (Term.strip_all_vars t))
    and body   = Term.strip_all_body t
    val nat_vars = Unsynchronized.ref ([] : string list)
    (*translation of a variable: record all natural numbers*)
    fun trans_var (a,T,is) =
        (if T = HOLogic.natT then nat_vars := (insert (op =) a (!nat_vars))
                             else ();
         UnInterp (a ^ param_string is, []))
    (*A variable, perhaps applied to a series of parameters*)
    fun var (Free(a,T), is)      = trans_var ("F_" ^ a, T, is)
      | var (Var((a, 0), T), is) = trans_var (a, T, is)
      | var (Bound i, is)        =
          let val (a,T) = List.nth (params, i)
          in  trans_var ("B_" ^ a, T, is)  end
      | var (t $ Bound i, is)    = var(t,i::is)
            (*removing a parameter from a Var: the bound var index will
               become part of the Var's name*)
      | var (t,_) = fail t;
    (*translation of a literal*)
    val lit = snd o HOLogic.dest_number;
    (*translation of a literal expression [no variables]*)
    fun litExp (Const(@{const_name HOL.plus}, T) $ x $ y) =
          if is_numeric_op T then (litExp x) + (litExp y)
          else fail t
      | litExp (Const(@{const_name HOL.minus}, T) $ x $ y) =
          if is_numeric_op T then (litExp x) - (litExp y)
          else fail t
      | litExp (Const(@{const_name HOL.times}, T) $ x $ y) =
          if is_numeric_op T then (litExp x) * (litExp y)
          else fail t
      | litExp (Const(@{const_name HOL.uminus}, T) $ x)   =
          if is_numeric_op T then ~(litExp x)
          else fail t
      | litExp t = lit t
                   handle Match => fail t
    (*translation of a real/rational expression*)
    fun suc t = Interp("+", [Int 1, t])
    fun tm (Const(@{const_name Suc}, T) $ x) = suc (tm x)
      | tm (Const(@{const_name HOL.plus}, T) $ x $ y) =
          if is_numeric_op T then Interp("+", [tm x, tm y])
          else fail t
      | tm (Const(@{const_name HOL.minus}, T) $ x $ y) =
          if is_numeric_op T then
              Interp("+", [tm x, Interp("*", [Int ~1, tm y])])
          else fail t
      | tm (Const(@{const_name HOL.times}, T) $ x $ y) =
          if is_numeric_op T then Interp("*", [tm x, tm y])
          else fail t
      | tm (Const(@{const_name HOL.inverse}, T) $ x) =
          if domain_type T = HOLogic.realT then
              Rat(1, litExp x)
          else fail t
      | tm (Const(@{const_name HOL.uminus}, T) $ x) =
          if is_numeric_op T then Interp("*", [Int ~1, tm x])
          else fail t
      | tm t = Int (lit t)
               handle Match => var (t,[])
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
                   else fail t
            end
        (*inequalities: possible types are nat, int, real*)
      | fm pos (t as Const(@{const_name HOL.less},  Type ("fun", [T,_])) $ x $ y) =
            if not pos orelse T = HOLogic.realT then
                Buildin("<", [tm x, tm y])
            else if is_intnat T then
                Buildin("<=", [suc (tm x), tm y])
            else fail t
      | fm pos (t as Const(@{const_name HOL.less_eq},  Type ("fun", [T,_])) $ x $ y) =
            if pos orelse T = HOLogic.realT then
                Buildin("<=", [tm x, tm y])
            else if is_intnat T then
                Buildin("<", [tm x, suc (tm y)])
            else fail t
      | fm pos t = var(t,[]);
      (*entry point, and translation of a meta-formula*)
      fun mt pos ((c as Const("Trueprop", _)) $ p) = fm pos (iff_tag p)
        | mt pos ((c as Const("==>", _)) $ p $ q) =
            Buildin("=>", [mt (not pos) p, mt pos q])
        | mt pos t = fm pos (iff_tag t)  (*it might be a formula*)

      val body_e = mt pos body  (*evaluate now to assign into !nat_vars*)
  in
     fold_rev add_nat_var (!nat_vars) body_e
  end;


 (*The oracle proves the given formula, if possible*)
  fun oracle ct =
    let
      val thy = Thm.theory_of_cterm ct;
      val t = Thm.term_of ct;
      val _ =
        if ! trace then tracing ("SVC oracle: problem is\n" ^ Syntax.string_of_term_global thy t)
       else ();
    in if valid (expr_of false t) then ct else fail t end;

end;
