(*
    ID:         $Id$
    Author:     Tobias Mayr

Additional theory file section for HOLCF: axioms 
*)

(*** new section of HOLCF : axioms 
     since rules are already internally called axioms,
     the new section is internally called ext_axioms res. eaxms *)

signature THY_AXIOMS =
sig
 (* theory extenders : *)
 val add_ext_axioms   : (string * string) list -> (string * string) list
                        -> (string * string) list -> theory -> theory;
 val add_ext_axioms_i : (string * (typ option)) list -> 
                        (string * (typ option)) list ->
                        (string * term) list -> theory -> theory;
 val axioms_keywords    : string list;
 val axioms_sections    : (string * (ThyParse.token list -> 
                        (string * string) * ThyParse.token list)) list;
end;

structure ThyAxioms : THY_AXIOMS =
struct

open HOLCFlogic;

(** library ******************************************************)

fun apsnd_of_three f = fn (a,b,c) => (a,f b,c);

fun is_elem e list = exists (fn y => e=y) list

fun without l1 l2 = (* l1 without the elements of l2 *)
  filter (fn x => (not (is_elem x l2))) l1;

fun conc [e:string] = e
  | conc (head::tail) = head^", "^(conc tail)
  | conc [] = "";

fun appear varlist = (* all (x,_) for which (x,_) is in varlist *)
  filter (fn x => (exists (fn y => (fst x)=(fst y)) varlist)) 


(* all non unique elements of a list *)
fun doubles (hd::tl) = if   (is_elem hd tl)
                       then (hd::(doubles tl))
                       else (doubles tl)
  | doubles _ = [];


(* The main functions are the section parser ext_axiom_decls and the 
   theory extender add_ext_axioms. *)

(** theory extender : add_ext_axioms *)

(* forms a function from constrained varnames to their constraints 
   these constraints are then used local to each axiom, as an argument
   of read_def_cterm. Called by add_ext_axioms. *)
fun get_constraints_of_str sign ((vname,vtyp)::tail) = 
   if (vtyp <> "")
   then ((fn (x,_)=> if x=vname 
                      then Some (#T (rep_ctyp (read_ctyp sign vtyp)))
                      else raise Match)
        orelf (get_constraints_of_str sign tail))
   else (get_constraints_of_str sign tail)
  | get_constraints_of_str sign [] = K None;

(* does the same job for allready parsed optional constraints. 
   Called by add_ext_axioms_i. *)
fun get_constraints_of_typ sign ((vname,vtyp)::tail) = 
   if (is_some vtyp)
   then ((fn (x,_)=> if x=vname 
                      then vtyp
                      else raise Match)
        orelf (get_constraints_of_typ sign tail))
   else (get_constraints_of_typ sign tail)
  | get_constraints_of_typ sign [] = K None;


(* applies mkNotEqUU_in on the axiom and every Free that appears in the list
   and in the axiom. Called by check_and_extend. *)
fun add_prem axiom [] = axiom
  | add_prem axiom (vname::tl) =
 let val vterm = find_first (fn x => ((#1 o dest_Free) x = vname))
                            (term_frees axiom)
 in 
   add_prem  
     (if (is_some vterm) 
      then mkNotEqUU_in (the vterm) axiom
      else axiom)
     tl
 end

(* checks for uniqueness and completeness of var/defvar declarations, 
   and enriches the axiom term with premises. Called by add_ext_axioms(_i).*)
fun check_and_extend sign defvarl varl axiom =
  let
   val names_of_frees =  map (fst o dest_Free) 
                             (term_frees axiom);
   val all_decl_varnames = (defvarl @ varl);
   val undeclared = without names_of_frees all_decl_varnames;
   val doubles = doubles all_decl_varnames
  in
   if (doubles <> [])
   then 
    (error("Multiple declarations of one identifier in section axioms :\n"
           ^(conc doubles)))
   else ();
   if (undeclared <> [])
   then 
    (error("Undeclared identifiers in section axioms : \n"
           ^(conc undeclared)))
   else (); 
   add_prem axiom (rev defvarl)
  end; 

(* the next five only differ from the original add_axioms' subfunctions
   in the constraints argument for read_def_cterm *) 
local
 fun err_in_axm name =
   error ("The error(s) above occurred in axiom " ^ quote name); 

 fun no_vars tm =
   if null (term_vars tm) andalso null (term_tvars tm) then tm
   else error "Illegal schematic variable(s) in term"; 

 fun read_ext_cterm sign constraints = 
   #1 o read_def_cterm (sign, constraints, K None) [] true;

 (* only for add_ext_axioms (working on strings) *)
 fun read_ext_axm sg constraints (name,str) =
   (name, no_vars (term_of (read_ext_cterm sg constraints (str, propT))))
    handle ERROR => err_in_axm name;

 (* only for add_ext_axioms_i (working on terms) *)
 fun read_ext_axm_terms sg constraints (name,term) =
   (name, no_vars (#2(Sign.infer_types sg constraints  (K None) [] true 
                                       ([term], propT))))
    handle ERROR => err_in_axm name;

in

(******* THE THEORY EXTENDERS THEMSELVES *****)
 fun add_ext_axioms varlist defvarlist axioms theory =
  let val {sign, ...} = rep_theory theory;
      val constraints = get_constraints_of_str sign (defvarlist@varlist)
  in
    add_axioms_i (map (apsnd 
     (check_and_extend sign (map fst defvarlist) (map fst varlist)) o
               (read_ext_axm sign constraints)) axioms) theory
  end 

 fun add_ext_axioms_i varlist defvarlist axiom_terms theory =
  let val {sign, ...} = rep_theory theory;
      val constraints = get_constraints_of_typ sign (defvarlist@varlist)
  in
    add_axioms_i (map (apsnd (check_and_extend sign 
                               (map fst defvarlist) (map fst varlist)) o
                   (read_ext_axm_terms sign constraints)) axiom_terms) theory
  end
end;


(******** SECTION PARSER : ext_axiom_decls **********)
local 
 open ThyParse 

 (* as in the pure section 'rules' : 
    making the "val thmname = get_axiom thy thmname" list *)
 val mk_list_of_pairs = mk_big_list o map (mk_pair o apfst quote);
 fun mk_val ax = "val " ^ ax ^ " = get_axiom thy " ^ quote ax ^ ";";
 val mk_vals = cat_lines o map mk_val;

 (* making the call for the theory extender *) 
 fun mk_eaxms_decls ((vars,defvars),axms) = 
     ( "|> ThyAxioms.add_ext_axioms \n  " ^ 
       (mk_list_of_pairs vars) ^ "\n  " ^
       (mk_list_of_pairs defvars) ^ "\n  " ^
       (mk_list_of_pairs axms),
       mk_vals (map fst axms));

 (* parsing the concrete syntax *)    

 val axiom_decls = (repeat1 (ident -- !! string));

 val varlist = "vars" $$-- 
                 repeat1 (ident -- optional ("::" $$-- string) "\"\"");

 val defvarlist = "defvars" $$-- 
                    repeat1 (ident -- optional ("::" $$-- string) "\"\""); 

in

 val ext_axiom_decls = (optional varlist []) -- (optional defvarlist [])
                         -- ("in" $$-- axiom_decls) >> mk_eaxms_decls;
end; (* local *)


(**** new keywords and sections ************************************)

val axioms_keywords = ["vars", "defvars","in"];
     (* "::" is already a pure keyword *)

val axioms_sections = [("axioms" , ext_axiom_decls)]
                       
end; (* the structure *)
