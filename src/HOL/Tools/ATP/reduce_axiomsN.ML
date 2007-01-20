(* Authors: Jia Meng, NICTA and Lawrence C Paulson, Cambridge University Computer Laboratory
   ID: $Id$
   Filtering strategies *)

(*A surprising number of theorems contain only a few significant constants.
  These include all induction rules, and other general theorems. Filtering
  theorems in clause form reveals these complexities in the form of Skolem 
  functions. If we were instead to filter theorems in their natural form,
  some other method of measuring theorem complexity would become necessary.*)

structure ReduceAxiomsN =
struct

val run_relevance_filter = ref true;
val theory_const = ref true;
val pass_mark = ref 0.5;
val convergence = ref 3.2;    (*Higher numbers allow longer inference chains*)
val max_new = ref 60;         (*Limits how many clauses can be picked up per stage*)
val follow_defs = ref false;  (*Follow definitions. Makes problems bigger.*)

fun log_weight2 (x:real) = 1.0 + 2.0/Math.ln (x+1.0);

(*The default seems best in practice. A constant function of one ignores
  the constant frequencies.*)
val weight_fn = ref log_weight2;


(*Including equality in this list might be expected to stop rules like subset_antisym from
  being chosen, but for some reason filtering works better with them listed. The
  logical signs All, Ex, &, and --> are omitted because any remaining occurrrences
  must be within comprehensions.*)
val standard_consts = ["Trueprop","==>","all","==","op |","Not","op ="];


(*** constants with types ***)

(*An abstraction of Isabelle types*)
datatype const_typ =  CTVar | CType of string * const_typ list

(*Is the second type an instance of the first one?*)
fun match_type (CType(con1,args1)) (CType(con2,args2)) = 
      con1=con2 andalso match_types args1 args2
  | match_type CTVar _ = true
  | match_type _ CTVar = false
and match_types [] [] = true
  | match_types (a1::as1) (a2::as2) = match_type a1 a2 andalso match_types as1 as2;

(*Is there a unifiable constant?*)
fun uni_mem gctab (c,c_typ) =
  case Symtab.lookup gctab c of
      NONE => false
    | SOME ctyps_list => exists (match_types c_typ) ctyps_list;
  
(*Maps a "real" type to a const_typ*)
fun const_typ_of (Type (c,typs)) = CType (c, map const_typ_of typs) 
  | const_typ_of (TFree _) = CTVar
  | const_typ_of (TVar _) = CTVar

(*Pairs a constant with the list of its type instantiations (using const_typ)*)
fun const_with_typ thy (c,typ) = 
    let val tvars = Sign.const_typargs thy (c,typ)
    in (c, map const_typ_of tvars) end
    handle TYPE _ => (c,[]);   (*Variable (locale constant): monomorphic*)   

(*Add a const/type pair to the table, but a [] entry means a standard connective,
  which we ignore.*)
fun add_const_typ_table ((c,ctyps), tab) =
  Symtab.map_default (c, [ctyps]) (fn [] => [] | ctyps_list => insert (op =) ctyps ctyps_list) 
    tab;

(*Free variables are included, as well as constants, to handle locales*)
fun add_term_consts_typs_rm thy (Const(c, typ), tab) =
      add_const_typ_table (const_with_typ thy (c,typ), tab) 
  | add_term_consts_typs_rm thy (Free(c, typ), tab) =
      add_const_typ_table (const_with_typ thy (c,typ), tab) 
  | add_term_consts_typs_rm thy (t $ u, tab) =
      add_term_consts_typs_rm thy (t, add_term_consts_typs_rm thy (u, tab))
  | add_term_consts_typs_rm thy (Abs(_,_,t), tab) = add_term_consts_typs_rm thy (t, tab)
  | add_term_consts_typs_rm thy (_, tab) = tab;

(*The empty list here indicates that the constant is being ignored*)
fun add_standard_const (s,tab) = Symtab.update (s,[]) tab;

val null_const_tab : const_typ list list Symtab.table = 
    foldl add_standard_const Symtab.empty standard_consts;

fun get_goal_consts_typs thy = foldl (add_term_consts_typs_rm thy) null_const_tab;

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun const_prop_of th =
 if !theory_const then
  let val name = Context.theory_name (theory_of_thm th)
      val t = Const (name ^ ". 1", HOLogic.boolT)
  in  t $ prop_of th  end
 else prop_of th;

(**** Constant / Type Frequencies ****)

(*A two-dimensional symbol table counts frequencies of constants. It's keyed first by
  constant name and second by its list of type instantiations. For the latter, we need
  a linear ordering on type const_typ list.*)
  
local

fun cons_nr CTVar = 0
  | cons_nr (CType _) = 1;

in

fun const_typ_ord TU =
  case TU of
    (CType (a, Ts), CType (b, Us)) =>
      (case fast_string_ord(a,b) of EQUAL => dict_ord const_typ_ord (Ts,Us) | ord => ord)
  | (T, U) => int_ord (cons_nr T, cons_nr U);

end;

structure CTtab = TableFun(type key = const_typ list val ord = dict_ord const_typ_ord);

fun count_axiom_consts thy ((thm,_), tab) = 
  let fun count_const (a, T, tab) =
	let val (c, cts) = const_with_typ thy (a,T)
	in  (*Two-dimensional table update. Constant maps to types maps to count.*)
	    Symtab.map_default (c, CTtab.empty) 
	                       (CTtab.map_default (cts,0) (fn n => n+1)) tab
	end
      fun count_term_consts (Const(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (Free(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (t $ u, tab) =
	    count_term_consts (t, count_term_consts (u, tab))
	| count_term_consts (Abs(_,_,t), tab) = count_term_consts (t, tab)
	| count_term_consts (_, tab) = tab
  in  count_term_consts (const_prop_of thm, tab)  end;


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency ctab (c, cts) =
  let val pairs = CTtab.dest (Option.valOf (Symtab.lookup ctab c))
      fun add ((cts',m), n) = if match_types cts cts' then m+n else n
  in  List.foldl add 0 pairs  end;

(*Add in a constant's weight, as determined by its frequency.*)
fun add_ct_weight ctab ((c,T), w) =
  w + !weight_fn (real (const_frequency ctab (c,T)));

(*Relevant constants are weighted according to frequency, 
  but irrelevant constants are simply counted. Otherwise, Skolem functions,
  which are rare, would harm a clause's chances of being picked.*)
fun clause_weight ctab gctyps consts_typs =
    let val rel = filter (uni_mem gctyps) consts_typs
        val rel_weight = List.foldl (add_ct_weight ctab) 0.0 rel
    in
	rel_weight / (rel_weight + real (length consts_typs - length rel))
    end;
    
(*Multiplies out to a list of pairs: 'a * 'b list -> ('a * 'b) list -> ('a * 'b) list*)
fun add_expand_pairs (x,ys) xys = foldl (fn (y,acc) => (x,y)::acc) xys ys;

fun consts_typs_of_term thy t = 
  let val tab = add_term_consts_typs_rm thy (t, null_const_tab)
  in  Symtab.fold add_expand_pairs tab []  end;

fun pair_consts_typs_axiom thy (thm,name) =
    ((thm,name), (consts_typs_of_term thy (const_prop_of thm)));

exception ConstFree;
fun dest_ConstFree (Const aT) = aT
  | dest_ConstFree (Free aT) = aT
  | dest_ConstFree _ = raise ConstFree;

(*Look for definitions of the form f ?x1 ... ?xn = t, but not reversed.*)
fun defines thy (thm,(name,n)) gctypes =
    let val tm = prop_of thm
	fun defs lhs rhs =
            let val (rator,args) = strip_comb lhs
		val ct = const_with_typ thy (dest_ConstFree rator)
            in  forall is_Var args andalso uni_mem gctypes ct andalso
                Term.add_vars rhs [] subset Term.add_vars lhs []
            end
	    handle ConstFree => false
    in    
	case tm of Const ("Trueprop",_) $ (Const("op =",_) $ lhs $ rhs) => 
		   defs lhs rhs andalso
		   (Output.debug (fn () => "Definition found: " ^ name ^ "_" ^ Int.toString n); true)
		 | _ => false
    end;

type annotd_cls = (thm * (string * int)) * ((string * const_typ list) list);
       
(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_,w1),(_,w2)) = Real.compare (w2,w1);

(*Limit the number of new clauses, to prevent runaway acceptance.*)
fun take_best (newpairs : (annotd_cls*real) list) =
  let val nnew = length newpairs
  in
    if nnew <= !max_new then (map #1 newpairs, [])
    else 
      let val cls = sort compare_pairs newpairs
          val accepted = List.take (cls, !max_new)
      in
        Output.debug (fn () => ("Number of candidates, " ^ Int.toString nnew ^ 
		       ", exceeds the limit of " ^ Int.toString (!max_new)));
        Output.debug (fn () => ("Effective pass mark: " ^ Real.toString (#2 (List.last accepted))));
        Output.debug (fn () => "Actually passed: " ^
          space_implode ", " (map (fn (((_,(name,_)),_),_) => name) accepted));

	(map #1 accepted, map #1 (List.drop (cls, !max_new)))
      end
  end;

fun relevant_clauses thy ctab p rel_consts =
  let fun relevant ([],_) [] = [] : (thm * (string * int)) list  (*Nothing added this iteration*)
	| relevant (newpairs,rejects) [] =
	    let val (newrels,more_rejects) = take_best newpairs
		val new_consts = List.concat (map #2 newrels)
		val rel_consts' = foldl add_const_typ_table rel_consts new_consts
		val newp = p + (1.0-p) / !convergence
	    in
              Output.debug (fn () => ("relevant this iteration: " ^ Int.toString (length newrels)));
	       (map #1 newrels) @ 
	       (relevant_clauses thy ctab newp rel_consts' (more_rejects@rejects))
	    end
	| relevant (newrels,rejects) ((ax as (clsthm as (_,(name,n)),consts_typs)) :: axs) =
	    let val weight = clause_weight ctab rel_consts consts_typs
	    in
	      if p <= weight orelse (!follow_defs andalso defines thy clsthm rel_consts)
	      then (Output.debug (fn () => (name ^ " passes: " ^ Real.toString weight));
	            relevant ((ax,weight)::newrels, rejects) axs)
	      else relevant (newrels, ax::rejects) axs
	    end
    in  Output.debug (fn () => ("relevant_clauses, current pass mark = " ^ Real.toString p));
        relevant ([],[]) 
    end;
	
fun relevance_filter thy axioms goals = 
 if !run_relevance_filter andalso !pass_mark >= 0.1
 then
  let val _ = Output.debug (fn () => "Start of relevance filtering");
      val const_tab = List.foldl (count_axiom_consts thy) Symtab.empty axioms
      val goal_const_tab = get_goal_consts_typs thy goals
      val _ = Output.debug (fn () => ("Initial constants: " ^
                                 space_implode ", " (Symtab.keys goal_const_tab)));
      val rels = relevant_clauses thy const_tab (!pass_mark) 
                   goal_const_tab  (map (pair_consts_typs_axiom thy) axioms)
  in
      Output.debug (fn () => ("Total relevant: " ^ Int.toString (length rels)));
      rels
  end
 else axioms;

end;
