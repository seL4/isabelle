(*  Title:      ZF/typechk
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Tactics for type checking -- from CTT
*)

infix 4 addTCs delTCs;

structure TypeCheck =
struct
datatype tcset =
    TC of {rules: thm list,	(*the type-checking rules*)
	   net: thm Net.net};   (*discrimination net of the same rules*)     



val mem_thm = gen_mem eq_thm
and rem_thm = gen_rem eq_thm;

fun addTC (cs as TC{rules, net}, th) =
  if mem_thm (th, rules) then 
	 (warning ("Ignoring duplicate type-checking rule\n" ^ 
		   string_of_thm th);
	  cs)
  else
      TC{rules	= th::rules,
	 net = Net.insert_term ((concl_of th, th), net, K false)};


fun delTC (cs as TC{rules, net}, th) =
  if mem_thm (th, rules) then
      TC{net = Net.delete_term ((concl_of th, th), net, eq_thm),
	 rules	= rem_thm (rules,th)}
  else (warning ("No such type-checking rule\n" ^ (string_of_thm th)); 
	cs);

val op addTCs = foldl addTC;
val op delTCs = foldl delTC;


(*resolution using a net rather than rules*)
fun net_res_tac maxr net =
  SUBGOAL
    (fn (prem,i) =>
      let val rls = Net.unify_term net (Logic.strip_assums_concl prem)
      in 
	 if length rls <= maxr then resolve_tac rls i else no_tac
      end);

fun is_rigid_elem (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) = 
      not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  eq_assume_tac i);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).  
  match_tac is too strict; would refuse to instantiate ?A*)
fun typecheck_step_tac (TC{net,...}) =
    FIRSTGOAL (test_assume_tac ORELSE' net_res_tac 3 net);

fun typecheck_tac tcset = REPEAT (typecheck_step_tac tcset);

(*Compiles a term-net for speed*)
val basic_res_tac = net_resolve_tac [TrueI,refl,reflexive_thm,iff_refl,
				     ballI,allI,conjI,impI];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_solver_tac tcset hyps = SELECT_GOAL
    (DEPTH_SOLVE (etac FalseE 1
		  ORELSE basic_res_tac 1
		  ORELSE (ares_tac hyps 1
			  APPEND typecheck_step_tac tcset)));



fun merge_tc (TC{rules,net}, TC{rules=rules',net=net'}) =
    TC {rules = gen_union eq_thm (rules,rules'),
	net = Net.merge (net, net', eq_thm)};

(*print tcsets*)
fun print_tc (TC{rules,...}) =
    Pretty.writeln
       (Pretty.big_list "type-checking rules:" (map Display.pretty_thm rules));


structure TypecheckingArgs =
  struct
  val name = "ZF/type-checker";
  type T = tcset ref;
  val empty = ref (TC{rules=[], net=Net.empty});
  fun copy (ref tc) = ref tc;
  val prep_ext = copy;
  fun merge (ref tc1, ref tc2) = ref (merge_tc (tc1, tc2));
  fun print _ (ref tc) = print_tc tc;
  end;

structure TypecheckingData = TheoryDataFun(TypecheckingArgs);

val setup = [TypecheckingData.init];

val print_tcset = TypecheckingData.print;
val tcset_ref_of_sg = TypecheckingData.get_sg;
val tcset_ref_of = TypecheckingData.get;

(* access global tcset *)

val tcset_of_sg = ! o tcset_ref_of_sg;
val tcset_of = tcset_of_sg o sign_of;

val tcset = tcset_of o Context.the_context;
val tcset_ref = tcset_ref_of_sg o sign_of o Context.the_context;

(* change global tcset *)

fun change_tcset f x = tcset_ref () := (f (tcset (), x));

val AddTCs = change_tcset (op addTCs);
val DelTCs = change_tcset (op delTCs);

fun Typecheck_tac st = typecheck_tac (tcset()) st;

fun Type_solver_tac hyps = type_solver_tac (tcset()) hyps;
end;


open TypeCheck;



