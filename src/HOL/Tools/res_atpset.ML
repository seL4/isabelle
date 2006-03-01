(*  ID:         $Id$
    Author:     Jia Meng, NICTA 

Set of rules used for ATPs
*)

structure ResAtpSet =

struct

datatype atpset = AtpSet of thm list


val mem_thm = member Drule.eq_thm_prop;
val rem_thm = remove Drule.eq_thm_prop;

val empty_atpset = AtpSet [];

fun add_atp_rule (thm,AtpSet thms) = 
    if mem_thm thms thm then (warning ("Ignoring duplicate ATP rules\n" ^ string_of_thm thm); AtpSet thms)
    else
	AtpSet (thm::thms);

fun add_atp_rule' thm ars = add_atp_rule (thm,ars);
fun add_atp_rules (ars,thms) =  foldl add_atp_rule ars thms;

fun del_atp_rule (thm,AtpSet thms) = 
    if mem_thm thms thm then AtpSet (rem_thm thm thms)
    else
	(warning "Undeclared rule for ATPs"; AtpSet thms);

fun del_atp_rule' thm ars = del_atp_rule (thm,ars);

fun del_atp_rules (ars,thms) = foldl del_atp_rule ars thms;

fun merge_atpset (ars1, AtpSet thms2) = add_atp_rules (ars1,thms2);

fun print_atpset (AtpSet thms) =
    let val pretty_thms = map Display.pretty_thm in
	[Pretty.big_list "Rules for ATPs:" (pretty_thms thms)]
	    |> Pretty.chunks |> Pretty.writeln
    end;


(* global AtpSet *)

structure GlobalAtpSet = TheoryDataFun
(struct
  val name = "AtpSet";
  type T = atpset ref;
  
  val empty = ref empty_atpset;
  fun copy (ref atpst) = ref atpst : T;
  val extend = copy;
  fun merge _ (ref atpst1, ref atpst2) =
      ref (merge_atpset (atpst1, atpst2));
  fun print (thy: Theory.theory) (ref atpst) = print_atpset atpst;
end);

val print_AtpSet = GlobalAtpSet.print; 
val get_AtpSet = ! o GlobalAtpSet.get;

val change_AtpSet_of = change o GlobalAtpSet.get;
fun change_AtpSet f = change_AtpSet_of (Context.the_context ()) f;


fun AtpSet_of thy = get_AtpSet thy;

fun Add_AtpRs args = change_AtpSet (fn ars => add_atp_rules (ars,args));

fun Del_AtpRs args = change_AtpSet (fn ars => del_atp_rules (ars,args));


(* local AtpSet *)

structure LocalAtpSet = ProofDataFun
(struct
  val name = "AtpSet";
  type T = atpset;
  val init = get_AtpSet;
  fun print _ atpst = print_atpset atpst;
end);

val print_local_AtpSet = LocalAtpSet.print;

val get_local_AtpSet = LocalAtpSet.get;

val put_local_AtpSet = LocalAtpSet.put;

fun local_AtpSet_of ctxt = get_local_AtpSet;


(* attributes *)
fun attrib f = Thm.declaration_attribute (fn th =>
   fn Context.Theory thy => (change_AtpSet_of thy (f th); Context.Theory thy)
    | Context.Proof ctxt => Context.Proof (LocalAtpSet.map (f th) ctxt));


val add_rule = attrib add_atp_rule';
val del_rule = attrib del_atp_rule';

val atpN = "atp";

val setup_attrs = Attrib.add_attributes
[(atpN, Attrib.add_del_args add_rule del_rule, "declaration of ATP rules")];

val setup = GlobalAtpSet.init #> LocalAtpSet.init #> setup_attrs;

end;