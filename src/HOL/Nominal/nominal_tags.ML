(* ID: "$Id$"
   Authors: Julien Narboux and Christian Urban

   This file introduces the infrastructure for the lemma 
   declaration "eqvt" "bij" and "fresh".

   By attaching [eqvt] [bij] or [fresh] to a lemma, the lemma gets stored 
   in a data-slot in the theory context. Possible modifiers
   are [tag add] and [tag del] for adding and deleting,
   respectively the lemma from the data-slot.  
*)

signature EQVT_RULES =
sig
  val print_eqvtset: Proof.context -> unit
  val eqvt_add: attribute
  val eqvt_del: attribute
  val setup: theory -> theory

  val EQVT_DEBUG : bool ref
end;

structure EqvtRules: EQVT_RULES =
struct

structure Data = GenericDataFun
(
  val name = "HOL/Nominal/eqvt";
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Drule.merge_rules;
  fun print context rules =
    Pretty.writeln (Pretty.big_list "Equivariance lemmas:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

(* Exception for when a theorem does not conform with form of an equivariance lemma. *)
(* There are two forms: one is an implication (for relations) and the other is an    *)
(* equality (for functions). In the implication-case, say P ==> Q, Q must be equal   *)
(* to P except that every free variable of Q, say x, is replaced by pi o x. In the   *)
(* equality case, say lhs = rhs, the lhs must be of the form pi o t and the rhs must *)
(* be equal to t except that every free variable, say x, is replaced by pi o x. In   *)
(* the implicational case it is also checked that the variables and permutation fit  *)
(* together, i.e. are of the right "pt_class", so that a stronger version of the     *)
(* eqality-lemma can be derived. *)
exception EQVT_FORM;

val print_eqvtset = Data.print o Context.Proof;

(* FIXME: should be a function in a library *)
fun mk_permT T = HOLogic.listT (HOLogic.mk_prodT (T, T));

val perm_bool = thm "perm_bool";

val EQVT_DEBUG = ref false;

fun tactic (msg,tac) = 
    if !EQVT_DEBUG 
    then (EVERY [tac, print_tac ("after "^msg)])
    else tac 

fun tactic_eqvt ctx orig_thm pi typi = 
    let 
        val mypi = Thm.cterm_of ctx (Var (pi,typi))
        val mypifree = Thm.cterm_of ctx (Const ("List.rev",typi --> typi) $ Free (fst pi,typi))
        val perm_pi_simp = PureThy.get_thms ctx (Name "perm_pi_simp")
    in
        EVERY [tactic ("iffI applied",rtac iffI 1), 
               tactic ("simplifies with orig_thm and perm_bool", 
                          asm_full_simp_tac (HOL_basic_ss addsimps [perm_bool,orig_thm]) 1), 
               tactic ("applies orig_thm instantiated with rev pi",
                          dtac (Drule.cterm_instantiate [(mypi,mypifree)] orig_thm) 1), 
               tactic ("getting rid of all remaining perms",
                          full_simp_tac (HOL_basic_ss addsimps (perm_bool::perm_pi_simp)) 1)] 
    end;

fun get_derived_thm thy hyp concl orig_thm pi typi =
   let 
       val lhs = (Const("Nominal.perm", typi --> HOLogic.boolT --> HOLogic.boolT) $ Var(pi,typi) $ hyp)
       val goal_term = Logic.unvarify (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,concl))) 
       val _ = Display.print_cterm (cterm_of thy goal_term) 
   in	
     Goal.prove_global thy [] [] goal_term (fn _ => (tactic_eqvt thy orig_thm pi typi)) 
   end

(* FIXME: something naughty here, but as long as there is no infrastructure to expose *)
(* the eqvt_thm_list to the user, we have to manually update the context and the      *)
(* thm-list eqvt *)
fun update_context flag thms context =
  let 
     val context' = fold (fn thm => Data.map (flag thm)) thms context 
  in 
    Context.mapping (snd o PureThy.add_thmss [(("eqvt",Data.get context'),[])]) I context'
  end;

(* replaces every variable, say x, in t with pi o x *) 
fun apply_pi trm (pi,typi) =
  let 
    fun only_vars t =
       (case t of
          Var (n,ty) => (Const ("Nominal.perm",typi --> ty --> ty) $ (Var (pi,typi)) $ (Var (n,ty)))
        | _ => t)
  in 
     map_aterms only_vars trm 
  end;

(* returns *the* pi which is in front of all variables, provided there *)
(* exists such a pi; otherwise raises EQVT_FORM                        *)
fun get_pi t thy =
  let fun get_pi_aux s =
        (case s of
          (Const ("Nominal.perm",typrm) $ 
             (Var (pi,typi as Type("List.list",[Type ("*",[Type (tyatm,[]),_])]))) $ 
               (Var (n,ty))) => 
             let
		(* FIXME: this should be an operation the library *)
                val class_name = (NameSpace.map_base (fn s => "pt_"^s) tyatm) 
	     in 
		if (Type.of_sort (Sign.tsig_of thy) (ty,[class_name])) 
                then [(pi,typi)] 
                else raise EQVT_FORM 
             end 
        | Abs (_,_,t1) => get_pi_aux t1
        | (t1 $ t2) => get_pi_aux t1 @ get_pi_aux t2
        | _ => [])  
  in 
    (* collect first all pi's in front of variables in t and then use distinct *)
    (* to ensure that all pi's must have been the same, i.e. distinct returns  *)
    (* a singleton-list  *)
    (case (distinct (op =) (get_pi_aux t)) of 
      [(pi,typi)] => (pi,typi)
    | _ => raise EQVT_FORM)
  end;

(* Either adds a theorem (orig_thm) to or deletes one from the equivaraince *)
(* lemma list depending on flag. To be added the lemma has to satisfy a     *)
(* certain form. *) 
fun eqvt_add_del_aux flag orig_thm context =
  let 
    val thy = Context.theory_of context
    val thms_to_be_added = (case (prop_of orig_thm) of
        (* case: eqvt-lemma is of the implicational form *) 
        (Const("==>", _) $ (Const ("Trueprop",_) $ hyp) $ (Const ("Trueprop",_) $ concl)) =>
          let  
            val (pi,typi) = get_pi concl thy
          in
             if (apply_pi hyp (pi,typi) = concl)
             then 
               (warning ("equivariance lemma of the relational form");
                [orig_thm, get_derived_thm thy hyp concl orig_thm pi typi])
             else raise EQVT_FORM
          end
        (* case: eqvt-lemma is of the equational form *)  
      | (Const ("Trueprop", _) $ (Const ("op =", _) $ 
            (Const ("Nominal.perm",_) $ Var (pi,typi) $ lhs) $ rhs)) =>
	      (if (apply_pi lhs (pi,typi)) = rhs 
               then [orig_thm] 
               else raise EQVT_FORM)
      | _ => raise EQVT_FORM)
  in 
      update_context flag thms_to_be_added context
  end
  handle EQVT_FORM => 
      error (string_of_thm orig_thm ^ " does not comply with the form of an equivariance lemma.")

val eqvt_add = Thm.declaration_attribute (eqvt_add_del_aux Drule.add_rule); 
val eqvt_del = Thm.declaration_attribute (eqvt_add_del_aux Drule.del_rule);

val setup =
  Data.init #>
  Attrib.add_attributes [("eqvt", Attrib.add_del_args eqvt_add eqvt_del, "equivariance rules")];

end;



signature BIJ_RULES =
sig
  val print_bijset: Proof.context -> unit
  val bij_add: attribute
  val bij_del: attribute
  val setup: theory -> theory
end;

structure BijRules: BIJ_RULES =
struct

structure Data = GenericDataFun
(
  val name = "HOL/Nominal/bij";
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Drule.merge_rules;
  fun print context rules =
    Pretty.writeln (Pretty.big_list "Bijection lemmas:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

val print_bijset = Data.print o Context.Proof;

fun bij_add_del_aux f = fn th => fn context =>
   let val new_context = Data.map (f th) context
   in 
       Context.mapping (snd o PureThy.add_thmss [(("bij",Data.get new_context),[])]) I new_context
   end

val bij_add = Thm.declaration_attribute (bij_add_del_aux Drule.add_rule); 
val bij_del = Thm.declaration_attribute (bij_add_del_aux Drule.del_rule);

val setup =
  Data.init #>
  Attrib.add_attributes [("bij", Attrib.add_del_args bij_add bij_del, "bijection rules")];

end;


signature FRESH_RULES =
sig
  val print_freshset: Proof.context -> unit
  val fresh_add: attribute
  val fresh_del: attribute
  val setup: theory -> theory
end;

structure FreshRules: FRESH_RULES =
struct

structure Data = GenericDataFun
(
  val name = "HOL/Nominal/fresh";
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Drule.merge_rules;
  fun print context rules =
    Pretty.writeln (Pretty.big_list "Freshness lemmas:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

val print_freshset = Data.print o Context.Proof;

fun fresh_add_del_aux f = fn th => fn context =>
   let val new_context = Data.map (f th) context
   in 
       Context.mapping (snd o PureThy.add_thmss [(("fresh",Data.get new_context),[])]) I new_context
   end

val fresh_add = Thm.declaration_attribute (fresh_add_del_aux Drule.add_rule); 
val fresh_del = Thm.declaration_attribute (fresh_add_del_aux Drule.del_rule);

val setup =
  Data.init #>
  Attrib.add_attributes [("fresh", Attrib.add_del_args fresh_add fresh_del, "freshness rules")];

end;

(* Thm.declaration_attribute is of type (thm -> Context.generic -> Context.generic) -> attribute *)

(* Thm.declaration_attribute has type (thm -> Context.generic -> Context.generic) -> attribute *)

(* Drule.add_rule has type thm -> thm list -> thm list *)

(* Data.map has type thm list -> thm list -> Context.generic -> Context.generic *)

(* add_del_args is of type attribute -> attribute -> src -> attribute *)