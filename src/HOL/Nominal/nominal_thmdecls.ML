(* ID: "$Id$"
   Authors: Julien Narboux and Christian Urban

   This file introduces the infrastructure for the lemma
   declaration "eqvts" "bijs" and "freshs".

   By attaching [eqvt] [bij] or [fresh] to a lemma, the lemma gets stored
   in a data-slot in the context. Possible modifiers
   are [attribute add] and [attribute del] for adding and deleting,
   respectively the lemma from the data-slot.
*)

signature NOMINAL_THMDECLS =
sig
  val print_data: Proof.context -> unit
  val eqvt_add: attribute
  val eqvt_del: attribute
  val eqvt_force_add: attribute
  val eqvt_force_del: attribute
  val setup: theory -> theory
  val get_eqvt_thms: Proof.context -> thm list
  val get_fresh_thms: Proof.context -> thm list
  val get_bij_thms: Proof.context -> thm list


  val NOMINAL_EQVT_DEBUG : bool ref
end;

structure NominalThmDecls: NOMINAL_THMDECLS =
struct

structure Data = GenericDataFun
(
  type T = {eqvts:thm list, freshs:thm list, bijs:thm list};
  val empty = ({eqvts=[], freshs=[], bijs=[]}:T);
  val extend = I;
  fun merge _ (r1:T,r2:T) = {eqvts  = Thm.merge_thms (#eqvts r1, #eqvts r2),
                             freshs = Thm.merge_thms (#freshs r1, #freshs r2),
                             bijs   = Thm.merge_thms (#bijs r1, #bijs r2)}
);

(* Exception for when a theorem does not conform with form of an equivariance lemma. *)
(* There are two forms: one is an implication (for relations) and the other is an    *)
(* equality (for functions). In the implication-case, say P ==> Q, Q must be equal   *)
(* to P except that every free variable of Q, say x, is replaced by pi o x. In the   *)
(* equality case, say lhs = rhs, the lhs must be of the form pi o t and the rhs must *)
(* be equal to t except that every free variable, say x, is replaced by pi o x. In   *)
(* the implicational case it is also checked that the variables and permutation fit  *)
(* together, i.e. are of the right "pt_class", so that a stronger version of the     *)
(* equality-lemma can be derived. *)
exception EQVT_FORM of string;

fun print_data ctxt =
  let
    val data = Data.get (Context.Proof ctxt);
    fun pretty_thms msg thms =
      Pretty.big_list msg (map (ProofContext.pretty_thm ctxt) thms);
  in
    Pretty.writeln (Pretty.chunks
     [pretty_thms "Equivariance lemmas:" (#eqvts data),
      pretty_thms "Freshness lemmas:" (#freshs data),
      pretty_thms "Bijection lemmas:" (#bijs data)])
  end;

val get_eqvt_thms = Context.Proof #> Data.get #> #eqvts;
val get_fresh_thms = Context.Proof #> Data.get #> #freshs;
val get_bij_thms = Context.Proof #> Data.get #> #bijs;

(* FIXME: should be a function in a library *)
fun mk_permT T = HOLogic.listT (HOLogic.mk_prodT (T, T));

val NOMINAL_EQVT_DEBUG = ref false;

fun tactic (msg,tac) =
    if !NOMINAL_EQVT_DEBUG
    then (EVERY [tac, print_tac ("after "^msg)])
    else tac

fun dynamic_thms thy name = PureThy.get_thms thy (Name name)

fun tactic_eqvt ctx orig_thm pi typi =
    let
        val mypi = Thm.cterm_of ctx (Var (pi,typi))
        val mypifree = Thm.cterm_of ctx (Const ("List.rev",typi --> typi) $ Free (fst pi,typi))
        val perm_pi_simp = dynamic_thms ctx "perm_pi_simp"
    in
        EVERY [tactic ("iffI applied",rtac iffI 1),
	       tactic ("remove pi with perm_boolE", (dtac @{thm perm_boolE} 1)),
               tactic ("solve with orig_thm", (etac orig_thm 1)),
               tactic ("applies orig_thm instantiated with rev pi",
                          dtac (Drule.cterm_instantiate [(mypi,mypifree)] orig_thm) 1),
	       tactic ("getting rid of the pi on the right",
                          (rtac @{thm perm_boolI} 1)),
               tactic ("getting rid of all remaining perms",
                          full_simp_tac (HOL_basic_ss addsimps perm_pi_simp) 1)]
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
    Context.mapping (snd o PureThy.add_thmss [(("eqvts",(#eqvts (Data.get context'))),[])]) I context'
  end;

(* replaces every variable x in t with pi o x *)
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
                if (Sign.of_sort thy (ty,[class_name]))
                then [(pi,typi)]
                else raise
                EQVT_FORM ("Could not find any permutation or an argument is not an instance of "^class_name)
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
    | _ => raise EQVT_FORM "All permutation should be the same")
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
             else raise EQVT_FORM "Type Implication"
          end
       (* case: eqvt-lemma is of the equational form *)
      | (Const ("Trueprop", _) $ (Const ("op =", _) $
            (Const ("Nominal.perm",typrm) $ Var (pi,typi) $ lhs) $ rhs)) =>
           (if (apply_pi lhs (pi,typi)) = rhs
               then [orig_thm]
               else raise EQVT_FORM "Type Equality")
      | _ => raise EQVT_FORM "Type unknown")
  in
      update_context flag thms_to_be_added context
  end
  handle EQVT_FORM s =>
      error (string_of_thm orig_thm ^ " does not comply with the form of an equivariance lemma ("^s^").")

(* in cases of bij- and freshness, we just add the lemmas to the *)
(* data-slot *)

fun simple_add_del_aux record_access name flag th context =
   let
     val context' = Data.map (flag th) context
   in
     Context.mapping (snd o PureThy.add_thmss [((name,(record_access (Data.get context'))),[])]) I context'
   end

fun bij_add_del_aux f   = simple_add_del_aux #bijs "bijs" f
fun fresh_add_del_aux f = simple_add_del_aux #freshs "freshs" f
fun eqvt_force_add_del_aux f = simple_add_del_aux #eqvts "eqvts" f

fun eqvt_map f th (r:Data.T)  = {eqvts = (f th (#eqvts r)), freshs = #freshs r, bijs = #bijs r};
fun fresh_map f th (r:Data.T) = {eqvts = #eqvts r, freshs = (f th (#freshs r)), bijs = #bijs r};
fun bij_map f th (r:Data.T)   = {eqvts = #eqvts r, freshs = #freshs r, bijs = (f th (#bijs r))};

val eqvt_add  = Thm.declaration_attribute (eqvt_add_del_aux (eqvt_map Thm.add_thm));
val eqvt_del  = Thm.declaration_attribute (eqvt_add_del_aux (eqvt_map Thm.del_thm));
val eqvt_force_add  = Thm.declaration_attribute (eqvt_force_add_del_aux (eqvt_map Thm.add_thm));
val eqvt_force_del  = Thm.declaration_attribute (eqvt_force_add_del_aux (eqvt_map Thm.del_thm));

val bij_add   = Thm.declaration_attribute (bij_add_del_aux (bij_map Thm.add_thm));
val bij_del   = Thm.declaration_attribute (bij_add_del_aux (bij_map Thm.del_thm));
val fresh_add = Thm.declaration_attribute (fresh_add_del_aux (fresh_map Thm.add_thm));
val fresh_del = Thm.declaration_attribute (fresh_add_del_aux (fresh_map Thm.del_thm));



val setup =
  Attrib.add_attributes
     [("eqvt",  Attrib.add_del_args eqvt_add eqvt_del,   "equivariance theorem declaration"),
      ("eqvt_force", Attrib.add_del_args eqvt_force_add eqvt_force_del,
        "equivariance theorem declaration (without checking the form of the lemma)"),
      ("fresh", Attrib.add_del_args fresh_add fresh_del, "freshness theorem declaration"),
      ("bij",   Attrib.add_del_args bij_add bij_del,     "bijection theorem declaration")];

end;
