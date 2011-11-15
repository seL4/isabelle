(*  Title:      HOL/Tools/cnf_funcs.ML
    Author:     Alwen Tiu, QSL Team, LORIA (http://qsl.loria.fr)
    Author:     Tjark Weber, TU Muenchen

FIXME: major overlaps with the code in meson.ML

Functions and tactics to transform a formula into Conjunctive Normal
Form (CNF).

A formula in CNF is of the following form:

    (x11 | x12 | ... | x1n) & ... & (xm1 | xm2 | ... | xmk)
    False
    True

where each xij is a literal (a positive or negative atomic Boolean
term), i.e. the formula is a conjunction of disjunctions of literals,
or "False", or "True".

A (non-empty) disjunction of literals is referred to as "clause".

For the purpose of SAT proof reconstruction, we also make use of
another representation of clauses, which we call the "raw clauses".
Raw clauses are of the form

    [..., x1', x2', ..., xn'] |- False ,

where each xi is a literal, and each xi' is the negation normal form
of ~xi.

Literals are successively removed from the hyps of raw clauses by
resolution during SAT proof reconstruction.
*)

signature CNF =
sig
  val is_atom: term -> bool
  val is_literal: term -> bool
  val is_clause: term -> bool
  val clause_is_trivial: term -> bool

  val clause2raw_thm: thm -> thm
  val make_nnf_thm: theory -> term -> thm

  val weakening_tac: int -> tactic  (* removes the first hypothesis of a subgoal *)

  val make_cnf_thm: Proof.context -> term -> thm
  val make_cnfx_thm: Proof.context -> term -> thm
  val cnf_rewrite_tac: Proof.context -> int -> tactic  (* converts all prems of a subgoal to CNF *)
  val cnfx_rewrite_tac: Proof.context -> int -> tactic
    (* converts all prems of a subgoal to (almost) definitional CNF *)
end;

structure cnf : CNF =
struct

val clause2raw_notE      = @{lemma "[| P; ~P |] ==> False" by auto};
val clause2raw_not_disj  = @{lemma "[| ~P; ~Q |] ==> ~(P | Q)" by auto};
val clause2raw_not_not   = @{lemma "P ==> ~~P" by auto};

val iff_refl             = @{lemma "(P::bool) = P" by auto};
val iff_trans            = @{lemma "[| (P::bool) = Q; Q = R |] ==> P = R" by auto};
val conj_cong            = @{lemma "[| P = P'; Q = Q' |] ==> (P & Q) = (P' & Q')" by auto};
val disj_cong            = @{lemma "[| P = P'; Q = Q' |] ==> (P | Q) = (P' | Q')" by auto};

val make_nnf_imp         = @{lemma "[| (~P) = P'; Q = Q' |] ==> (P --> Q) = (P' | Q')" by auto};
val make_nnf_iff         = @{lemma "[| P = P'; (~P) = NP; Q = Q'; (~Q) = NQ |] ==> (P = Q) = ((P' | NQ) & (NP | Q'))" by auto};
val make_nnf_not_false   = @{lemma "(~False) = True" by auto};
val make_nnf_not_true    = @{lemma "(~True) = False" by auto};
val make_nnf_not_conj    = @{lemma "[| (~P) = P'; (~Q) = Q' |] ==> (~(P & Q)) = (P' | Q')" by auto};
val make_nnf_not_disj    = @{lemma "[| (~P) = P'; (~Q) = Q' |] ==> (~(P | Q)) = (P' & Q')" by auto};
val make_nnf_not_imp     = @{lemma "[| P = P'; (~Q) = Q' |] ==> (~(P --> Q)) = (P' & Q')" by auto};
val make_nnf_not_iff     = @{lemma "[| P = P'; (~P) = NP; Q = Q'; (~Q) = NQ |] ==> (~(P = Q)) = ((P' | Q') & (NP | NQ))" by auto};
val make_nnf_not_not     = @{lemma "P = P' ==> (~~P) = P'" by auto};

val simp_TF_conj_True_l  = @{lemma "[| P = True; Q = Q' |] ==> (P & Q) = Q'" by auto};
val simp_TF_conj_True_r  = @{lemma "[| P = P'; Q = True |] ==> (P & Q) = P'" by auto};
val simp_TF_conj_False_l = @{lemma "P = False ==> (P & Q) = False" by auto};
val simp_TF_conj_False_r = @{lemma "Q = False ==> (P & Q) = False" by auto};
val simp_TF_disj_True_l  = @{lemma "P = True ==> (P | Q) = True" by auto};
val simp_TF_disj_True_r  = @{lemma "Q = True ==> (P | Q) = True" by auto};
val simp_TF_disj_False_l = @{lemma "[| P = False; Q = Q' |] ==> (P | Q) = Q'" by auto};
val simp_TF_disj_False_r = @{lemma "[| P = P'; Q = False |] ==> (P | Q) = P'" by auto};

val make_cnf_disj_conj_l = @{lemma "[| (P | R) = PR; (Q | R) = QR |] ==> ((P & Q) | R) = (PR & QR)" by auto};
val make_cnf_disj_conj_r = @{lemma "[| (P | Q) = PQ; (P | R) = PR |] ==> (P | (Q & R)) = (PQ & PR)" by auto};

val make_cnfx_disj_ex_l  = @{lemma "((EX (x::bool). P x) | Q) = (EX x. P x | Q)" by auto};
val make_cnfx_disj_ex_r  = @{lemma "(P | (EX (x::bool). Q x)) = (EX x. P | Q x)" by auto};
val make_cnfx_newlit     = @{lemma "(P | Q) = (EX x. (P | x) & (Q | ~x))" by auto};
val make_cnfx_ex_cong    = @{lemma "(ALL (x::bool). P x = Q x) ==> (EX x. P x) = (EX x. Q x)" by auto};

val weakening_thm        = @{lemma "[| P; Q |] ==> Q" by auto};

val cnftac_eq_imp        = @{lemma "[| P = Q; P |] ==> Q" by auto};

fun is_atom (Const (@{const_name False}, _)) = false
  | is_atom (Const (@{const_name True}, _)) = false
  | is_atom (Const (@{const_name HOL.conj}, _) $ _ $ _) = false
  | is_atom (Const (@{const_name HOL.disj}, _) $ _ $ _) = false
  | is_atom (Const (@{const_name HOL.implies}, _) $ _ $ _) = false
  | is_atom (Const (@{const_name HOL.eq}, Type ("fun", @{typ bool} :: _)) $ _ $ _) = false
  | is_atom (Const (@{const_name Not}, _) $ _) = false
  | is_atom _ = true;

fun is_literal (Const (@{const_name Not}, _) $ x) = is_atom x
  | is_literal x = is_atom x;

fun is_clause (Const (@{const_name HOL.disj}, _) $ x $ y) = is_clause x andalso is_clause y
  | is_clause x = is_literal x;

(* ------------------------------------------------------------------------- *)
(* clause_is_trivial: a clause is trivially true if it contains both an atom *)
(*      and the atom's negation                                              *)
(* ------------------------------------------------------------------------- *)

fun clause_is_trivial c =
  let
    fun dual (Const (@{const_name Not}, _) $ x) = x
      | dual x = HOLogic.Not $ x
    fun has_duals [] = false
      | has_duals (x::xs) = member (op =) xs (dual x) orelse has_duals xs
  in
    has_duals (HOLogic.disjuncts c)
  end;

(* ------------------------------------------------------------------------- *)
(* clause2raw_thm: translates a clause into a raw clause, i.e.               *)
(*        [...] |- x1 | ... | xn                                             *)
(*      (where each xi is a literal) is translated to                        *)
(*        [..., x1', ..., xn'] |- False ,                                    *)
(*      where each xi' is the negation normal form of ~xi                    *)
(* ------------------------------------------------------------------------- *)

fun clause2raw_thm clause =
  let
    (* eliminates negated disjunctions from the i-th premise, possibly *)
    (* adding new premises, then continues with the (i+1)-th premise   *)
    (* int -> Thm.thm -> Thm.thm *)
    fun not_disj_to_prem i thm =
      if i > nprems_of thm then
        thm
      else
        not_disj_to_prem (i+1) (Seq.hd (REPEAT_DETERM (rtac clause2raw_not_disj i) thm))
    (* moves all premises to hyps, i.e. "[...] |- A1 ==> ... ==> An ==> B" *)
    (* becomes "[..., A1, ..., An] |- B"                                   *)
    (* Thm.thm -> Thm.thm *)
    fun prems_to_hyps thm =
      fold (fn cprem => fn thm' =>
        Thm.implies_elim thm' (Thm.assume cprem)) (cprems_of thm) thm
  in
    (* [...] |- ~(x1 | ... | xn) ==> False *)
    (clause2raw_notE OF [clause])
    (* [...] |- ~x1 ==> ... ==> ~xn ==> False *)
    |> not_disj_to_prem 1
    (* [...] |- x1' ==> ... ==> xn' ==> False *)
    |> Seq.hd o TRYALL (rtac clause2raw_not_not)
    (* [..., x1', ..., xn'] |- False *)
    |> prems_to_hyps
  end;

(* ------------------------------------------------------------------------- *)
(* inst_thm: instantiates a theorem with a list of terms                     *)
(* ------------------------------------------------------------------------- *)

fun inst_thm thy ts thm =
  instantiate' [] (map (SOME o cterm_of thy) ts) thm;

(* ------------------------------------------------------------------------- *)
(*                         Naive CNF transformation                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* make_nnf_thm: produces a theorem of the form t = t', where t' is the      *)
(*      negation normal form (i.e. negation only occurs in front of atoms)   *)
(*      of t; implications ("-->") and equivalences ("=" on bool) are        *)
(*      eliminated (possibly causing an exponential blowup)                  *)
(* ------------------------------------------------------------------------- *)

fun make_nnf_thm thy (Const (@{const_name HOL.conj}, _) $ x $ y) =
      let
        val thm1 = make_nnf_thm thy x
        val thm2 = make_nnf_thm thy y
      in
        conj_cong OF [thm1, thm2]
      end
  | make_nnf_thm thy (Const (@{const_name HOL.disj}, _) $ x $ y) =
      let
        val thm1 = make_nnf_thm thy x
        val thm2 = make_nnf_thm thy y
      in
        disj_cong OF [thm1, thm2]
      end
  | make_nnf_thm thy (Const (@{const_name HOL.implies}, _) $ x $ y) =
      let
        val thm1 = make_nnf_thm thy (HOLogic.Not $ x)
        val thm2 = make_nnf_thm thy y
      in
        make_nnf_imp OF [thm1, thm2]
      end
  | make_nnf_thm thy (Const (@{const_name HOL.eq}, Type ("fun", @{typ bool} :: _)) $ x $ y) =
      let
        val thm1 = make_nnf_thm thy x
        val thm2 = make_nnf_thm thy (HOLogic.Not $ x)
        val thm3 = make_nnf_thm thy y
        val thm4 = make_nnf_thm thy (HOLogic.Not $ y)
      in
        make_nnf_iff OF [thm1, thm2, thm3, thm4]
      end
  | make_nnf_thm thy (Const (@{const_name Not}, _) $ Const (@{const_name False}, _)) =
      make_nnf_not_false
  | make_nnf_thm thy (Const (@{const_name Not}, _) $ Const (@{const_name True}, _)) =
      make_nnf_not_true
  | make_nnf_thm thy (Const (@{const_name Not}, _) $ (Const (@{const_name HOL.conj}, _) $ x $ y)) =
      let
        val thm1 = make_nnf_thm thy (HOLogic.Not $ x)
        val thm2 = make_nnf_thm thy (HOLogic.Not $ y)
      in
        make_nnf_not_conj OF [thm1, thm2]
      end
  | make_nnf_thm thy (Const (@{const_name Not}, _) $ (Const (@{const_name HOL.disj}, _) $ x $ y)) =
      let
        val thm1 = make_nnf_thm thy (HOLogic.Not $ x)
        val thm2 = make_nnf_thm thy (HOLogic.Not $ y)
      in
        make_nnf_not_disj OF [thm1, thm2]
      end
  | make_nnf_thm thy
      (Const (@{const_name Not}, _) $
        (Const (@{const_name HOL.implies}, _) $ x $ y)) =
      let
        val thm1 = make_nnf_thm thy x
        val thm2 = make_nnf_thm thy (HOLogic.Not $ y)
      in
        make_nnf_not_imp OF [thm1, thm2]
      end
  | make_nnf_thm thy
      (Const (@{const_name Not}, _) $
        (Const (@{const_name HOL.eq}, Type ("fun", @{typ bool} :: _)) $ x $ y)) =
      let
        val thm1 = make_nnf_thm thy x
        val thm2 = make_nnf_thm thy (HOLogic.Not $ x)
        val thm3 = make_nnf_thm thy y
        val thm4 = make_nnf_thm thy (HOLogic.Not $ y)
      in
        make_nnf_not_iff OF [thm1, thm2, thm3, thm4]
      end
  | make_nnf_thm thy (Const (@{const_name Not}, _) $ (Const (@{const_name Not}, _) $ x)) =
      let
        val thm1 = make_nnf_thm thy x
      in
        make_nnf_not_not OF [thm1]
      end
  | make_nnf_thm thy t = inst_thm thy [t] iff_refl;

val meta_eq_to_obj_eq = @{thm meta_eq_to_obj_eq}
val eq_reflection = @{thm eq_reflection}

fun make_under_quantifiers ctxt make t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun conv ctxt ct =
      case term_of ct of
        Const _ $ Abs _ => Conv.comb_conv (conv ctxt) ct
      | Abs _ => Conv.abs_conv (conv o snd) ctxt ct
      | Const _ => Conv.all_conv ct
      | t => make t RS eq_reflection
  in conv ctxt (cterm_of thy t) RS meta_eq_to_obj_eq end

fun make_nnf_thm_under_quantifiers ctxt =
  make_under_quantifiers ctxt (make_nnf_thm (Proof_Context.theory_of ctxt))

(* ------------------------------------------------------------------------- *)
(* simp_True_False_thm: produces a theorem t = t', where t' is equivalent to *)
(*      t, but simplified wrt. the following theorems:                       *)
(*        (True & x) = x                                                     *)
(*        (x & True) = x                                                     *)
(*        (False & x) = False                                                *)
(*        (x & False) = False                                                *)
(*        (True | x) = True                                                  *)
(*        (x | True) = True                                                  *)
(*        (False | x) = x                                                    *)
(*        (x | False) = x                                                    *)
(*      No simplification is performed below connectives other than & and |. *)
(*      Optimization: The right-hand side of a conjunction (disjunction) is  *)
(*      simplified only if the left-hand side does not simplify to False     *)
(*      (True, respectively).                                                *)
(* ------------------------------------------------------------------------- *)

(* Theory.theory -> Term.term -> Thm.thm *)

fun simp_True_False_thm thy (Const (@{const_name HOL.conj}, _) $ x $ y) =
      let
        val thm1 = simp_True_False_thm thy x
        val x'= (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm1
      in
        if x' = HOLogic.false_const then
          simp_TF_conj_False_l OF [thm1]  (* (x & y) = False *)
        else
          let
            val thm2 = simp_True_False_thm thy y
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm2
          in
            if x' = HOLogic.true_const then
              simp_TF_conj_True_l OF [thm1, thm2]  (* (x & y) = y' *)
            else if y' = HOLogic.false_const then
              simp_TF_conj_False_r OF [thm2]  (* (x & y) = False *)
            else if y' = HOLogic.true_const then
              simp_TF_conj_True_r OF [thm1, thm2]  (* (x & y) = x' *)
            else
              conj_cong OF [thm1, thm2]  (* (x & y) = (x' & y') *)
          end
      end
  | simp_True_False_thm thy (Const (@{const_name HOL.disj}, _) $ x $ y) =
      let
        val thm1 = simp_True_False_thm thy x
        val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm1
      in
        if x' = HOLogic.true_const then
          simp_TF_disj_True_l OF [thm1]  (* (x | y) = True *)
        else
          let
            val thm2 = simp_True_False_thm thy y
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm2
          in
            if x' = HOLogic.false_const then
              simp_TF_disj_False_l OF [thm1, thm2]  (* (x | y) = y' *)
            else if y' = HOLogic.true_const then
              simp_TF_disj_True_r OF [thm2]  (* (x | y) = True *)
            else if y' = HOLogic.false_const then
              simp_TF_disj_False_r OF [thm1, thm2]  (* (x | y) = x' *)
            else
              disj_cong OF [thm1, thm2]  (* (x | y) = (x' | y') *)
          end
      end
  | simp_True_False_thm thy t = inst_thm thy [t] iff_refl;  (* t = t *)

(* ------------------------------------------------------------------------- *)
(* make_cnf_thm: given any HOL term 't', produces a theorem t = t', where t' *)
(*      is in conjunction normal form.  May cause an exponential blowup      *)
(*      in the length of the term.                                           *)
(* ------------------------------------------------------------------------- *)

fun make_cnf_thm ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun make_cnf_thm_from_nnf (Const (@{const_name HOL.conj}, _) $ x $ y) =
          let
            val thm1 = make_cnf_thm_from_nnf x
            val thm2 = make_cnf_thm_from_nnf y
          in
            conj_cong OF [thm1, thm2]
          end
      | make_cnf_thm_from_nnf (Const (@{const_name HOL.disj}, _) $ x $ y) =
          let
            (* produces a theorem "(x' | y') = t'", where x', y', and t' are in CNF *)
            fun make_cnf_disj_thm (Const (@{const_name HOL.conj}, _) $ x1 $ x2) y' =
                  let
                    val thm1 = make_cnf_disj_thm x1 y'
                    val thm2 = make_cnf_disj_thm x2 y'
                  in
                    make_cnf_disj_conj_l OF [thm1, thm2]  (* ((x1 & x2) | y') = ((x1 | y')' & (x2 | y')') *)
                  end
              | make_cnf_disj_thm x' (Const (@{const_name HOL.conj}, _) $ y1 $ y2) =
                  let
                    val thm1 = make_cnf_disj_thm x' y1
                    val thm2 = make_cnf_disj_thm x' y2
                  in
                    make_cnf_disj_conj_r OF [thm1, thm2]  (* (x' | (y1 & y2)) = ((x' | y1)' & (x' | y2)') *)
                  end
              | make_cnf_disj_thm x' y' =
                  inst_thm thy [HOLogic.mk_disj (x', y')] iff_refl  (* (x' | y') = (x' | y') *)
            val thm1 = make_cnf_thm_from_nnf x
            val thm2 = make_cnf_thm_from_nnf y
            val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm1
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm2
            val disj_thm = disj_cong OF [thm1, thm2]  (* (x | y) = (x' | y') *)
          in
            iff_trans OF [disj_thm, make_cnf_disj_thm x' y']
          end
      | make_cnf_thm_from_nnf t = inst_thm thy [t] iff_refl
    (* convert 't' to NNF first *)
    val nnf_thm = make_nnf_thm_under_quantifiers ctxt t
(*###
    val nnf_thm = make_nnf_thm thy t
*)
    val nnf = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) nnf_thm
    (* then simplify wrt. True/False (this should preserve NNF) *)
    val simp_thm = simp_True_False_thm thy nnf
    val simp = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) simp_thm
    (* finally, convert to CNF (this should preserve the simplification) *)
    val cnf_thm = make_under_quantifiers ctxt make_cnf_thm_from_nnf simp
(* ###
    val cnf_thm = make_cnf_thm_from_nnf simp
*)
  in
    iff_trans OF [iff_trans OF [nnf_thm, simp_thm], cnf_thm]
  end;

(* ------------------------------------------------------------------------- *)
(*            CNF transformation by introducing new literals                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* make_cnfx_thm: given any HOL term 't', produces a theorem t = t', where   *)
(*      t' is almost in conjunction normal form, except that conjunctions    *)
(*      and existential quantifiers may be nested.  (Use e.g. 'REPEAT_DETERM *)
(*      (etac exE i ORELSE etac conjE i)' afterwards to normalize.)  May     *)
(*      introduce new (existentially bound) literals.  Note: the current     *)
(*      implementation calls 'make_nnf_thm', causing an exponential blowup   *)
(*      in the case of nested equivalences.                                  *)
(* ------------------------------------------------------------------------- *)

fun make_cnfx_thm ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val var_id = Unsynchronized.ref 0  (* properly initialized below *)
    fun new_free () =
      Free ("cnfx_" ^ string_of_int (Unsynchronized.inc var_id), HOLogic.boolT)
    fun make_cnfx_thm_from_nnf (Const (@{const_name HOL.conj}, _) $ x $ y) : thm =
          let
            val thm1 = make_cnfx_thm_from_nnf x
            val thm2 = make_cnfx_thm_from_nnf y
          in
            conj_cong OF [thm1, thm2]
          end
      | make_cnfx_thm_from_nnf (Const (@{const_name HOL.disj}, _) $ x $ y) =
          if is_clause x andalso is_clause y then
            inst_thm thy [HOLogic.mk_disj (x, y)] iff_refl
          else if is_literal y orelse is_literal x then
            let
              (* produces a theorem "(x' | y') = t'", where x', y', and t' are *)
              (* almost in CNF, and x' or y' is a literal                      *)
              fun make_cnfx_disj_thm (Const (@{const_name HOL.conj}, _) $ x1 $ x2) y' =
                    let
                      val thm1 = make_cnfx_disj_thm x1 y'
                      val thm2 = make_cnfx_disj_thm x2 y'
                    in
                      make_cnf_disj_conj_l OF [thm1, thm2]  (* ((x1 & x2) | y') = ((x1 | y')' & (x2 | y')') *)
                    end
                | make_cnfx_disj_thm x' (Const (@{const_name HOL.conj}, _) $ y1 $ y2) =
                    let
                      val thm1 = make_cnfx_disj_thm x' y1
                      val thm2 = make_cnfx_disj_thm x' y2
                    in
                      make_cnf_disj_conj_r OF [thm1, thm2]  (* (x' | (y1 & y2)) = ((x' | y1)' & (x' | y2)') *)
                    end
                | make_cnfx_disj_thm (@{term "Ex::(bool => bool) => bool"} $ x') y' =
                    let
                      val thm1 = inst_thm thy [x', y'] make_cnfx_disj_ex_l   (* ((Ex x') | y') = (Ex (x' | y')) *)
                      val var = new_free ()
                      val thm2 = make_cnfx_disj_thm (betapply (x', var)) y'  (* (x' | y') = body' *)
                      val thm3 = Thm.forall_intr (cterm_of thy var) thm2     (* !!v. (x' | y') = body' *)
                      val thm4 = Thm.strip_shyps (thm3 COMP allI)            (* ALL v. (x' | y') = body' *)
                      val thm5 = Thm.strip_shyps (thm4 RS make_cnfx_ex_cong) (* (EX v. (x' | y')) = (EX v. body') *)
                    in
                      iff_trans OF [thm1, thm5]  (* ((Ex x') | y') = (Ex v. body') *)
                    end
                | make_cnfx_disj_thm x' (@{term "Ex::(bool => bool) => bool"} $ y') =
                    let
                      val thm1 = inst_thm thy [x', y'] make_cnfx_disj_ex_r   (* (x' | (Ex y')) = (Ex (x' | y')) *)
                      val var = new_free ()
                      val thm2 = make_cnfx_disj_thm x' (betapply (y', var))  (* (x' | y') = body' *)
                      val thm3 = Thm.forall_intr (cterm_of thy var) thm2     (* !!v. (x' | y') = body' *)
                      val thm4 = Thm.strip_shyps (thm3 COMP allI)            (* ALL v. (x' | y') = body' *)
                      val thm5 = Thm.strip_shyps (thm4 RS make_cnfx_ex_cong) (* (EX v. (x' | y')) = (EX v. body') *)
                    in
                      iff_trans OF [thm1, thm5]  (* (x' | (Ex y')) = (EX v. body') *)
                    end
                | make_cnfx_disj_thm x' y' =
                    inst_thm thy [HOLogic.mk_disj (x', y')] iff_refl  (* (x' | y') = (x' | y') *)
              val thm1 = make_cnfx_thm_from_nnf x
              val thm2 = make_cnfx_thm_from_nnf y
              val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm1
              val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) thm2
              val disj_thm = disj_cong OF [thm1, thm2]  (* (x | y) = (x' | y') *)
            in
              iff_trans OF [disj_thm, make_cnfx_disj_thm x' y']
            end
          else
            let  (* neither 'x' nor 'y' is a literal: introduce a fresh variable *)
              val thm1 = inst_thm thy [x, y] make_cnfx_newlit     (* (x | y) = EX v. (x | v) & (y | ~v) *)
              val var = new_free ()
              val body = HOLogic.mk_conj (HOLogic.mk_disj (x, var), HOLogic.mk_disj (y, HOLogic.Not $ var))
              val thm2 = make_cnfx_thm_from_nnf body              (* (x | v) & (y | ~v) = body' *)
              val thm3 = Thm.forall_intr (cterm_of thy var) thm2  (* !!v. (x | v) & (y | ~v) = body' *)
              val thm4 = Thm.strip_shyps (thm3 COMP allI)         (* ALL v. (x | v) & (y | ~v) = body' *)
              val thm5 = Thm.strip_shyps (thm4 RS make_cnfx_ex_cong)  (* (EX v. (x | v) & (y | ~v)) = (EX v. body') *)
            in
              iff_trans OF [thm1, thm5]
            end
      | make_cnfx_thm_from_nnf t = inst_thm thy [t] iff_refl
    (* convert 't' to NNF first *)
    val nnf_thm = make_nnf_thm_under_quantifiers ctxt t
(* ###
    val nnf_thm = make_nnf_thm thy t
*)
    val nnf = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) nnf_thm
    (* then simplify wrt. True/False (this should preserve NNF) *)
    val simp_thm = simp_True_False_thm thy nnf
    val simp = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) simp_thm
    (* initialize var_id, in case the term already contains variables of the form "cnfx_<int>" *)
    val _ = (var_id := fold (fn free => fn max =>
      let
        val (name, _) = dest_Free free
        val idx =
          if String.isPrefix "cnfx_" name then
            (Int.fromString o String.extract) (name, String.size "cnfx_", NONE)
          else
            NONE
      in
        Int.max (max, the_default 0 idx)
      end) (Misc_Legacy.term_frees simp) 0)
    (* finally, convert to definitional CNF (this should preserve the simplification) *)
    val cnfx_thm = make_under_quantifiers ctxt make_cnfx_thm_from_nnf simp
(*###
    val cnfx_thm = make_cnfx_thm_from_nnf simp
*)
  in
    iff_trans OF [iff_trans OF [nnf_thm, simp_thm], cnfx_thm]
  end;

(* ------------------------------------------------------------------------- *)
(*                                  Tactics                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* weakening_tac: removes the first hypothesis of the 'i'-th subgoal         *)
(* ------------------------------------------------------------------------- *)

fun weakening_tac i =
  dtac weakening_thm i THEN atac (i+1);

(* ------------------------------------------------------------------------- *)
(* cnf_rewrite_tac: converts all premises of the 'i'-th subgoal to CNF       *)
(*      (possibly causing an exponential blowup in the length of each        *)
(*      premise)                                                             *)
(* ------------------------------------------------------------------------- *)

fun cnf_rewrite_tac ctxt i =
  (* cut the CNF formulas as new premises *)
  Subgoal.FOCUS (fn {prems, ...} =>
    let
      val cnf_thms = map (make_cnf_thm ctxt o HOLogic.dest_Trueprop o Thm.prop_of) prems
      val cut_thms = map (fn (th, pr) => cnftac_eq_imp OF [th, pr]) (cnf_thms ~~ prems)
    in
      cut_facts_tac cut_thms 1
    end) ctxt i
  (* remove the original premises *)
  THEN SELECT_GOAL (fn thm =>
    let
      val n = Logic.count_prems ((Term.strip_all_body o fst o Logic.dest_implies o prop_of) thm)
    in
      PRIMITIVE (funpow (n div 2) (Seq.hd o weakening_tac 1)) thm
    end) i;

(* ------------------------------------------------------------------------- *)
(* cnfx_rewrite_tac: converts all premises of the 'i'-th subgoal to CNF      *)
(*      (possibly introducing new literals)                                  *)
(* ------------------------------------------------------------------------- *)

fun cnfx_rewrite_tac ctxt i =
  (* cut the CNF formulas as new premises *)
  Subgoal.FOCUS (fn {prems, ...} =>
    let
      val cnfx_thms = map (make_cnfx_thm ctxt o HOLogic.dest_Trueprop o prop_of) prems
      val cut_thms = map (fn (th, pr) => cnftac_eq_imp OF [th, pr]) (cnfx_thms ~~ prems)
    in
      cut_facts_tac cut_thms 1
    end) ctxt i
  (* remove the original premises *)
  THEN SELECT_GOAL (fn thm =>
    let
      val n = Logic.count_prems ((Term.strip_all_body o fst o Logic.dest_implies o prop_of) thm)
    in
      PRIMITIVE (funpow (n div 2) (Seq.hd o weakening_tac 1)) thm
    end) i;

end;
