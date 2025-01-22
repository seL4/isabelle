(*  Title:      HOL/Tools/cnf.ML
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

  val clause2raw_thm: Proof.context -> thm -> thm
  val make_nnf_thm: Proof.context -> term -> thm

  val weakening_tac: Proof.context -> int -> tactic  (* removes the first hypothesis of a subgoal *)

  val make_cnf_thm: Proof.context -> term -> thm
  val make_cnfx_thm: Proof.context -> term -> thm
  val cnf_rewrite_tac: Proof.context -> int -> tactic  (* converts all prems of a subgoal to CNF *)
  val cnfx_rewrite_tac: Proof.context -> int -> tactic
    (* converts all prems of a subgoal to (almost) definitional CNF *)
end;

structure CNF : CNF =
struct

fun is_atom \<^Const_>\<open>False\<close> = false
  | is_atom \<^Const_>\<open>True\<close> = false
  | is_atom \<^Const_>\<open>conj for _ _\<close> = false
  | is_atom \<^Const_>\<open>disj for _ _\<close> = false
  | is_atom \<^Const_>\<open>implies for _ _\<close> = false
  | is_atom \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for _ _\<close> = false
  | is_atom \<^Const_>\<open>Not for _\<close> = false
  | is_atom _ = true;

fun is_literal \<^Const_>\<open>Not for x\<close> = is_atom x
  | is_literal x = is_atom x;

fun is_clause \<^Const_>\<open>disj for x y\<close> = is_clause x andalso is_clause y
  | is_clause x = is_literal x;

(* ------------------------------------------------------------------------- *)
(* clause_is_trivial: a clause is trivially true if it contains both an atom *)
(*      and the atom's negation                                              *)
(* ------------------------------------------------------------------------- *)

fun clause_is_trivial c =
  let
    fun dual \<^Const_>\<open>Not for x\<close> = x
      | dual x = \<^Const>\<open>Not for x\<close>
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

fun clause2raw_thm ctxt clause =
  let
    (* eliminates negated disjunctions from the i-th premise, possibly *)
    (* adding new premises, then continues with the (i+1)-th premise   *)
    fun not_disj_to_prem i thm =
      if i > Thm.nprems_of thm then
        thm
      else
        not_disj_to_prem (i+1)
          (Seq.hd (REPEAT_DETERM (resolve_tac ctxt @{thms cnf.clause2raw_not_disj} i) thm))
    (* moves all premises to hyps, i.e. "[...] |- A1 ==> ... ==> An ==> B" *)
    (* becomes "[..., A1, ..., An] |- B"                                   *)
    fun prems_to_hyps thm =
      fold (fn cprem => fn thm' =>
        Thm.implies_elim thm' (Thm.assume cprem)) (Thm.cprems_of thm) thm
  in
    (* [...] |- ~(x1 | ... | xn) ==> False *)
    (@{thm cnf.clause2raw_notE} OF [clause])
    (* [...] |- ~x1 ==> ... ==> ~xn ==> False *)
    |> not_disj_to_prem 1
    (* [...] |- x1' ==> ... ==> xn' ==> False *)
    |> Seq.hd o TRYALL (resolve_tac ctxt @{thms cnf.clause2raw_not_not})
    (* [..., x1', ..., xn'] |- False *)
    |> prems_to_hyps
  end;

(* ------------------------------------------------------------------------- *)
(* inst_thm: instantiates a theorem with a list of terms                     *)
(* ------------------------------------------------------------------------- *)

fun inst_thm ctxt ts thm =
  Thm.instantiate' [] (map (SOME o Thm.cterm_of ctxt) ts) thm;

(* ------------------------------------------------------------------------- *)
(*                         Naive CNF transformation                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* make_nnf_thm: produces a theorem of the form t = t', where t' is the      *)
(*      negation normal form (i.e. negation only occurs in front of atoms)   *)
(*      of t; implications ("-->") and equivalences ("=" on bool) are        *)
(*      eliminated (possibly causing an exponential blowup)                  *)
(* ------------------------------------------------------------------------- *)

fun make_nnf_thm ctxt \<^Const_>\<open>conj for x y\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
        val thm2 = make_nnf_thm ctxt y
      in
        @{thm cnf.conj_cong} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>disj for x y\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
        val thm2 = make_nnf_thm ctxt y
      in
        @{thm cnf.disj_cong} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>implies for x y\<close> =
      let
        val thm1 = make_nnf_thm ctxt \<^Const>\<open>Not for x\<close>
        val thm2 = make_nnf_thm ctxt y
      in
        @{thm cnf.make_nnf_imp} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for x y\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
        val thm2 = make_nnf_thm ctxt \<^Const>\<open>Not for x\<close>
        val thm3 = make_nnf_thm ctxt y
        val thm4 = make_nnf_thm ctxt \<^Const>\<open>Not for y\<close>
      in
        @{thm cnf.make_nnf_iff} OF [thm1, thm2, thm3, thm4]
      end
  | make_nnf_thm _ \<^Const_>\<open>Not for \<^Const_>\<open>False\<close>\<close> =
      @{thm cnf.make_nnf_not_false}
  | make_nnf_thm _ \<^Const_>\<open>Not for \<^Const_>\<open>True\<close>\<close> =
      @{thm cnf.make_nnf_not_true}
  | make_nnf_thm ctxt \<^Const_>\<open>Not for \<^Const_>\<open>conj for x y\<close>\<close> =
      let
        val thm1 = make_nnf_thm ctxt \<^Const>\<open>Not for x\<close>
        val thm2 = make_nnf_thm ctxt \<^Const>\<open>Not for y\<close>
      in
        @{thm cnf.make_nnf_not_conj} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>Not for \<^Const_>\<open>disj for x y\<close>\<close> =
      let
        val thm1 = make_nnf_thm ctxt \<^Const>\<open>Not for x\<close>
        val thm2 = make_nnf_thm ctxt \<^Const>\<open>Not for y\<close>
      in
        @{thm cnf.make_nnf_not_disj} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>Not for \<^Const_>\<open>implies for x y\<close>\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
        val thm2 = make_nnf_thm ctxt \<^Const>\<open>Not for y\<close>
      in
        @{thm cnf.make_nnf_not_imp} OF [thm1, thm2]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>Not for \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for x y\<close>\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
        val thm2 = make_nnf_thm ctxt \<^Const>\<open>Not for x\<close>
        val thm3 = make_nnf_thm ctxt y
        val thm4 = make_nnf_thm ctxt \<^Const>\<open>Not for y\<close>
      in
        @{thm cnf.make_nnf_not_iff} OF [thm1, thm2, thm3, thm4]
      end
  | make_nnf_thm ctxt \<^Const_>\<open>Not for \<^Const_>\<open>Not for x\<close>\<close> =
      let
        val thm1 = make_nnf_thm ctxt x
      in
        @{thm cnf.make_nnf_not_not} OF [thm1]
      end
  | make_nnf_thm ctxt t = inst_thm ctxt [t] @{thm cnf.iff_refl};

fun make_under_quantifiers ctxt make t =
  let
    fun conv ctxt ct =
      (case Thm.term_of ct of
        Const _ $ Abs _ => Conv.comb_conv (conv ctxt) ct
      | Abs _ => Conv.abs_conv (conv o snd) ctxt ct
      | Const _ => Conv.all_conv ct
      | t => make t RS @{thm eq_reflection})
  in HOLogic.mk_obj_eq (conv ctxt (Thm.cterm_of ctxt t)) end

fun make_nnf_thm_under_quantifiers ctxt =
  make_under_quantifiers ctxt (make_nnf_thm ctxt)

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

fun simp_True_False_thm ctxt \<^Const_>\<open>conj for x y\<close> =
      let
        val thm1 = simp_True_False_thm ctxt x
        val x'= (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm1
      in
        if x' = \<^Const>\<open>False\<close> then
          @{thm cnf.simp_TF_conj_False_l} OF [thm1]  (* (x & y) = False *)
        else
          let
            val thm2 = simp_True_False_thm ctxt y
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm2
          in
            if x' = \<^Const>\<open>True\<close> then
              @{thm cnf.simp_TF_conj_True_l} OF [thm1, thm2]  (* (x & y) = y' *)
            else if y' = \<^Const>\<open>False\<close> then
              @{thm cnf.simp_TF_conj_False_r} OF [thm2]  (* (x & y) = False *)
            else if y' = \<^Const>\<open>True\<close> then
              @{thm cnf.simp_TF_conj_True_r} OF [thm1, thm2]  (* (x & y) = x' *)
            else
              @{thm cnf.conj_cong} OF [thm1, thm2]  (* (x & y) = (x' & y') *)
          end
      end
  | simp_True_False_thm ctxt \<^Const_>\<open>disj for x y\<close> =
      let
        val thm1 = simp_True_False_thm ctxt x
        val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm1
      in
        if x' = \<^Const>\<open>True\<close> then
          @{thm cnf.simp_TF_disj_True_l} OF [thm1]  (* (x | y) = True *)
        else
          let
            val thm2 = simp_True_False_thm ctxt y
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm2
          in
            if x' = \<^Const>\<open>False\<close> then
              @{thm cnf.simp_TF_disj_False_l} OF [thm1, thm2]  (* (x | y) = y' *)
            else if y' = \<^Const>\<open>True\<close> then
              @{thm cnf.simp_TF_disj_True_r} OF [thm2]  (* (x | y) = True *)
            else if y' = \<^Const>\<open>False\<close> then
              @{thm cnf.simp_TF_disj_False_r} OF [thm1, thm2]  (* (x | y) = x' *)
            else
              @{thm cnf.disj_cong} OF [thm1, thm2]  (* (x | y) = (x' | y') *)
          end
      end
  | simp_True_False_thm ctxt t = inst_thm ctxt [t] @{thm cnf.iff_refl};  (* t = t *)

(* ------------------------------------------------------------------------- *)
(* make_cnf_thm: given any HOL term 't', produces a theorem t = t', where t' *)
(*      is in conjunction normal form.  May cause an exponential blowup      *)
(*      in the length of the term.                                           *)
(* ------------------------------------------------------------------------- *)

fun make_cnf_thm ctxt t =
  let
    fun make_cnf_thm_from_nnf \<^Const_>\<open>conj for x y\<close> =
          let
            val thm1 = make_cnf_thm_from_nnf x
            val thm2 = make_cnf_thm_from_nnf y
          in
            @{thm cnf.conj_cong} OF [thm1, thm2]
          end
      | make_cnf_thm_from_nnf \<^Const_>\<open>disj for x y\<close> =
          let
            (* produces a theorem "(x' | y') = t'", where x', y', and t' are in CNF *)
            fun make_cnf_disj_thm \<^Const_>\<open>conj for x1 x2\<close> y' =
                  let
                    val thm1 = make_cnf_disj_thm x1 y'
                    val thm2 = make_cnf_disj_thm x2 y'
                  in
                    @{thm cnf.make_cnf_disj_conj_l} OF [thm1, thm2]  (* ((x1 & x2) | y') = ((x1 | y')' & (x2 | y')') *)
                  end
              | make_cnf_disj_thm x' \<^Const_>\<open>conj for y1 y2\<close> =
                  let
                    val thm1 = make_cnf_disj_thm x' y1
                    val thm2 = make_cnf_disj_thm x' y2
                  in
                    @{thm cnf.make_cnf_disj_conj_r} OF [thm1, thm2]  (* (x' | (y1 & y2)) = ((x' | y1)' & (x' | y2)') *)
                  end
              | make_cnf_disj_thm x' y' =
                  inst_thm ctxt [\<^Const>\<open>disj for x' y'\<close>] @{thm cnf.iff_refl}  (* (x' | y') = (x' | y') *)
            val thm1 = make_cnf_thm_from_nnf x
            val thm2 = make_cnf_thm_from_nnf y
            val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm1
            val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm2
            val disj_thm = @{thm cnf.disj_cong} OF [thm1, thm2]  (* (x | y) = (x' | y') *)
          in
            @{thm cnf.iff_trans} OF [disj_thm, make_cnf_disj_thm x' y']
          end
      | make_cnf_thm_from_nnf t = inst_thm ctxt [t] @{thm cnf.iff_refl}
    (* convert 't' to NNF first *)
    val nnf_thm = make_nnf_thm_under_quantifiers ctxt t
(*###
    val nnf_thm = make_nnf_thm ctxt t
*)
    val nnf = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) nnf_thm
    (* then simplify wrt. True/False (this should preserve NNF) *)
    val simp_thm = simp_True_False_thm ctxt nnf
    val simp = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) simp_thm
    (* finally, convert to CNF (this should preserve the simplification) *)
    val cnf_thm = make_under_quantifiers ctxt make_cnf_thm_from_nnf simp
(* ###
    val cnf_thm = make_cnf_thm_from_nnf simp
*)
  in
    @{thm cnf.iff_trans} OF [@{thm cnf.iff_trans} OF [nnf_thm, simp_thm], cnf_thm]
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
    val var_id = Unsynchronized.ref 0  (* properly initialized below *)
    fun new_free () =
      Free ("cnfx_" ^ string_of_int (Unsynchronized.inc var_id), \<^Type>\<open>bool\<close>)
    fun make_cnfx_thm_from_nnf \<^Const_>\<open>conj for x y\<close> =
          let
            val thm1 = make_cnfx_thm_from_nnf x
            val thm2 = make_cnfx_thm_from_nnf y
          in
            @{thm cnf.conj_cong} OF [thm1, thm2]
          end
      | make_cnfx_thm_from_nnf \<^Const_>\<open>disj for x y\<close> =
          if is_clause x andalso is_clause y then
            inst_thm ctxt [\<^Const>\<open>disj for x y\<close>] @{thm cnf.iff_refl}
          else if is_literal y orelse is_literal x then
            let
              (* produces a theorem "(x' | y') = t'", where x', y', and t' are *)
              (* almost in CNF, and x' or y' is a literal                      *)
              fun make_cnfx_disj_thm \<^Const_>\<open>conj for x1 x2\<close> y' =
                    let
                      val thm1 = make_cnfx_disj_thm x1 y'
                      val thm2 = make_cnfx_disj_thm x2 y'
                    in
                      @{thm cnf.make_cnf_disj_conj_l} OF [thm1, thm2]  (* ((x1 & x2) | y') = ((x1 | y')' & (x2 | y')') *)
                    end
                | make_cnfx_disj_thm x' \<^Const_>\<open>conj for y1 y2\<close> =
                    let
                      val thm1 = make_cnfx_disj_thm x' y1
                      val thm2 = make_cnfx_disj_thm x' y2
                    in
                      @{thm cnf.make_cnf_disj_conj_r} OF [thm1, thm2]  (* (x' | (y1 & y2)) = ((x' | y1)' & (x' | y2)') *)
                    end
                | make_cnfx_disj_thm \<^Const_>\<open>Ex \<^Type>\<open>bool\<close> for x'\<close> y' =
                    let
                      val thm1 = inst_thm ctxt [x', y'] @{thm cnf.make_cnfx_disj_ex_l}   (* ((Ex x') | y') = (Ex (x' | y')) *)
                      val var = new_free ()
                      val thm2 = make_cnfx_disj_thm (betapply (x', var)) y'  (* (x' | y') = body' *)
                      val thm3 = Thm.forall_intr (Thm.cterm_of ctxt var) thm2 (* !!v. (x' | y') = body' *)
                      val thm4 = Thm.strip_shyps (thm3 COMP allI)            (* ALL v. (x' | y') = body' *)
                      val thm5 = Thm.strip_shyps (thm4 RS @{thm cnf.make_cnfx_ex_cong}) (* (EX v. (x' | y')) = (EX v. body') *)
                    in
                      @{thm cnf.iff_trans} OF [thm1, thm5]  (* ((Ex x') | y') = (Ex v. body') *)
                    end
                | make_cnfx_disj_thm x' \<^Const_>\<open>Ex \<^Type>\<open>bool\<close> for y'\<close> =
                    let
                      val thm1 = inst_thm ctxt [x', y'] @{thm cnf.make_cnfx_disj_ex_r}   (* (x' | (Ex y')) = (Ex (x' | y')) *)
                      val var = new_free ()
                      val thm2 = make_cnfx_disj_thm x' (betapply (y', var))  (* (x' | y') = body' *)
                      val thm3 = Thm.forall_intr (Thm.cterm_of ctxt var) thm2 (* !!v. (x' | y') = body' *)
                      val thm4 = Thm.strip_shyps (thm3 COMP allI)            (* ALL v. (x' | y') = body' *)
                      val thm5 = Thm.strip_shyps (thm4 RS @{thm cnf.make_cnfx_ex_cong}) (* (EX v. (x' | y')) = (EX v. body') *)
                    in
                      @{thm cnf.iff_trans} OF [thm1, thm5]  (* (x' | (Ex y')) = (EX v. body') *)
                    end
                | make_cnfx_disj_thm x' y' =
                    inst_thm ctxt [\<^Const>\<open>disj for x' y'\<close>] @{thm cnf.iff_refl}  (* (x' | y') = (x' | y') *)
              val thm1 = make_cnfx_thm_from_nnf x
              val thm2 = make_cnfx_thm_from_nnf y
              val x' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm1
              val y' = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm2
              val disj_thm = @{thm cnf.disj_cong} OF [thm1, thm2]  (* (x | y) = (x' | y') *)
            in
              @{thm cnf.iff_trans} OF [disj_thm, make_cnfx_disj_thm x' y']
            end
          else
            let  (* neither 'x' nor 'y' is a literal: introduce a fresh variable *)
              val thm1 = inst_thm ctxt [x, y] @{thm cnf.make_cnfx_newlit}     (* (x | y) = EX v. (x | v) & (y | ~v) *)
              val var = new_free ()
              val body = \<^Const>\<open>conj for \<^Const>\<open>disj for x var\<close> \<^Const>\<open>disj for y \<^Const>\<open>Not for var\<close>\<close>\<close>
              val thm2 = make_cnfx_thm_from_nnf body              (* (x | v) & (y | ~v) = body' *)
              val thm3 = Thm.forall_intr (Thm.cterm_of ctxt var) thm2 (* !!v. (x | v) & (y | ~v) = body' *)
              val thm4 = Thm.strip_shyps (thm3 COMP allI)         (* ALL v. (x | v) & (y | ~v) = body' *)
              val thm5 = Thm.strip_shyps (thm4 RS @{thm cnf.make_cnfx_ex_cong})  (* (EX v. (x | v) & (y | ~v)) = (EX v. body') *)
            in
              @{thm cnf.iff_trans} OF [thm1, thm5]
            end
      | make_cnfx_thm_from_nnf t = inst_thm ctxt [t] @{thm cnf.iff_refl}
    (* convert 't' to NNF first *)
    val nnf_thm = make_nnf_thm_under_quantifiers ctxt t
(* ###
    val nnf_thm = make_nnf_thm ctxt t
*)
    val nnf = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) nnf_thm
    (* then simplify wrt. True/False (this should preserve NNF) *)
    val simp_thm = simp_True_False_thm ctxt nnf
    val simp = (snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) simp_thm
    (* initialize var_id, in case the term already contains variables of the form "cnfx_<int>" *)
    val _ = (var_id := Frees.fold (fn ((name, _), _) => fn max =>
      let
        val idx =
          (case try (unprefix "cnfx_") name of
            SOME s => Int.fromString s
          | NONE => NONE)
      in
        Int.max (max, the_default 0 idx)
      end) (Frees.build (Frees.add_frees simp)) 0)
    (* finally, convert to definitional CNF (this should preserve the simplification) *)
    val cnfx_thm = make_under_quantifiers ctxt make_cnfx_thm_from_nnf simp
(*###
    val cnfx_thm = make_cnfx_thm_from_nnf simp
*)
  in
    @{thm cnf.iff_trans} OF [@{thm cnf.iff_trans} OF [nnf_thm, simp_thm], cnfx_thm]
  end;

(* ------------------------------------------------------------------------- *)
(*                                  Tactics                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* weakening_tac: removes the first hypothesis of the 'i'-th subgoal         *)
(* ------------------------------------------------------------------------- *)

fun weakening_tac ctxt i =
  dresolve_tac ctxt @{thms cnf.weakening_thm} i THEN assume_tac ctxt (i+1);

(* ------------------------------------------------------------------------- *)
(* cnf_rewrite_tac: converts all premises of the 'i'-th subgoal to CNF       *)
(*      (possibly causing an exponential blowup in the length of each        *)
(*      premise)                                                             *)
(* ------------------------------------------------------------------------- *)

fun cnf_rewrite_tac ctxt i =
  (* cut the CNF formulas as new premises *)
  Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
    let
      val cnf_thms = map (make_cnf_thm ctxt' o HOLogic.dest_Trueprop o Thm.prop_of) prems
      val cut_thms = map (fn (th, pr) => @{thm cnf.cnftac_eq_imp} OF [th, pr]) (cnf_thms ~~ prems)
    in
      cut_facts_tac cut_thms 1
    end) ctxt i
  (* remove the original premises *)
  THEN SELECT_GOAL (fn thm =>
    let
      val n = Logic.count_prems ((Term.strip_all_body o fst o Logic.dest_implies o Thm.prop_of) thm)
    in
      PRIMITIVE (funpow (n div 2) (Seq.hd o weakening_tac ctxt 1)) thm
    end) i;

(* ------------------------------------------------------------------------- *)
(* cnfx_rewrite_tac: converts all premises of the 'i'-th subgoal to CNF      *)
(*      (possibly introducing new literals)                                  *)
(* ------------------------------------------------------------------------- *)

fun cnfx_rewrite_tac ctxt i =
  (* cut the CNF formulas as new premises *)
  Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
    let
      val cnfx_thms = map (make_cnfx_thm ctxt' o HOLogic.dest_Trueprop o Thm.prop_of) prems
      val cut_thms = map (fn (th, pr) => @{thm cnf.cnftac_eq_imp} OF [th, pr]) (cnfx_thms ~~ prems)
    in
      cut_facts_tac cut_thms 1
    end) ctxt i
  (* remove the original premises *)
  THEN SELECT_GOAL (fn thm =>
    let
      val n = Logic.count_prems ((Term.strip_all_body o fst o Logic.dest_implies o Thm.prop_of) thm)
    in
      PRIMITIVE (funpow (n div 2) (Seq.hd o weakening_tac ctxt 1)) thm
    end) i;

end;
