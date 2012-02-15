(*  Title:      HOL/Tools/SMT/z3_proof_literals.ML
    Author:     Sascha Boehme, TU Muenchen

Proof tools related to conjunctions and disjunctions.
*)

signature Z3_PROOF_LITERALS =
sig
  (*literal table*)
  type littab = thm Termtab.table
  val make_littab: thm list -> littab
  val insert_lit: thm -> littab -> littab
  val delete_lit: thm -> littab -> littab
  val lookup_lit: littab -> term -> thm option
  val get_first_lit: (term -> bool) -> littab -> thm option

  (*rules*)
  val true_thm: thm
  val rewrite_true: thm

  (*properties*)
  val is_conj: term -> bool
  val is_disj: term -> bool
  val exists_lit: bool -> (term -> bool) -> term -> bool
  val negate: cterm -> cterm

  (*proof tools*)
  val explode: bool -> bool -> bool -> term list -> thm -> thm list
  val join: bool -> littab -> term -> thm
  val prove_conj_disj_eq: cterm -> thm
end

structure Z3_Proof_Literals: Z3_PROOF_LITERALS =
struct



(* literal table *)

type littab = thm Termtab.table

fun make_littab thms =
  fold (Termtab.update o `SMT_Utils.prop_of) thms Termtab.empty

fun insert_lit thm = Termtab.update (`SMT_Utils.prop_of thm)
fun delete_lit thm = Termtab.delete (SMT_Utils.prop_of thm)
fun lookup_lit lits = Termtab.lookup lits
fun get_first_lit f =
  Termtab.get_first (fn (t, thm) => if f t then SOME thm else NONE)



(* rules *)

val true_thm = @{lemma "~False" by simp}
val rewrite_true = @{lemma "True == ~ False" by simp}



(* properties and term operations *)

val is_neg = (fn @{const Not} $ _ => true | _ => false)
fun is_neg' f = (fn @{const Not} $ t => f t | _ => false)
val is_dneg = is_neg' is_neg
val is_conj = (fn @{const HOL.conj} $ _ $ _ => true | _ => false)
val is_disj = (fn @{const HOL.disj} $ _ $ _ => true | _ => false)

fun dest_disj_term' f = (fn
    @{const Not} $ (@{const HOL.disj} $ t $ u) => SOME (f t, f u)
  | _ => NONE)

val dest_conj_term = (fn @{const HOL.conj} $ t $ u => SOME (t, u) | _ => NONE)
val dest_disj_term =
  dest_disj_term' (fn @{const Not} $ t => t | t => @{const Not} $ t)

fun exists_lit is_conj P =
  let
    val dest = if is_conj then dest_conj_term else dest_disj_term
    fun exists t = P t orelse
      (case dest t of
        SOME (t1, t2) => exists t1 orelse exists t2
      | NONE => false)
  in exists end

val negate = Thm.apply (Thm.cterm_of @{theory} @{const Not})



(* proof tools *)

(** explosion of conjunctions and disjunctions **)

local
  val precomp = Z3_Proof_Tools.precompose2

  fun destc ct = Thm.dest_binop (Thm.dest_arg ct)
  val dest_conj1 = precomp destc @{thm conjunct1}
  val dest_conj2 = precomp destc @{thm conjunct2}
  fun dest_conj_rules t =
    dest_conj_term t |> Option.map (K (dest_conj1, dest_conj2))
    
  fun destd f ct = f (Thm.dest_binop (Thm.dest_arg (Thm.dest_arg ct)))
  val dn1 = apfst Thm.dest_arg and dn2 = apsnd Thm.dest_arg
  val dest_disj1 = precomp (destd I) @{lemma "~(P | Q) ==> ~P" by fast}
  val dest_disj2 = precomp (destd dn1) @{lemma "~(~P | Q) ==> P" by fast}
  val dest_disj3 = precomp (destd I) @{lemma "~(P | Q) ==> ~Q" by fast}
  val dest_disj4 = precomp (destd dn2) @{lemma "~(P | ~Q) ==> Q" by fast}

  fun dest_disj_rules t =
    (case dest_disj_term' is_neg t of
      SOME (true, true) => SOME (dest_disj2, dest_disj4)
    | SOME (true, false) => SOME (dest_disj2, dest_disj3)
    | SOME (false, true) => SOME (dest_disj1, dest_disj4)
    | SOME (false, false) => SOME (dest_disj1, dest_disj3)
    | NONE => NONE)

  fun destn ct = [Thm.dest_arg (Thm.dest_arg (Thm.dest_arg ct))]
  val dneg_rule = Z3_Proof_Tools.precompose destn @{thm notnotD}
in

(*
  explode a term into literals and collect all rules to be able to deduce
  particular literals afterwards
*)
fun explode_term is_conj =
  let
    val dest = if is_conj then dest_conj_term else dest_disj_term
    val dest_rules = if is_conj then dest_conj_rules else dest_disj_rules

    fun add (t, rs) = Termtab.map_default (t, rs)
      (fn rs' => if length rs' < length rs then rs' else rs)

    fun explode1 rules t =
      (case dest t of
        SOME (t1, t2) =>
          let val (rule1, rule2) = the (dest_rules t)
          in
            explode1 (rule1 :: rules) t1 #>
            explode1 (rule2 :: rules) t2 #>
            add (t, rev rules)
          end
      | NONE => add (t, rev rules))

    fun explode0 (@{const Not} $ (@{const Not} $ t)) =
          Termtab.make [(t, [dneg_rule])]
      | explode0 t = explode1 [] t Termtab.empty

  in explode0 end

(*
  extract a literal by applying previously collected rules
*)
fun extract_lit thm rules = fold Z3_Proof_Tools.compose rules thm


(*
  explode a theorem into its literals
*)
fun explode is_conj full keep_intermediate stop_lits =
  let
    val dest_rules = if is_conj then dest_conj_rules else dest_disj_rules
    val tab = fold (Termtab.update o rpair ()) stop_lits Termtab.empty

    fun explode1 thm =
      if Termtab.defined tab (SMT_Utils.prop_of thm) then cons thm
      else
        (case dest_rules (SMT_Utils.prop_of thm) of
          SOME (rule1, rule2) =>
            explode2 rule1 thm #>
            explode2 rule2 thm #>
            keep_intermediate ? cons thm
        | NONE => cons thm)

    and explode2 dest_rule thm =
      if full orelse
        exists_lit is_conj (Termtab.defined tab) (SMT_Utils.prop_of thm)
      then explode1 (Z3_Proof_Tools.compose dest_rule thm)
      else cons (Z3_Proof_Tools.compose dest_rule thm)

    fun explode0 thm =
      if not is_conj andalso is_dneg (SMT_Utils.prop_of thm)
      then [Z3_Proof_Tools.compose dneg_rule thm]
      else explode1 thm []

  in explode0 end

end



(** joining of literals to conjunctions or disjunctions **)

local
  fun on_cprem i f thm = f (Thm.cprem_of thm i)
  fun on_cprop f thm = f (Thm.cprop_of thm)
  fun precomp2 f g thm = (on_cprem 1 f thm, on_cprem 2 g thm, f, g, thm)
  fun comp2 (cv1, cv2, f, g, rule) thm1 thm2 =
    Thm.instantiate ([], [(cv1, on_cprop f thm1), (cv2, on_cprop g thm2)]) rule
    |> Z3_Proof_Tools.discharge thm1 |> Z3_Proof_Tools.discharge thm2

  fun d1 ct = Thm.dest_arg ct and d2 ct = Thm.dest_arg (Thm.dest_arg ct)

  val conj_rule = precomp2 d1 d1 @{thm conjI}
  fun comp_conj ((_, thm1), (_, thm2)) = comp2 conj_rule thm1 thm2

  val disj1 = precomp2 d2 d2 @{lemma "~P ==> ~Q ==> ~(P | Q)" by fast}
  val disj2 = precomp2 d2 d1 @{lemma "~P ==> Q ==> ~(P | ~Q)" by fast}
  val disj3 = precomp2 d1 d2 @{lemma "P ==> ~Q ==> ~(~P | Q)" by fast}
  val disj4 = precomp2 d1 d1 @{lemma "P ==> Q ==> ~(~P | ~Q)" by fast}

  fun comp_disj ((false, thm1), (false, thm2)) = comp2 disj1 thm1 thm2
    | comp_disj ((false, thm1), (true, thm2)) = comp2 disj2 thm1 thm2
    | comp_disj ((true, thm1), (false, thm2)) = comp2 disj3 thm1 thm2
    | comp_disj ((true, thm1), (true, thm2)) = comp2 disj4 thm1 thm2

  fun dest_conj (@{const HOL.conj} $ t $ u) = ((false, t), (false, u))
    | dest_conj t = raise TERM ("dest_conj", [t])

  val neg = (fn @{const Not} $ t => (true, t) | t => (false, @{const Not} $ t))
  fun dest_disj (@{const Not} $ (@{const HOL.disj} $ t $ u)) = (neg t, neg u)
    | dest_disj t = raise TERM ("dest_disj", [t])

  val precomp = Z3_Proof_Tools.precompose
  val dnegE = precomp (single o d2 o d1) @{thm notnotD}
  val dnegI = precomp (single o d1) @{lemma "P ==> ~~P" by fast}
  fun as_dneg f t = f (@{const Not} $ (@{const Not} $ t))

  val precomp2 = Z3_Proof_Tools.precompose2
  fun dni f = apsnd f o Thm.dest_binop o f o d1
  val negIffE = precomp2 (dni d1) @{lemma "~(P = (~Q)) ==> Q = P" by fast}
  val negIffI = precomp2 (dni I) @{lemma "P = Q ==> ~(Q = (~P))" by fast}
  val iff_const = @{const HOL.eq (bool)}
  fun as_negIff f (@{const HOL.eq (bool)} $ t $ u) =
        f (@{const Not} $ (iff_const $ u $ (@{const Not} $ t)))
    | as_negIff _ _ = NONE
in

fun join is_conj littab t =
  let
    val comp = if is_conj then comp_conj else comp_disj
    val dest = if is_conj then dest_conj else dest_disj

    val lookup = lookup_lit littab

    fun lookup_rule t =
      (case t of
        @{const Not} $ (@{const Not} $ t) =>
          (Z3_Proof_Tools.compose dnegI, lookup t)
      | @{const Not} $ (@{const HOL.eq (bool)} $ t $ (@{const Not} $ u)) =>
          (Z3_Proof_Tools.compose negIffI, lookup (iff_const $ u $ t))
      | @{const Not} $ ((eq as Const (@{const_name HOL.eq}, _)) $ t $ u) =>
          let fun rewr lit = lit COMP @{thm not_sym}
          in (rewr, lookup (@{const Not} $ (eq $ u $ t))) end
      | _ =>
          (case as_dneg lookup t of
            NONE => (Z3_Proof_Tools.compose negIffE, as_negIff lookup t)
          | x => (Z3_Proof_Tools.compose dnegE, x)))

    fun join1 (s, t) =
      (case lookup t of
        SOME lit => (s, lit)
      | NONE => 
          (case lookup_rule t of
            (rewrite, SOME lit) => (s, rewrite lit)
          | (_, NONE) => (s, comp (pairself join1 (dest t)))))

  in snd (join1 (if is_conj then (false, t) else (true, t))) end

end



(** proving equality of conjunctions or disjunctions **)

fun iff_intro thm1 thm2 = thm2 COMP (thm1 COMP @{thm iffI})

local
  val cp1 = @{lemma "(~P) = (~Q) ==> P = Q" by simp}
  val cp2 = @{lemma "(~P) = Q ==> P = (~Q)" by fastforce}
  val cp3 = @{lemma "P = (~Q) ==> (~P) = Q" by simp}
in
fun contrapos1 prove (ct, cu) = prove (negate ct, negate cu) COMP cp1
fun contrapos2 prove (ct, cu) = prove (negate ct, Thm.dest_arg cu) COMP cp2
fun contrapos3 prove (ct, cu) = prove (Thm.dest_arg ct, negate cu) COMP cp3
end


local
  val contra_rule = @{lemma "P ==> ~P ==> False" by (rule notE)}
  fun contra_left conj thm =
    let
      val rules = explode_term conj (SMT_Utils.prop_of thm)
      fun contra_lits (t, rs) =
        (case t of
          @{const Not} $ u => Termtab.lookup rules u |> Option.map (pair rs)
        | _ => NONE)
    in
      (case Termtab.lookup rules @{const False} of
        SOME rs => extract_lit thm rs
      | NONE =>
          the (Termtab.get_first contra_lits rules)
          |> pairself (extract_lit thm)
          |> (fn (nlit, plit) => nlit COMP (plit COMP contra_rule)))
    end

  val falseE_v = Thm.dest_arg (Thm.dest_arg (Thm.cprop_of @{thm FalseE}))
  fun contra_right ct = Thm.instantiate ([], [(falseE_v, ct)]) @{thm FalseE}
in
fun contradict conj ct =
  iff_intro (Z3_Proof_Tools.under_assumption (contra_left conj) ct)
    (contra_right ct)
end


local
  fun prove_eq l r (cl, cr) =
    let
      fun explode' is_conj = explode is_conj true (l <> r) []
      fun make_tab is_conj thm = make_littab (true_thm :: explode' is_conj thm)
      fun prove is_conj ct tab = join is_conj tab (Thm.term_of ct)

      val thm1 = Z3_Proof_Tools.under_assumption (prove r cr o make_tab l) cl
      val thm2 = Z3_Proof_Tools.under_assumption (prove l cl o make_tab r) cr
    in iff_intro thm1 thm2 end

  datatype conj_disj = CONJ | DISJ | NCON | NDIS
  fun kind_of t =
    if is_conj t then SOME CONJ
    else if is_disj t then SOME DISJ
    else if is_neg' is_conj t then SOME NCON
    else if is_neg' is_disj t then SOME NDIS
    else NONE
in

fun prove_conj_disj_eq ct =
  let val cp as (cl, cr) = Thm.dest_binop (Thm.dest_arg ct)
  in
    (case (kind_of (Thm.term_of cl), Thm.term_of cr) of
      (SOME CONJ, @{const False}) => contradict true cl
    | (SOME DISJ, @{const Not} $ @{const False}) =>
        contrapos2 (contradict false o fst) cp
    | (kl, _) =>
        (case (kl, kind_of (Thm.term_of cr)) of
          (SOME CONJ, SOME CONJ) => prove_eq true true cp
        | (SOME CONJ, SOME NDIS) => prove_eq true false cp
        | (SOME CONJ, _) => prove_eq true true cp
        | (SOME DISJ, SOME DISJ) => contrapos1 (prove_eq false false) cp
        | (SOME DISJ, SOME NCON) => contrapos2 (prove_eq false true) cp
        | (SOME DISJ, _) => contrapos1 (prove_eq false false) cp
        | (SOME NCON, SOME NCON) => contrapos1 (prove_eq true true) cp
        | (SOME NCON, SOME DISJ) => contrapos3 (prove_eq true false) cp
        | (SOME NCON, NONE) => contrapos3 (prove_eq true false) cp
        | (SOME NDIS, SOME NDIS) => prove_eq false false cp
        | (SOME NDIS, SOME CONJ) => prove_eq false true cp
        | (SOME NDIS, NONE) => prove_eq false true cp
        | _ => raise CTERM ("prove_conj_disj_eq", [ct])))
  end

end

end
