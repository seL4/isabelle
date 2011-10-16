(*  Title:      Pure/drule.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Derived rules and other operations on theorems.
*)

infix 0 RS RSN RL RLN MRS MRL OF COMP INCR_COMP COMP_INCR;

signature BASIC_DRULE =
sig
  val mk_implies: cterm * cterm -> cterm
  val list_implies: cterm list * cterm -> cterm
  val strip_imp_prems: cterm -> cterm list
  val strip_imp_concl: cterm -> cterm
  val cprems_of: thm -> cterm list
  val cterm_fun: (term -> term) -> (cterm -> cterm)
  val ctyp_fun: (typ -> typ) -> (ctyp -> ctyp)
  val forall_intr_list: cterm list -> thm -> thm
  val forall_intr_vars: thm -> thm
  val forall_elim_list: cterm list -> thm -> thm
  val gen_all: thm -> thm
  val lift_all: cterm -> thm -> thm
  val legacy_freeze_thaw: thm -> thm * (thm -> thm)
  val legacy_freeze_thaw_robust: thm -> thm * (int -> thm -> thm)
  val implies_elim_list: thm -> thm list -> thm
  val implies_intr_list: cterm list -> thm -> thm
  val instantiate_normalize: (ctyp * ctyp) list * (cterm * cterm) list -> thm -> thm
  val zero_var_indexes_list: thm list -> thm list
  val zero_var_indexes: thm -> thm
  val implies_intr_hyps: thm -> thm
  val rotate_prems: int -> thm -> thm
  val rearrange_prems: int list -> thm -> thm
  val RSN: thm * (int * thm) -> thm
  val RS: thm * thm -> thm
  val RLN: thm list * (int * thm list) -> thm list
  val RL: thm list * thm list -> thm list
  val MRS: thm list * thm -> thm
  val MRL: thm list list * thm list -> thm list
  val OF: thm * thm list -> thm
  val compose: thm * int * thm -> thm list
  val COMP: thm * thm -> thm
  val INCR_COMP: thm * thm -> thm
  val COMP_INCR: thm * thm -> thm
  val cterm_instantiate: (cterm*cterm)list -> thm -> thm
  val size_of_thm: thm -> int
  val reflexive_thm: thm
  val symmetric_thm: thm
  val transitive_thm: thm
  val symmetric_fun: thm -> thm
  val extensional: thm -> thm
  val equals_cong: thm
  val imp_cong: thm
  val swap_prems_eq: thm
  val asm_rl: thm
  val cut_rl: thm
  val revcut_rl: thm
  val thin_rl: thm
  val triv_forall_equality: thm
  val distinct_prems_rl: thm
  val swap_prems_rl: thm
  val equal_intr_rule: thm
  val equal_elim_rule1: thm
  val equal_elim_rule2: thm
  val instantiate': ctyp option list -> cterm option list -> thm -> thm
end;

signature DRULE =
sig
  include BASIC_DRULE
  val generalize: string list * string list -> thm -> thm
  val list_comb: cterm * cterm list -> cterm
  val strip_comb: cterm -> cterm * cterm list
  val strip_type: ctyp -> ctyp list * ctyp
  val beta_conv: cterm -> cterm -> cterm
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val flexflex_unique: thm -> thm
  val export_without_context: thm -> thm
  val export_without_context_open: thm -> thm
  val store_thm: binding -> thm -> thm
  val store_standard_thm: binding -> thm -> thm
  val store_thm_open: binding -> thm -> thm
  val store_standard_thm_open: binding -> thm -> thm
  val compose_single: thm * int * thm -> thm
  val imp_cong_rule: thm -> thm -> thm
  val arg_cong_rule: cterm -> thm -> thm
  val binop_cong_rule: cterm -> thm -> thm -> thm
  val fun_cong_rule: thm -> cterm -> thm
  val beta_eta_conversion: cterm -> thm
  val eta_long_conversion: cterm -> thm
  val eta_contraction_rule: thm -> thm
  val norm_hhf_eq: thm
  val norm_hhf_eqs: thm list
  val is_norm_hhf: term -> bool
  val norm_hhf: theory -> term -> term
  val norm_hhf_cterm: cterm -> cterm
  val protect: cterm -> cterm
  val protectI: thm
  val protectD: thm
  val protect_cong: thm
  val implies_intr_protected: cterm list -> thm -> thm
  val termI: thm
  val mk_term: cterm -> thm
  val dest_term: thm -> cterm
  val cterm_rule: (thm -> thm) -> cterm -> cterm
  val term_rule: theory -> (thm -> thm) -> term -> term
  val dummy_thm: thm
  val sort_constraintI: thm
  val sort_constraint_eq: thm
  val with_subgoal: int -> (thm -> thm) -> thm -> thm
  val comp_no_flatten: thm * int -> int -> thm -> thm
  val rename_bvars: (string * string) list -> thm -> thm
  val rename_bvars': string option list -> thm -> thm
  val incr_indexes: thm -> thm -> thm
  val incr_indexes2: thm -> thm -> thm -> thm
  val remdups_rl: thm
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val abs_def: thm -> thm
end;

structure Drule: DRULE =
struct


(** some cterm->cterm operations: faster than calling cterm_of! **)

(* A1==>...An==>B  goes to  [A1,...,An], where B is not an implication *)
fun strip_imp_prems ct =
  let val (cA, cB) = Thm.dest_implies ct
  in cA :: strip_imp_prems cB end
  handle TERM _ => [];

(* A1==>...An==>B  goes to B, where B is not an implication *)
fun strip_imp_concl ct =
  (case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => strip_imp_concl (Thm.dest_arg ct)
  | _ => ct);

(*The premises of a theorem, as a cterm list*)
val cprems_of = strip_imp_prems o cprop_of;

fun cterm_fun f ct = Thm.cterm_of (Thm.theory_of_cterm ct) (f (Thm.term_of ct));
fun ctyp_fun f cT = Thm.ctyp_of (Thm.theory_of_ctyp cT) (f (Thm.typ_of cT));

fun certify t = Thm.cterm_of (Context.the_theory (Context.the_thread_data ())) t;

val implies = certify Logic.implies;
fun mk_implies (A, B) = Thm.capply (Thm.capply implies A) B;

(*cterm version of list_implies: [A1,...,An], B  goes to [|A1;==>;An|]==>B *)
fun list_implies([], B) = B
  | list_implies(A::AS, B) = mk_implies (A, list_implies(AS,B));

(*cterm version of list_comb: maps  (f, [t1,...,tn])  to  f(t1,...,tn) *)
fun list_comb (f, []) = f
  | list_comb (f, t::ts) = list_comb (Thm.capply f t, ts);

(*cterm version of strip_comb: maps  f(t1,...,tn)  to  (f, [t1,...,tn]) *)
fun strip_comb ct =
  let
    fun stripc (p as (ct, cts)) =
      let val (ct1, ct2) = Thm.dest_comb ct
      in stripc (ct1, ct2 :: cts) end handle CTERM _ => p
  in stripc (ct, []) end;

(* cterm version of strip_type: maps  [T1,...,Tn]--->T  to   ([T1,T2,...,Tn], T) *)
fun strip_type cT = (case Thm.typ_of cT of
    Type ("fun", _) =>
      let
        val [cT1, cT2] = Thm.dest_ctyp cT;
        val (cTs, cT') = strip_type cT2
      in (cT1 :: cTs, cT') end
  | _ => ([], cT));

(*Beta-conversion for cterms, where x is an abstraction. Simply returns the rhs
  of the meta-equality returned by the beta_conversion rule.*)
fun beta_conv x y =
  Thm.dest_arg (cprop_of (Thm.beta_conversion false (Thm.capply x y)));



(*** Find the type (sort) associated with a (T)Var or (T)Free in a term
     Used for establishing default types (of variables) and sorts (of
     type variables) when reading another term.
     Index -1 indicates that a (T)Free rather than a (T)Var is wanted.
***)

fun types_sorts thm =
  let
    val vars = Thm.fold_terms Term.add_vars thm [];
    val frees = Thm.fold_terms Term.add_frees thm [];
    val tvars = Thm.fold_terms Term.add_tvars thm [];
    val tfrees = Thm.fold_terms Term.add_tfrees thm [];
    fun types (a, i) =
      if i < 0 then AList.lookup (op =) frees a else AList.lookup (op =) vars (a, i);
    fun sorts (a, i) =
      if i < 0 then AList.lookup (op =) tfrees a else AList.lookup (op =) tvars (a, i);
  in (types, sorts) end;




(** Standardization of rules **)

(*Generalization over a list of variables*)
val forall_intr_list = fold_rev Thm.forall_intr;

(*Generalization over Vars -- canonical order*)
fun forall_intr_vars th =
  fold Thm.forall_intr
    (map (Thm.cterm_of (Thm.theory_of_thm th) o Var) (Thm.fold_terms Term.add_vars th [])) th;

fun outer_params t =
  let val vs = Term.strip_all_vars t
  in Name.variant_list [] (map (Name.clean o #1) vs) ~~ map #2 vs end;

(*generalize outermost parameters*)
fun gen_all th =
  let
    val thy = Thm.theory_of_thm th;
    val {prop, maxidx, ...} = Thm.rep_thm th;
    val cert = Thm.cterm_of thy;
    fun elim (x, T) = Thm.forall_elim (cert (Var ((x, maxidx + 1), T)));
  in fold elim (outer_params prop) th end;

(*lift vars wrt. outermost goal parameters
  -- reverses the effect of gen_all modulo higher-order unification*)
fun lift_all goal th =
  let
    val thy = Theory.merge (Thm.theory_of_cterm goal, Thm.theory_of_thm th);
    val cert = Thm.cterm_of thy;
    val maxidx = Thm.maxidx_of th;
    val ps = outer_params (Thm.term_of goal)
      |> map (fn (x, T) => Var ((x, maxidx + 1), Logic.incr_tvar (maxidx + 1) T));
    val Ts = map Term.fastype_of ps;
    val inst = Thm.fold_terms Term.add_vars th [] |> map (fn (xi, T) =>
      (cert (Var (xi, T)), cert (Term.list_comb (Var (xi, Ts ---> T), ps))));
  in
    th |> Thm.instantiate ([], inst)
    |> fold_rev (Thm.forall_intr o cert) ps
  end;

(*direct generalization*)
fun generalize names th = Thm.generalize names (Thm.maxidx_of th + 1) th;

(*specialization over a list of cterms*)
val forall_elim_list = fold Thm.forall_elim;

(*maps A1,...,An |- B  to  [| A1;...;An |] ==> B*)
val implies_intr_list = fold_rev Thm.implies_intr;

(*maps [| A1;...;An |] ==> B and [A1,...,An]  to  B*)
fun implies_elim_list impth ths = fold Thm.elim_implies ths impth;

(*Reset Var indexes to zero, renaming to preserve distinctness*)
fun zero_var_indexes_list [] = []
  | zero_var_indexes_list ths =
      let
        val thy = Theory.merge_list (map Thm.theory_of_thm ths);
        val certT = Thm.ctyp_of thy and cert = Thm.cterm_of thy;
        val (instT, inst) = Term_Subst.zero_var_indexes_inst (map Thm.full_prop_of ths);
        val cinstT = map (fn (v, T) => (certT (TVar v), certT T)) instT;
        val cinst = map (fn (v, t) => (cert (Var v), cert t)) inst;
      in map (Thm.adjust_maxidx_thm ~1 o Thm.instantiate (cinstT, cinst)) ths end;

val zero_var_indexes = singleton zero_var_indexes_list;


(** Standard form of object-rule: no hypotheses, flexflex constraints,
    Frees, or outer quantifiers; all generality expressed by Vars of index 0.**)

(*Discharge all hypotheses.*)
fun implies_intr_hyps th =
  fold Thm.implies_intr (#hyps (Thm.crep_thm th)) th;

(*Squash a theorem's flexflex constraints provided it can be done uniquely.
  This step can lose information.*)
fun flexflex_unique th =
  if null (Thm.tpairs_of th) then th else
    case distinct Thm.eq_thm (Seq.list_of (Thm.flexflex_rule th)) of
      [th] => th
    | []   => raise THM("flexflex_unique: impossible constraints", 0, [th])
    |  _   => raise THM("flexflex_unique: multiple unifiers", 0, [th]);


(* old-style export without context *)

val export_without_context_open =
  implies_intr_hyps
  #> Thm.forall_intr_frees
  #> `Thm.maxidx_of
  #-> (fn maxidx =>
    Thm.forall_elim_vars (maxidx + 1)
    #> Thm.strip_shyps
    #> zero_var_indexes
    #> Thm.varifyT_global);

val export_without_context =
  flexflex_unique
  #> export_without_context_open
  #> Thm.close_derivation;


(*Convert all Vars in a theorem to Frees.  Also return a function for
  reversing that operation.  DOES NOT WORK FOR TYPE VARIABLES.*)

fun legacy_freeze_thaw_robust th =
 let val fth = Thm.legacy_freezeT th
     val thy = Thm.theory_of_thm fth
 in
   case Thm.fold_terms Term.add_vars fth [] of
       [] => (fth, fn i => fn x => x)   (*No vars: nothing to do!*)
     | vars =>
         let fun newName (ix,_) = (ix, legacy_gensym (string_of_indexname ix))
             val alist = map newName vars
             fun mk_inst (v,T) =
                 (cterm_of thy (Var(v,T)),
                  cterm_of thy (Free(((the o AList.lookup (op =) alist) v), T)))
             val insts = map mk_inst vars
             fun thaw i th' = (*i is non-negative increment for Var indexes*)
                 th' |> forall_intr_list (map #2 insts)
                     |> forall_elim_list (map (Thm.incr_indexes_cterm i o #1) insts)
         in  (Thm.instantiate ([],insts) fth, thaw)  end
 end;

(*Basic version of the function above. No option to rename Vars apart in thaw.
  The Frees created from Vars have nice names.*)
fun legacy_freeze_thaw th =
 let val fth = Thm.legacy_freezeT th
     val thy = Thm.theory_of_thm fth
 in
   case Thm.fold_terms Term.add_vars fth [] of
       [] => (fth, fn x => x)
     | vars =>
         let fun newName (ix, _) (pairs, used) =
                   let val v = singleton (Name.variant_list used) (string_of_indexname ix)
                   in  ((ix,v)::pairs, v::used)  end;
             val (alist, _) =
                 fold_rev newName vars ([], Thm.fold_terms Term.add_free_names fth [])
             fun mk_inst (v, T) =
                 (cterm_of thy (Var(v,T)),
                  cterm_of thy (Free(((the o AList.lookup (op =) alist) v), T)))
             val insts = map mk_inst vars
             fun thaw th' =
                 th' |> forall_intr_list (map #2 insts)
                     |> forall_elim_list (map #1 insts)
         in  (Thm.instantiate ([],insts) fth, thaw)  end
 end;

(*Rotates a rule's premises to the left by k*)
fun rotate_prems 0 = I
  | rotate_prems k = Thm.permute_prems 0 k;

fun with_subgoal i f = rotate_prems (i - 1) #> f #> rotate_prems (1 - i);

(*Permute prems, where the i-th position in the argument list (counting from 0)
  gives the position within the original thm to be transferred to position i.
  Any remaining trailing positions are left unchanged.*)
val rearrange_prems =
  let
    fun rearr new [] thm = thm
      | rearr new (p :: ps) thm =
          rearr (new + 1)
            (map (fn q => if new <= q andalso q < p then q + 1 else q) ps)
            (Thm.permute_prems (new + 1) (new - p) (Thm.permute_prems new (p - new) thm))
  in rearr 0 end;

(*Resolution: exactly one resolvent must be produced.*)
fun tha RSN (i,thb) =
  case Seq.chop 2 (Thm.biresolution false [(false,tha)] i thb) of
      ([th],_) => th
    | ([],_)   => raise THM("RSN: no unifiers", i, [tha,thb])
    |      _   => raise THM("RSN: multiple unifiers", i, [tha,thb]);

(*resolution: P==>Q, Q==>R gives P==>R. *)
fun tha RS thb = tha RSN (1,thb);

(*For joining lists of rules*)
fun thas RLN (i,thbs) =
  let val resolve = Thm.biresolution false (map (pair false) thas) i
      fun resb thb = Seq.list_of (resolve thb) handle THM _ => []
  in maps resb thbs end;

fun thas RL thbs = thas RLN (1,thbs);

(*Resolve a list of rules against bottom_rl from right to left;
  makes proof trees*)
fun rls MRS bottom_rl =
  let fun rs_aux i [] = bottom_rl
        | rs_aux i (rl::rls) = rl RSN (i, rs_aux (i+1) rls)
  in  rs_aux 1 rls  end;

(*As above, but for rule lists*)
fun rlss MRL bottom_rls =
  let fun rs_aux i [] = bottom_rls
        | rs_aux i (rls::rlss) = rls RLN (i, rs_aux (i+1) rlss)
  in  rs_aux 1 rlss  end;

(*A version of MRS with more appropriate argument order*)
fun bottom_rl OF rls = rls MRS bottom_rl;

(*compose Q and [...,Qi,Q(i+1),...]==>R to [...,Q(i+1),...]==>R
  with no lifting or renaming!  Q may contain ==> or meta-quants
  ALWAYS deletes premise i *)
fun compose(tha,i,thb) =
    distinct Thm.eq_thm (Seq.list_of (Thm.bicompose false (false,tha,0) i thb));

fun compose_single (tha,i,thb) =
  case compose (tha,i,thb) of
    [th] => th
  | _ => raise THM ("compose: unique result expected", i, [tha,thb]);

(*compose Q and [Q1,Q2,...,Qk]==>R to [Q2,...,Qk]==>R getting unique result*)
fun tha COMP thb =
    case compose(tha,1,thb) of
        [th] => th
      | _ =>   raise THM("COMP", 1, [tha,thb]);


(** theorem equality **)

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o Thm.full_prop_of;



(*** Meta-Rewriting Rules ***)

val read_prop = certify o Simple_Syntax.read_prop;

fun store_thm name th =
  Context.>>> (Context.map_theory_result (Global_Theory.store_thm (name, th)));

fun store_thm_open name th =
  Context.>>> (Context.map_theory_result (Global_Theory.store_thm_open (name, th)));

fun store_standard_thm name th = store_thm name (export_without_context th);
fun store_standard_thm_open name thm = store_thm_open name (export_without_context_open thm);

val reflexive_thm =
  let val cx = certify (Var(("x",0),TVar(("'a",0),[])))
  in store_standard_thm_open (Binding.name "reflexive") (Thm.reflexive cx) end;

val symmetric_thm =
  let
    val xy = read_prop "x::'a == y::'a";
    val thm = Thm.implies_intr xy (Thm.symmetric (Thm.assume xy));
  in store_standard_thm_open (Binding.name "symmetric") thm end;

val transitive_thm =
  let
    val xy = read_prop "x::'a == y::'a";
    val yz = read_prop "y::'a == z::'a";
    val xythm = Thm.assume xy;
    val yzthm = Thm.assume yz;
    val thm = Thm.implies_intr yz (Thm.transitive xythm yzthm);
  in store_standard_thm_open (Binding.name "transitive") thm end;

fun symmetric_fun thm = thm RS symmetric_thm;

fun extensional eq =
  let val eq' =
    Thm.abstract_rule "x" (Thm.dest_arg (fst (Thm.dest_equals (cprop_of eq)))) eq
  in Thm.equal_elim (Thm.eta_conversion (cprop_of eq')) eq' end;

val equals_cong =
  store_standard_thm_open (Binding.name "equals_cong")
    (Thm.reflexive (read_prop "x::'a == y::'a"));

val imp_cong =
  let
    val ABC = read_prop "A ==> B::prop == C::prop"
    val AB = read_prop "A ==> B"
    val AC = read_prop "A ==> C"
    val A = read_prop "A"
  in
    store_standard_thm_open (Binding.name "imp_cong") (Thm.implies_intr ABC (Thm.equal_intr
      (Thm.implies_intr AB (Thm.implies_intr A
        (Thm.equal_elim (Thm.implies_elim (Thm.assume ABC) (Thm.assume A))
          (Thm.implies_elim (Thm.assume AB) (Thm.assume A)))))
      (Thm.implies_intr AC (Thm.implies_intr A
        (Thm.equal_elim (Thm.symmetric (Thm.implies_elim (Thm.assume ABC) (Thm.assume A)))
          (Thm.implies_elim (Thm.assume AC) (Thm.assume A)))))))
  end;

val swap_prems_eq =
  let
    val ABC = read_prop "A ==> B ==> C"
    val BAC = read_prop "B ==> A ==> C"
    val A = read_prop "A"
    val B = read_prop "B"
  in
    store_standard_thm_open (Binding.name "swap_prems_eq")
      (Thm.equal_intr
        (Thm.implies_intr ABC (Thm.implies_intr B (Thm.implies_intr A
          (Thm.implies_elim (Thm.implies_elim (Thm.assume ABC) (Thm.assume A)) (Thm.assume B)))))
        (Thm.implies_intr BAC (Thm.implies_intr A (Thm.implies_intr B
          (Thm.implies_elim (Thm.implies_elim (Thm.assume BAC) (Thm.assume B)) (Thm.assume A))))))
  end;

val imp_cong_rule = Thm.combination o Thm.combination (Thm.reflexive implies);

fun arg_cong_rule ct th = Thm.combination (Thm.reflexive ct) th;    (*AP_TERM in LCF/HOL*)
fun fun_cong_rule th ct = Thm.combination th (Thm.reflexive ct);    (*AP_THM in LCF/HOL*)
fun binop_cong_rule ct th1 th2 = Thm.combination (arg_cong_rule ct th1) th2;

local
  val dest_eq = Thm.dest_equals o cprop_of
  val rhs_of = snd o dest_eq
in
fun beta_eta_conversion t =
  let val thm = Thm.beta_conversion true t
  in Thm.transitive thm (Thm.eta_conversion (rhs_of thm)) end
end;

fun eta_long_conversion ct =
  Thm.transitive
    (beta_eta_conversion ct)
    (Thm.symmetric (beta_eta_conversion (cterm_fun (Pattern.eta_long []) ct)));

(*Contract all eta-redexes in the theorem, lest they give rise to needless abstractions*)
fun eta_contraction_rule th =
  Thm.equal_elim (Thm.eta_conversion (cprop_of th)) th;


(* abs_def *)

(*
   f ?x1 ... ?xn == u
  --------------------
   f == %x1 ... xn. u
*)

local

fun contract_lhs th =
  Thm.transitive (Thm.symmetric (beta_eta_conversion
    (fst (Thm.dest_equals (cprop_of th))))) th;

fun var_args ct =
  (case try Thm.dest_comb ct of
    SOME (f, arg) =>
      (case Thm.term_of arg of
        Var ((x, _), _) => update (eq_snd (op aconvc)) (x, arg) (var_args f)
      | _ => [])
  | NONE => []);

in

fun abs_def th =
  let
    val th' = contract_lhs th;
    val args = var_args (Thm.lhs_of th');
  in contract_lhs (fold (uncurry Thm.abstract_rule) args th') end;

end;



(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl = store_standard_thm_open (Binding.name "asm_rl") (Thm.trivial (read_prop "?psi"));

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl =
  store_standard_thm_open (Binding.name "cut_rl")
    (Thm.trivial (read_prop "?psi ==> ?theta"));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let
    val V = read_prop "V";
    val VW = read_prop "V ==> W";
  in
    store_standard_thm_open (Binding.name "revcut_rl")
      (Thm.implies_intr V (Thm.implies_intr VW (Thm.implies_elim (Thm.assume VW) (Thm.assume V))))
  end;

(*for deleting an unwanted assumption*)
val thin_rl =
  let
    val V = read_prop "V";
    val W = read_prop "W";
    val thm = Thm.implies_intr V (Thm.implies_intr W (Thm.assume W));
  in store_standard_thm_open (Binding.name "thin_rl") thm end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let
    val V = read_prop "V";
    val QV = read_prop "!!x::'a. V";
    val x = certify (Free ("x", Term.aT []));
  in
    store_standard_thm_open (Binding.name "triv_forall_equality")
      (Thm.equal_intr (Thm.implies_intr QV (Thm.forall_elim x (Thm.assume QV)))
        (Thm.implies_intr V (Thm.forall_intr x (Thm.assume V))))
  end;

(* (PROP ?Phi ==> PROP ?Phi ==> PROP ?Psi) ==>
   (PROP ?Phi ==> PROP ?Psi)
*)
val distinct_prems_rl =
  let
    val AAB = read_prop "Phi ==> Phi ==> Psi";
    val A = read_prop "Phi";
  in
    store_standard_thm_open (Binding.name "distinct_prems_rl")
      (implies_intr_list [AAB, A] (implies_elim_list (Thm.assume AAB) [Thm.assume A, Thm.assume A]))
  end;

(* (PROP ?PhiA ==> PROP ?PhiB ==> PROP ?Psi) ==>
   (PROP ?PhiB ==> PROP ?PhiA ==> PROP ?Psi)
   `thm COMP swap_prems_rl' swaps the first two premises of `thm'
*)
val swap_prems_rl =
  let
    val cmajor = read_prop "PhiA ==> PhiB ==> Psi";
    val major = Thm.assume cmajor;
    val cminor1 = read_prop "PhiA";
    val minor1 = Thm.assume cminor1;
    val cminor2 = read_prop "PhiB";
    val minor2 = Thm.assume cminor2;
  in
    store_standard_thm_open (Binding.name "swap_prems_rl")
      (Thm.implies_intr cmajor (Thm.implies_intr cminor2 (Thm.implies_intr cminor1
        (Thm.implies_elim (Thm.implies_elim major minor1) minor2))))
  end;

(* [| PROP ?phi ==> PROP ?psi; PROP ?psi ==> PROP ?phi |]
   ==> PROP ?phi == PROP ?psi
   Introduction rule for == as a meta-theorem.
*)
val equal_intr_rule =
  let
    val PQ = read_prop "phi ==> psi";
    val QP = read_prop "psi ==> phi";
  in
    store_standard_thm_open (Binding.name "equal_intr_rule")
      (Thm.implies_intr PQ (Thm.implies_intr QP (Thm.equal_intr (Thm.assume PQ) (Thm.assume QP))))
  end;

(* PROP ?phi == PROP ?psi ==> PROP ?phi ==> PROP ?psi *)
val equal_elim_rule1 =
  let
    val eq = read_prop "phi::prop == psi::prop";
    val P = read_prop "phi";
  in
    store_standard_thm_open (Binding.name "equal_elim_rule1")
      (Thm.equal_elim (Thm.assume eq) (Thm.assume P) |> implies_intr_list [eq, P])
  end;

(* PROP ?psi == PROP ?phi ==> PROP ?phi ==> PROP ?psi *)
val equal_elim_rule2 =
  store_standard_thm_open (Binding.name "equal_elim_rule2")
    (symmetric_thm RS equal_elim_rule1);

(* PROP ?phi ==> PROP ?phi ==> PROP ?psi ==> PROP ?psi *)
val remdups_rl =
  let
    val P = read_prop "phi";
    val Q = read_prop "psi";
    val thm = implies_intr_list [P, P, Q] (Thm.assume Q);
  in store_standard_thm_open (Binding.name "remdups_rl") thm end;



(** embedded terms and types **)

local
  val A = certify (Free ("A", propT));
  val axiom = Thm.unvarify_global o Thm.axiom (Context.the_theory (Context.the_thread_data ()));
  val prop_def = axiom "Pure.prop_def";
  val term_def = axiom "Pure.term_def";
  val sort_constraint_def = axiom "Pure.sort_constraint_def";
  val C = Thm.lhs_of sort_constraint_def;
  val T = Thm.dest_arg C;
  val CA = mk_implies (C, A);
in

(* protect *)

val protect = Thm.capply (certify Logic.protectC);

val protectI =
  store_standard_thm (Binding.conceal (Binding.name "protectI"))
    (Thm.equal_elim (Thm.symmetric prop_def) (Thm.assume A));

val protectD =
  store_standard_thm (Binding.conceal (Binding.name "protectD"))
    (Thm.equal_elim prop_def (Thm.assume (protect A)));

val protect_cong =
  store_standard_thm_open (Binding.name "protect_cong") (Thm.reflexive (protect A));

fun implies_intr_protected asms th =
  let val asms' = map protect asms in
    implies_elim_list
      (implies_intr_list asms th)
      (map (fn asm' => Thm.assume asm' RS protectD) asms')
    |> implies_intr_list asms'
  end;


(* term *)

val termI =
  store_standard_thm (Binding.conceal (Binding.name "termI"))
    (Thm.equal_elim (Thm.symmetric term_def) (Thm.forall_intr A (Thm.trivial A)));

fun mk_term ct =
  let
    val thy = Thm.theory_of_cterm ct;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val T = Thm.typ_of (Thm.ctyp_of_term ct);
    val a = certT (TVar (("'a", 0), []));
    val x = cert (Var (("x", 0), T));
  in Thm.instantiate ([(a, certT T)], [(x, ct)]) termI end;

fun dest_term th =
  let val cprop = strip_imp_concl (Thm.cprop_of th) in
    if can Logic.dest_term (Thm.term_of cprop) then
      Thm.dest_arg cprop
    else raise THM ("dest_term", 0, [th])
  end;

fun cterm_rule f = dest_term o f o mk_term;
fun term_rule thy f t = Thm.term_of (cterm_rule f (Thm.cterm_of thy t));

val dummy_thm = mk_term (certify Term.dummy_prop);


(* sort_constraint *)

val sort_constraintI =
  store_standard_thm (Binding.conceal (Binding.name "sort_constraintI"))
    (Thm.equal_elim (Thm.symmetric sort_constraint_def) (mk_term T));

val sort_constraint_eq =
  store_standard_thm (Binding.conceal (Binding.name "sort_constraint_eq"))
    (Thm.equal_intr
      (Thm.implies_intr CA (Thm.implies_elim (Thm.assume CA)
        (Thm.unvarify_global sort_constraintI)))
      (implies_intr_list [A, C] (Thm.assume A)));

end;


(* HHF normalization *)

(* (PROP ?phi ==> (!!x. PROP ?psi(x))) == (!!x. PROP ?phi ==> PROP ?psi(x)) *)
val norm_hhf_eq =
  let
    val aT = TFree ("'a", []);
    val all = Term.all aT;
    val x = Free ("x", aT);
    val phi = Free ("phi", propT);
    val psi = Free ("psi", aT --> propT);

    val cx = certify x;
    val cphi = certify phi;
    val lhs = certify (Logic.mk_implies (phi, all $ Abs ("x", aT, psi $ Bound 0)));
    val rhs = certify (all $ Abs ("x", aT, Logic.mk_implies (phi, psi $ Bound 0)));
  in
    Thm.equal_intr
      (Thm.implies_elim (Thm.assume lhs) (Thm.assume cphi)
        |> Thm.forall_elim cx
        |> Thm.implies_intr cphi
        |> Thm.forall_intr cx
        |> Thm.implies_intr lhs)
      (Thm.implies_elim
          (Thm.assume rhs |> Thm.forall_elim cx) (Thm.assume cphi)
        |> Thm.forall_intr cx
        |> Thm.implies_intr cphi
        |> Thm.implies_intr rhs)
    |> store_standard_thm_open (Binding.name "norm_hhf_eq")
  end;

val norm_hhf_prop = Logic.dest_equals (Thm.prop_of norm_hhf_eq);
val norm_hhf_eqs = [norm_hhf_eq, sort_constraint_eq];

fun is_norm_hhf (Const ("Pure.sort_constraint", _)) = false
  | is_norm_hhf (Const ("==>", _) $ _ $ (Const ("all", _) $ _)) = false
  | is_norm_hhf (Abs _ $ _) = false
  | is_norm_hhf (t $ u) = is_norm_hhf t andalso is_norm_hhf u
  | is_norm_hhf (Abs (_, _, t)) = is_norm_hhf t
  | is_norm_hhf _ = true;

fun norm_hhf thy t =
  if is_norm_hhf t then t
  else Pattern.rewrite_term thy [norm_hhf_prop] [] t;

fun norm_hhf_cterm ct =
  if is_norm_hhf (Thm.term_of ct) then ct
  else cterm_fun (Pattern.rewrite_term (Thm.theory_of_cterm ct) [norm_hhf_prop] []) ct;


(* var indexes *)

fun incr_indexes th = Thm.incr_indexes (Thm.maxidx_of th + 1);

fun incr_indexes2 th1 th2 =
  Thm.incr_indexes (Int.max (Thm.maxidx_of th1, Thm.maxidx_of th2) + 1);

fun th1 INCR_COMP th2 = incr_indexes th2 th1 COMP th2;
fun th1 COMP_INCR th2 = th1 COMP incr_indexes th1 th2;

fun comp_no_flatten (th, n) i rule =
  (case distinct Thm.eq_thm (Seq.list_of
      (Thm.compose_no_flatten false (th, n) i (incr_indexes th rule))) of
    [th'] => th'
  | [] => raise THM ("comp_no_flatten", i, [th, rule])
  | _ => raise THM ("comp_no_flatten: unique result expected", i, [th, rule]));



(*** Instantiate theorem th, reading instantiations in theory thy ****)

fun instantiate_normalize instpair th =
  Thm.adjust_maxidx_thm ~1 (Thm.instantiate instpair th COMP_INCR asm_rl);

(*Left-to-right replacements: tpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms, inferring type instantiations. *)
local
  fun add_types ((ct,cu), (thy,tye,maxidx)) =
    let
        val thyt = Thm.theory_of_cterm ct;
        val thyu = Thm.theory_of_cterm cu;
        val {t, T, maxidx = maxt, ...} = Thm.rep_cterm ct;
        val {t = u, T = U, maxidx = maxu, ...} = Thm.rep_cterm cu;
        val maxi = Int.max(maxidx, Int.max(maxt, maxu));
        val thy' = Theory.merge(thy, Theory.merge(thyt, thyu))
        val (tye',maxi') = Sign.typ_unify thy' (T, U) (tye, maxi)
          handle Type.TUNIFY => raise TYPE ("Ill-typed instantiation:\nType\n" ^
            Syntax.string_of_typ_global thy' (Envir.norm_type tye T) ^
            "\nof variable " ^
            Syntax.string_of_term_global thy' (Term.map_types (Envir.norm_type tye) t) ^
            "\ncannot be unified with type\n" ^
            Syntax.string_of_typ_global thy' (Envir.norm_type tye U) ^ "\nof term " ^
            Syntax.string_of_term_global thy' (Term.map_types (Envir.norm_type tye) u),
            [T, U], [t, u])
    in  (thy', tye', maxi')  end;
in
fun cterm_instantiate [] th = th
  | cterm_instantiate ctpairs0 th =
  let val (thy,tye,_) = List.foldr add_types (Thm.theory_of_thm th, Vartab.empty, 0) ctpairs0
      fun instT(ct,cu) =
        let val inst = cterm_of thy o Term.map_types (Envir.norm_type tye) o term_of
        in (inst ct, inst cu) end
      fun ctyp2 (ixn, (S, T)) = (ctyp_of thy (TVar (ixn, S)), ctyp_of thy (Envir.norm_type tye T))
  in  instantiate_normalize (map ctyp2 (Vartab.dest tye), map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible theories",0,[th])
       | TYPE (msg, _, _) => raise THM(msg, 0, [th])
end;



(** variations on instantiate **)

(* instantiate by left-to-right occurrence of variables *)

fun instantiate' cTs cts thm =
  let
    fun err msg =
      raise TYPE ("instantiate': " ^ msg,
        map_filter (Option.map Thm.typ_of) cTs,
        map_filter (Option.map Thm.term_of) cts);

    fun inst_of (v, ct) =
      (Thm.cterm_of (Thm.theory_of_cterm ct) (Var v), ct)
        handle TYPE (msg, _, _) => err msg;

    fun tyinst_of (v, cT) =
      (Thm.ctyp_of (Thm.theory_of_ctyp cT) (TVar v), cT)
        handle TYPE (msg, _, _) => err msg;

    fun zip_vars xs ys =
      zip_options xs ys handle ListPair.UnequalLengths =>
        err "more instantiations than variables in thm";

    (*instantiate types first!*)
    val thm' =
      if forall is_none cTs then thm
      else Thm.instantiate
        (map tyinst_of (zip_vars (rev (Thm.fold_terms Term.add_tvars thm [])) cTs), []) thm;
    val thm'' =
      if forall is_none cts then thm'
      else Thm.instantiate
        ([], map inst_of (zip_vars (rev (Thm.fold_terms Term.add_vars thm' [])) cts)) thm';
    in thm'' end;



(** renaming of bound variables **)

(* replace bound variables x_i in thm by y_i *)
(* where vs = [(x_1, y_1), ..., (x_n, y_n)]  *)

fun rename_bvars [] thm = thm
  | rename_bvars vs thm =
      let
        val cert = Thm.cterm_of (Thm.theory_of_thm thm);
        fun ren (Abs (x, T, t)) = Abs (AList.lookup (op =) vs x |> the_default x, T, ren t)
          | ren (t $ u) = ren t $ ren u
          | ren t = t;
      in Thm.equal_elim (Thm.reflexive (cert (ren (Thm.prop_of thm)))) thm end;


(* renaming in left-to-right order *)

fun rename_bvars' xs thm =
  let
    val cert = Thm.cterm_of (Thm.theory_of_thm thm);
    val prop = Thm.prop_of thm;
    fun rename [] t = ([], t)
      | rename (x' :: xs) (Abs (x, T, t)) =
          let val (xs', t') = rename xs t
          in (xs', Abs (the_default x x', T, t')) end
      | rename xs (t $ u) =
          let
            val (xs', t') = rename xs t;
            val (xs'', u') = rename xs' u
          in (xs'', t' $ u') end
      | rename xs t = (xs, t);
  in case rename xs prop of
      ([], prop') => Thm.equal_elim (Thm.reflexive (cert prop')) thm
    | _ => error "More names than abstractions in theorem"
  end;



(** multi_resolve **)

local

fun res th i rule =
  Thm.biresolution false [(false, th)] i rule handle THM _ => Seq.empty;

fun multi_res _ [] rule = Seq.single rule
  | multi_res i (th :: ths) rule = Seq.maps (res th i) (multi_res (i + 1) ths rule);

in

val multi_resolve = multi_res 1;
fun multi_resolves facts rules = Seq.maps (multi_resolve facts) (Seq.of_list rules);

end;

end;

structure Basic_Drule: BASIC_DRULE = Drule;
open Basic_Drule;
