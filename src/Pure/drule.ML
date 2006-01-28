(*  Title:      Pure/drule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Derived rules and other operations on theorems.
*)

infix 0 RS RSN RL RLN MRS MRL OF COMP;

signature BASIC_DRULE =
sig
  val mk_implies: cterm * cterm -> cterm
  val list_implies: cterm list * cterm -> cterm
  val dest_implies: cterm -> cterm * cterm
  val dest_equals: cterm -> cterm * cterm
  val strip_imp_prems: cterm -> cterm list
  val strip_imp_concl: cterm -> cterm
  val cprems_of: thm -> cterm list
  val cterm_fun: (term -> term) -> (cterm -> cterm)
  val ctyp_fun: (typ -> typ) -> (ctyp -> ctyp)
  val read_insts: theory -> (indexname -> typ option) * (indexname -> sort option) ->
    (indexname -> typ option) * (indexname -> sort option) -> string list ->
    (indexname * string) list -> (ctyp * ctyp) list * (cterm * cterm) list
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val strip_shyps_warning: thm -> thm
  val forall_intr_list: cterm list -> thm -> thm
  val forall_intr_frees: thm -> thm
  val forall_intr_vars: thm -> thm
  val forall_elim_list: cterm list -> thm -> thm
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val gen_all: thm -> thm
  val lift_all: cterm -> thm -> thm
  val freeze_thaw: thm -> thm * (thm -> thm)
  val freeze_thaw_robust: thm -> thm * (int -> thm -> thm)
  val implies_elim_list: thm -> thm list -> thm
  val implies_intr_list: cterm list -> thm -> thm
  val instantiate: (ctyp * ctyp) list * (cterm * cterm) list -> thm -> thm
  val zero_var_indexes: thm -> thm
  val implies_intr_hyps: thm -> thm
  val standard: thm -> thm
  val standard': thm -> thm
  val rotate_prems: int -> thm -> thm
  val rearrange_prems: int list -> thm -> thm
  val assume_ax: theory -> string -> thm
  val RSN: thm * (int * thm) -> thm
  val RS: thm * thm -> thm
  val RLN: thm list * (int * thm list) -> thm list
  val RL: thm list * thm list -> thm list
  val MRS: thm list * thm -> thm
  val MRL: thm list list * thm list -> thm list
  val OF: thm * thm list -> thm
  val compose: thm * int * thm -> thm list
  val COMP: thm * thm -> thm
  val read_instantiate_sg: theory -> (string*string)list -> thm -> thm
  val read_instantiate: (string*string)list -> thm -> thm
  val cterm_instantiate: (cterm*cterm)list -> thm -> thm
  val eq_thm_thy: thm * thm -> bool
  val eq_thm_prop: thm * thm -> bool
  val weak_eq_thm: thm * thm -> bool
  val size_of_thm: thm -> int
  val reflexive_thm: thm
  val symmetric_thm: thm
  val transitive_thm: thm
  val symmetric_fun: thm -> thm
  val extensional: thm -> thm
  val equals_cong: thm
  val imp_cong: thm
  val swap_prems_eq: thm
  val equal_abs_elim: cterm  -> thm -> thm
  val equal_abs_elim_list: cterm list -> thm -> thm
  val asm_rl: thm
  val cut_rl: thm
  val revcut_rl: thm
  val thin_rl: thm
  val triv_forall_equality: thm
  val swap_prems_rl: thm
  val equal_intr_rule: thm
  val equal_elim_rule1: thm
  val inst: string -> string -> thm -> thm
  val instantiate': ctyp option list -> cterm option list -> thm -> thm
  val incr_indexes: thm -> thm -> thm
  val incr_indexes_wrt: int list -> ctyp list -> cterm list -> thm list -> thm -> thm
end;

signature DRULE =
sig
  include BASIC_DRULE
  val list_comb: cterm * cterm list -> cterm
  val strip_comb: cterm -> cterm * cterm list
  val strip_type: ctyp -> ctyp list * ctyp
  val beta_conv: cterm -> cterm -> cterm
  val plain_prop_of: thm -> term
  val add_used: thm -> string list -> string list
  val flexflex_unique: thm -> thm
  val close_derivation: thm -> thm
  val local_standard: thm -> thm
  val compose_single: thm * int * thm -> thm
  val add_rule: thm -> thm list -> thm list
  val del_rule: thm -> thm list -> thm list
  val add_rules: thm list -> thm list -> thm list
  val del_rules: thm list -> thm list -> thm list
  val merge_rules: thm list * thm list -> thm list
  val imp_cong_rule: thm -> thm -> thm
  val beta_eta_conversion: cterm -> thm
  val eta_long_conversion: cterm -> thm
  val forall_conv: int -> (cterm -> thm) -> cterm -> thm
  val concl_conv: int -> (cterm -> thm) -> cterm -> thm
  val prems_conv: int -> (int -> cterm -> thm) -> cterm -> thm
  val conjunction_conv: int -> (int -> cterm -> thm) -> cterm -> thm
  val goals_conv: (int -> bool) -> (cterm -> thm) -> cterm -> thm
  val fconv_rule: (cterm -> thm) -> thm -> thm
  val norm_hhf_eq: thm
  val is_norm_hhf: term -> bool
  val norm_hhf: theory -> term -> term
  val protect: cterm -> cterm
  val protectI: thm
  val protectD: thm
  val protect_cong: thm
  val implies_intr_protected: cterm list -> thm -> thm
  val freeze_all: thm -> thm
  val tvars_of_terms: term list -> (indexname * sort) list
  val vars_of_terms: term list -> (indexname * typ) list
  val tvars_of: thm -> (indexname * sort) list
  val vars_of: thm -> (indexname * typ) list
  val tfrees_of: thm -> (string * sort) list
  val frees_of: thm -> (string * typ) list
  val fold_terms: (term -> 'a -> 'a) -> thm -> 'a -> 'a
  val rename_bvars: (string * string) list -> thm -> thm
  val rename_bvars': string option list -> thm -> thm
  val unvarifyT: thm -> thm
  val unvarify: thm -> thm
  val tvars_intr_list: string list -> thm -> (string * (indexname * sort)) list * thm
  val remdups_rl: thm
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val conj_intr: thm -> thm -> thm
  val conj_intr_list: thm list -> thm
  val conj_elim: thm -> thm * thm
  val conj_elim_list: thm -> thm list
  val conj_elim_precise: int list -> thm -> thm list list
  val conj_intr_thm: thm
  val conj_curry: thm -> thm
  val abs_def: thm -> thm
  val read_instantiate_sg': theory -> (indexname * string) list -> thm -> thm
  val read_instantiate': (indexname * string) list -> thm -> thm
end;

structure Drule: DRULE =
struct


(** some cterm->cterm operations: faster than calling cterm_of! **)

fun dest_implies ct =
  (case Thm.term_of ct of
    (Const ("==>", _) $ _ $ _) =>
      let val (ct1, ct2) = Thm.dest_comb ct
      in (#2 (Thm.dest_comb ct1), ct2) end
  | _ => raise TERM ("dest_implies", [term_of ct]));

fun dest_equals ct =
  (case Thm.term_of ct of
    (Const ("==", _) $ _ $ _) =>
      let val (ct1, ct2) = Thm.dest_comb ct
      in (#2 (Thm.dest_comb ct1), ct2) end
    | _ => raise TERM ("dest_equals", [term_of ct]));


(* A1==>...An==>B  goes to  [A1,...,An], where B is not an implication *)
fun strip_imp_prems ct =
    let val (cA,cB) = dest_implies ct
    in  cA :: strip_imp_prems cB  end
    handle TERM _ => [];

(* A1==>...An==>B  goes to B, where B is not an implication *)
fun strip_imp_concl ct =
    case term_of ct of (Const("==>", _) $ _ $ _) =>
        strip_imp_concl (#2 (Thm.dest_comb ct))
  | _ => ct;

(*The premises of a theorem, as a cterm list*)
val cprems_of = strip_imp_prems o cprop_of;

fun cterm_fun f ct =
  let val {t, thy, ...} = Thm.rep_cterm ct
  in Thm.cterm_of thy (f t) end;

fun ctyp_fun f cT =
  let val {T, thy, ...} = Thm.rep_ctyp cT
  in Thm.ctyp_of thy (f T) end;

val implies = cterm_of ProtoPure.thy Term.implies;

(*cterm version of mk_implies*)
fun mk_implies(A,B) = Thm.capply (Thm.capply implies A) B;

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
    #2 (Thm.dest_comb (cprop_of (Thm.beta_conversion false (Thm.capply x y))));

fun plain_prop_of raw_thm =
  let
    val thm = Thm.strip_shyps raw_thm;
    fun err msg = raise THM ("plain_prop_of: " ^ msg, 0, [thm]);
    val {hyps, prop, tpairs, ...} = Thm.rep_thm thm;
  in
    if not (null hyps) then
      err "theorem may not contain hypotheses"
    else if not (null (Thm.extra_shyps thm)) then
      err "theorem may not contain sort hypotheses"
    else if not (null tpairs) then
      err "theorem may not contain flex-flex pairs"
    else prop
  end;



(** reading of instantiations **)

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

fun read_insts thy (rtypes,rsorts) (types,sorts) used insts =
let
    fun is_tv ((a, _), _) =
      (case Symbol.explode a of "'" :: _ => true | _ => false);
    val (tvs, vs) = List.partition is_tv insts;
    fun sort_of ixn = case rsorts ixn of SOME S => S | NONE => absent ixn;
    fun readT (ixn, st) =
        let val S = sort_of ixn;
            val T = Sign.read_typ (thy,sorts) st;
        in if Sign.typ_instance thy (T, TVar(ixn,S)) then (ixn,T)
           else inst_failure ixn
        end
    val tye = map readT tvs;
    fun mkty(ixn,st) = (case rtypes ixn of
                          SOME T => (ixn,(st,typ_subst_TVars tye T))
                        | NONE => absent ixn);
    val ixnsTs = map mkty vs;
    val ixns = map fst ixnsTs
    and sTs  = map snd ixnsTs
    val (cts,tye2) = read_def_cterms(thy,types,sorts) used false sTs;
    fun mkcVar(ixn,T) =
        let val U = typ_subst_TVars tye2 T
        in cterm_of thy (Var(ixn,U)) end
    val ixnTs = ListPair.zip(ixns, map snd sTs)
in (map (fn (ixn, T) => (ctyp_of thy (TVar (ixn, sort_of ixn)),
      ctyp_of thy T)) (tye2 @ tye),
    ListPair.zip(map mkcVar ixnTs,cts))
end;


(*** Find the type (sort) associated with a (T)Var or (T)Free in a term
     Used for establishing default types (of variables) and sorts (of
     type variables) when reading another term.
     Index -1 indicates that a (T)Free rather than a (T)Var is wanted.
***)

fun types_sorts thm =
    let val {prop, hyps, tpairs, ...} = Thm.rep_thm thm;
        (* bogus term! *)
        val big = Term.list_comb
                    (Term.list_comb (prop, hyps), Thm.terms_of_tpairs tpairs);
        val vars = map dest_Var (term_vars big);
        val frees = map dest_Free (term_frees big);
        val tvars = term_tvars big;
        val tfrees = term_tfrees big;
        fun typ(a,i) = if i<0 then AList.lookup (op =) frees a else AList.lookup (op =) vars (a,i);
        fun sort(a,i) = if i<0 then AList.lookup (op =) tfrees a else AList.lookup (op =) tvars (a,i);
    in (typ,sort) end;

fun add_used thm used =
  let val {prop, hyps, tpairs, ...} = Thm.rep_thm thm in
    add_term_tvarnames (prop, used)
    |> fold (curry add_term_tvarnames) hyps
    |> fold (curry add_term_tvarnames) (Thm.terms_of_tpairs tpairs)
  end;



(** Standardization of rules **)

(*vars in left-to-right order*)
fun tvars_of_terms ts = rev (fold Term.add_tvars ts []);
fun vars_of_terms ts = rev (fold Term.add_vars ts []);
fun tvars_of thm = tvars_of_terms [Thm.full_prop_of thm];
fun vars_of thm = vars_of_terms [Thm.full_prop_of thm];

fun fold_terms f th =
  let val {hyps, tpairs, prop, ...} = Thm.rep_thm th
  in f prop #> fold (fn (t, u) => f t #> f u) tpairs #> fold f hyps end;

fun tfrees_of th = rev (fold_terms Term.add_tfrees th []);
fun frees_of th = rev (fold_terms Term.add_frees th []);

(*Strip extraneous shyps as far as possible*)
fun strip_shyps_warning thm =
  let
    val str_of_sort = Pretty.str_of o Sign.pretty_sort (Thm.theory_of_thm thm);
    val thm' = Thm.strip_shyps thm;
    val xshyps = Thm.extra_shyps thm';
  in
    if null xshyps then ()
    else warning ("Pending sort hypotheses: " ^ commas (map str_of_sort xshyps));
    thm'
  end;

(*Generalization over a list of variables, IGNORING bad ones*)
fun forall_intr_list [] th = th
  | forall_intr_list (y::ys) th =
        let val gth = forall_intr_list ys th
        in  forall_intr y gth   handle THM _ =>  gth  end;

(*Generalization over all suitable Free variables*)
fun forall_intr_frees th =
    let val {prop,thy,...} = rep_thm th
    in  forall_intr_list
         (map (cterm_of thy) (sort Term.term_ord (term_frees prop)))
         th
    end;

(*Generalization over Vars -- canonical order*)
fun forall_intr_vars th =
  let val cert = Thm.cterm_of (Thm.theory_of_thm th)
  in forall_intr_list (map (cert o Var) (vars_of th)) th end;

val forall_elim_var = PureThy.forall_elim_var;
val forall_elim_vars = PureThy.forall_elim_vars;

fun outer_params t =
  let
    val vs = Term.strip_all_vars t;
    val xs = Term.variantlist (map (perhaps (try Syntax.dest_skolem) o #1) vs, []);
  in xs ~~ map #2 vs end;

(*generalize outermost parameters*)
fun gen_all th =
  let
    val {thy, prop, maxidx, ...} = Thm.rep_thm th;
    val cert = Thm.cterm_of thy;
    fun elim (x, T) = Thm.forall_elim (cert (Var ((x, maxidx + 1), T)));
  in fold elim (outer_params prop) th end;

(*lift vars wrt. outermost goal parameters
  -- reverses the effect of gen_all modulo higher-order unification*)
fun lift_all goal th =
  let
    val thy = Theory.merge (Thm.theory_of_cterm goal, Thm.theory_of_thm th);
    val cert = Thm.cterm_of thy;
    val {maxidx, ...} = Thm.rep_thm th;
    val ps = outer_params (Thm.term_of goal)
      |> map (fn (x, T) => Var ((x, maxidx + 1), Logic.incr_tvar (maxidx + 1) T));
    val Ts = map Term.fastype_of ps;
    val inst = vars_of th |> map (fn (xi, T) =>
      (cert (Var (xi, T)), cert (Term.list_comb (Var (xi, Ts ---> T), ps))));
  in
    th |> Thm.instantiate ([], inst)
    |> fold_rev (Thm.forall_intr o cert) ps
  end;


(*specialization over a list of cterms*)
val forall_elim_list = fold forall_elim;

(*maps A1,...,An |- B  to  [| A1;...;An |] ==> B*)
val implies_intr_list = fold_rev implies_intr;

(*maps [| A1;...;An |] ==> B and [A1,...,An]  to  B*)
fun implies_elim_list impth ths = Library.foldl (uncurry implies_elim) (impth,ths);

(*Reset Var indexes to zero, renaming to preserve distinctness*)
fun zero_var_indexes th =
  let
    val thy = Thm.theory_of_thm th;
    val certT = Thm.ctyp_of thy and cert = Thm.cterm_of thy;
    val (instT, inst) = Term.zero_var_indexes_inst (Thm.full_prop_of th);
    val cinstT = map (fn (v, T) => (certT (TVar v), certT T)) instT;
    val cinst = map (fn (v, t) => (cert (Var v), cert t)) inst;
  in Thm.adjust_maxidx_thm (Thm.instantiate (cinstT, cinst) th) end;


(** Standard form of object-rule: no hypotheses, flexflex constraints,
    Frees, or outer quantifiers; all generality expressed by Vars of index 0.**)

(*Discharge all hypotheses.*)
fun implies_intr_hyps th =
  fold Thm.implies_intr (#hyps (Thm.crep_thm th)) th;

(*Squash a theorem's flexflex constraints provided it can be done uniquely.
  This step can lose information.*)
fun flexflex_unique th =
  if null (tpairs_of th) then th else
    case Seq.chop (2, flexflex_rule th) of
      ([th],_) => th
    | ([],_)   => raise THM("flexflex_unique: impossible constraints", 0, [th])
    |      _   => raise THM("flexflex_unique: multiple unifiers", 0, [th]);

fun close_derivation thm =
  if Thm.get_name_tags thm = ("", []) then Thm.name_thm ("", thm)
  else thm;

val standard' =
  implies_intr_hyps
  #> forall_intr_frees
  #> `(#maxidx o Thm.rep_thm)
  #-> (fn maxidx =>
    forall_elim_vars (maxidx + 1)
    #> strip_shyps_warning
    #> zero_var_indexes
    #> Thm.varifyT
    #> Thm.compress);

val standard =
  flexflex_unique
  #> standard'
  #> close_derivation;

val local_standard =
  strip_shyps
  #> zero_var_indexes
  #> Thm.compress
  #> close_derivation;


(*Convert all Vars in a theorem to Frees.  Also return a function for
  reversing that operation.  DOES NOT WORK FOR TYPE VARIABLES.
  Similar code in type/freeze_thaw*)

fun freeze_thaw_robust th =
 let val fth = freezeT th
     val {prop, tpairs, thy, ...} = rep_thm fth
 in
   case foldr add_term_vars [] (prop :: Thm.terms_of_tpairs tpairs) of
       [] => (fth, fn i => fn x => x)   (*No vars: nothing to do!*)
     | vars =>
         let fun newName (Var(ix,_), pairs) =
                   let val v = gensym (string_of_indexname ix)
                   in  ((ix,v)::pairs)  end;
             val alist = foldr newName [] vars
             fun mk_inst (Var(v,T)) =
                 (cterm_of thy (Var(v,T)),
                  cterm_of thy (Free(((the o AList.lookup (op =) alist) v), T)))
             val insts = map mk_inst vars
             fun thaw i th' = (*i is non-negative increment for Var indexes*)
                 th' |> forall_intr_list (map #2 insts)
                     |> forall_elim_list (map (Thm.cterm_incr_indexes i o #1) insts)
         in  (Thm.instantiate ([],insts) fth, thaw)  end
 end;

(*Basic version of the function above. No option to rename Vars apart in thaw.
  The Frees created from Vars have nice names.*)
fun freeze_thaw th =
 let val fth = freezeT th
     val {prop, tpairs, thy, ...} = rep_thm fth
 in
   case foldr add_term_vars [] (prop :: Thm.terms_of_tpairs tpairs) of
       [] => (fth, fn x => x)
     | vars =>
         let fun newName (Var(ix,_), (pairs,used)) =
                   let val v = variant used (string_of_indexname ix)
                   in  ((ix,v)::pairs, v::used)  end;
             val (alist, _) = foldr newName ([], Library.foldr add_term_names
               (prop :: Thm.terms_of_tpairs tpairs, [])) vars
             fun mk_inst (Var(v,T)) =
                 (cterm_of thy (Var(v,T)),
                  cterm_of thy (Free(((the o AList.lookup (op =) alist) v), T)))
             val insts = map mk_inst vars
             fun thaw th' =
                 th' |> forall_intr_list (map #2 insts)
                     |> forall_elim_list (map #1 insts)
         in  (Thm.instantiate ([],insts) fth, thaw)  end
 end;

(*Rotates a rule's premises to the left by k*)
val rotate_prems = permute_prems 0;

(* permute prems, where the i-th position in the argument list (counting from 0)
   gives the position within the original thm to be transferred to position i.
   Any remaining trailing positions are left unchanged. *)
val rearrange_prems = let
  fun rearr new []      thm = thm
  |   rearr new (p::ps) thm = rearr (new+1)
     (map (fn q => if new<=q andalso q<p then q+1 else q) ps)
     (permute_prems (new+1) (new-p) (permute_prems new (p-new) thm))
  in rearr 0 end;

(*Assume a new formula, read following the same conventions as axioms.
  Generalizes over Free variables,
  creates the assumption, and then strips quantifiers.
  Example is [| ALL x:?A. ?P(x) |] ==> [| ?P(?a) |]
             [ !(A,P,a)[| ALL x:A. P(x) |] ==> [| P(a) |] ]    *)
fun assume_ax thy sP =
  let val prop = Logic.close_form (term_of (read_cterm thy (sP, propT)))
  in forall_elim_vars 0 (Thm.assume (cterm_of thy prop)) end;

(*Resolution: exactly one resolvent must be produced.*)
fun tha RSN (i,thb) =
  case Seq.chop (2, biresolution false [(false,tha)] i thb) of
      ([th],_) => th
    | ([],_)   => raise THM("RSN: no unifiers", i, [tha,thb])
    |      _   => raise THM("RSN: multiple unifiers", i, [tha,thb]);

(*resolution: P==>Q, Q==>R gives P==>R. *)
fun tha RS thb = tha RSN (1,thb);

(*For joining lists of rules*)
fun thas RLN (i,thbs) =
  let val resolve = biresolution false (map (pair false) thas) i
      fun resb thb = Seq.list_of (resolve thb) handle THM _ => []
  in  List.concat (map resb thbs)  end;

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
    Seq.list_of (bicompose false (false,tha,0) i thb);

fun compose_single (tha,i,thb) =
  (case compose (tha,i,thb) of
    [th] => th
  | _ => raise THM ("compose: unique result expected", i, [tha,thb]));

(*compose Q and [Q1,Q2,...,Qk]==>R to [Q2,...,Qk]==>R getting unique result*)
fun tha COMP thb =
    case compose(tha,1,thb) of
        [th] => th
      | _ =>   raise THM("COMP", 1, [tha,thb]);


(** theorem equality **)

(*True if the two theorems have the same theory.*)
val eq_thm_thy = eq_thy o pairself Thm.theory_of_thm;

(*True if the two theorems have the same prop field, ignoring hyps, der, etc.*)
val eq_thm_prop = op aconv o pairself Thm.full_prop_of;

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o Thm.full_prop_of;

(*maintain lists of theorems --- preserving canonical order*)
fun del_rules rs rules = Library.gen_rems eq_thm_prop (rules, rs);
fun add_rules rs rules = rs @ del_rules rs rules;
val del_rule = del_rules o single;
val add_rule = add_rules o single;
fun merge_rules (rules1, rules2) = gen_merge_lists' eq_thm_prop rules1 rules2;

(*weak_eq_thm: ignores variable renaming and (some) type variable renaming*)
val weak_eq_thm = Thm.eq_thm o pairself (forall_intr_vars o freezeT);


(*** Meta-Rewriting Rules ***)

fun read_prop s = read_cterm ProtoPure.thy (s, propT);

fun store_thm name thm = hd (PureThy.smart_store_thms (name, [thm]));
fun store_standard_thm name thm = store_thm name (standard thm);
fun store_thm_open name thm = hd (PureThy.smart_store_thms_open (name, [thm]));
fun store_standard_thm_open name thm = store_thm_open name (standard' thm);

val reflexive_thm =
  let val cx = cterm_of ProtoPure.thy (Var(("x",0),TVar(("'a",0),[])))
  in store_standard_thm_open "reflexive" (Thm.reflexive cx) end;

val symmetric_thm =
  let val xy = read_prop "x == y"
  in store_standard_thm_open "symmetric" (Thm.implies_intr xy (Thm.symmetric (Thm.assume xy))) end;

val transitive_thm =
  let val xy = read_prop "x == y"
      val yz = read_prop "y == z"
      val xythm = Thm.assume xy and yzthm = Thm.assume yz
  in store_standard_thm_open "transitive" (Thm.implies_intr yz (Thm.transitive xythm yzthm)) end;

fun symmetric_fun thm = thm RS symmetric_thm;

fun extensional eq =
  let val eq' =
    abstract_rule "x" (snd (Thm.dest_comb (fst (dest_equals (cprop_of eq))))) eq
  in equal_elim (eta_conversion (cprop_of eq')) eq' end;

val equals_cong =
  store_standard_thm_open "equals_cong" (Thm.reflexive (read_prop "x == y"));

val imp_cong =
  let
    val ABC = read_prop "PROP A ==> PROP B == PROP C"
    val AB = read_prop "PROP A ==> PROP B"
    val AC = read_prop "PROP A ==> PROP C"
    val A = read_prop "PROP A"
  in
    store_standard_thm_open "imp_cong" (implies_intr ABC (equal_intr
      (implies_intr AB (implies_intr A
        (equal_elim (implies_elim (assume ABC) (assume A))
          (implies_elim (assume AB) (assume A)))))
      (implies_intr AC (implies_intr A
        (equal_elim (symmetric (implies_elim (assume ABC) (assume A)))
          (implies_elim (assume AC) (assume A)))))))
  end;

val swap_prems_eq =
  let
    val ABC = read_prop "PROP A ==> PROP B ==> PROP C"
    val BAC = read_prop "PROP B ==> PROP A ==> PROP C"
    val A = read_prop "PROP A"
    val B = read_prop "PROP B"
  in
    store_standard_thm_open "swap_prems_eq" (equal_intr
      (implies_intr ABC (implies_intr B (implies_intr A
        (implies_elim (implies_elim (assume ABC) (assume A)) (assume B)))))
      (implies_intr BAC (implies_intr A (implies_intr B
        (implies_elim (implies_elim (assume BAC) (assume B)) (assume A))))))
  end;

val imp_cong_rule = combination o combination (reflexive implies);

local
  val dest_eq = dest_equals o cprop_of
  val rhs_of = snd o dest_eq
in
fun beta_eta_conversion t =
  let val thm = beta_conversion true t
  in transitive thm (eta_conversion (rhs_of thm)) end
end;

fun eta_long_conversion ct = transitive (beta_eta_conversion ct)
  (symmetric (beta_eta_conversion (cterm_fun (Pattern.eta_long []) ct)));

val abs_def =
  let
    fun contract_lhs th =
      Thm.transitive (Thm.symmetric (beta_eta_conversion (fst (dest_equals (cprop_of th))))) th;
    fun abstract cx th = Thm.abstract_rule
        (case Thm.term_of cx of Var ((x, _), _) => x | Free (x, _) => x | _ => "x") cx th
      handle THM _ => raise THM ("Malformed definitional equation", 0, [th]);
  in
    contract_lhs
    #> `(snd o strip_comb o fst o dest_equals o cprop_of)
    #-> fold_rev abstract
    #> contract_lhs
  end;

(*rewrite B in !!x1 ... xn. B*)
fun forall_conv 0 cv ct = cv ct
  | forall_conv n cv ct =
      (case try Thm.dest_comb ct of
        NONE => cv ct
      | SOME (A, B) =>
          (case (term_of A, term_of B) of
            (Const ("all", _), Abs (x, _, _)) =>
              let val (v, B') = Thm.dest_abs (SOME (gensym "all_")) B in
                Thm.combination (Thm.reflexive A)
                  (Thm.abstract_rule x v (forall_conv (n - 1) cv B'))
              end
          | _ => cv ct));

(*rewrite B in A1 ==> ... ==> An ==> B*)
fun concl_conv 0 cv ct = cv ct
  | concl_conv n cv ct =
      (case try dest_implies ct of
        NONE => cv ct
      | SOME (A, B) => imp_cong_rule (reflexive A) (concl_conv (n - 1) cv B));

(*rewrite the A's in A1 ==> ... ==> An ==> B*)
fun prems_conv 0 _ = reflexive
  | prems_conv n cv =
      let
        fun conv i ct =
          if i = n + 1 then reflexive ct
          else
            (case try dest_implies ct of
              NONE => reflexive ct
            | SOME (A, B) => imp_cong_rule (cv i A) (conv (i + 1) B));
  in conv 1 end;

(*rewrite the A's in A1 && ... && An*)
fun conjunction_conv 0 _ = reflexive
  | conjunction_conv n cv =
      let
        fun conv i ct =
          if i <> n andalso can Logic.dest_conjunction (term_of ct) then
            forall_conv 1
              (prems_conv 1 (K (prems_conv 2 (fn 1 => cv i | 2 => conv (i + 1))))) ct
          else cv i ct;
      in conv 1 end;


fun goals_conv pred cv = prems_conv ~1 (fn i => if pred i then cv else reflexive);
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;


(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl = store_standard_thm_open "asm_rl" (Thm.trivial (read_prop "PROP ?psi"));
val _ = store_thm "_" asm_rl;

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl =
  store_standard_thm_open "cut_rl"
    (Thm.trivial (read_prop "PROP ?psi ==> PROP ?theta"));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let val V = read_prop "PROP V"
      and VW = read_prop "PROP V ==> PROP W";
  in
    store_standard_thm_open "revcut_rl"
      (implies_intr V (implies_intr VW (implies_elim (assume VW) (assume V))))
  end;

(*for deleting an unwanted assumption*)
val thin_rl =
  let val V = read_prop "PROP V"
      and W = read_prop "PROP W";
  in store_standard_thm_open "thin_rl" (implies_intr V (implies_intr W (assume W))) end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let val V  = read_prop "PROP V"
      and QV = read_prop "!!x::'a. PROP V"
      and x  = read_cterm ProtoPure.thy ("x", TypeInfer.logicT);
  in
    store_standard_thm_open "triv_forall_equality"
      (equal_intr (implies_intr QV (forall_elim x (assume QV)))
        (implies_intr V  (forall_intr x (assume V))))
  end;

(* (PROP ?PhiA ==> PROP ?PhiB ==> PROP ?Psi) ==>
   (PROP ?PhiB ==> PROP ?PhiA ==> PROP ?Psi)
   `thm COMP swap_prems_rl' swaps the first two premises of `thm'
*)
val swap_prems_rl =
  let val cmajor = read_prop "PROP PhiA ==> PROP PhiB ==> PROP Psi";
      val major = assume cmajor;
      val cminor1 = read_prop "PROP PhiA";
      val minor1 = assume cminor1;
      val cminor2 = read_prop "PROP PhiB";
      val minor2 = assume cminor2;
  in store_standard_thm_open "swap_prems_rl"
       (implies_intr cmajor (implies_intr cminor2 (implies_intr cminor1
         (implies_elim (implies_elim major minor1) minor2))))
  end;

(* [| PROP ?phi ==> PROP ?psi; PROP ?psi ==> PROP ?phi |]
   ==> PROP ?phi == PROP ?psi
   Introduction rule for == as a meta-theorem.
*)
val equal_intr_rule =
  let val PQ = read_prop "PROP phi ==> PROP psi"
      and QP = read_prop "PROP psi ==> PROP phi"
  in
    store_standard_thm_open "equal_intr_rule"
      (implies_intr PQ (implies_intr QP (equal_intr (assume PQ) (assume QP))))
  end;

(* [| PROP ?phi == PROP ?psi; PROP ?phi |] ==> PROP ?psi *)
val equal_elim_rule1 =
  let val eq = read_prop "PROP phi == PROP psi"
      and P = read_prop "PROP phi"
  in store_standard_thm_open "equal_elim_rule1"
    (Thm.equal_elim (assume eq) (assume P) |> implies_intr_list [eq, P])
  end;

(* "[| PROP ?phi; PROP ?phi; PROP ?psi |] ==> PROP ?psi" *)

val remdups_rl =
  let val P = read_prop "PROP phi" and Q = read_prop "PROP psi";
  in store_standard_thm_open "remdups_rl" (implies_intr_list [P, P, Q] (Thm.assume Q)) end;


(*(PROP ?phi ==> (!!x. PROP ?psi(x))) == (!!x. PROP ?phi ==> PROP ?psi(x))
  Rewrite rule for HHF normalization.*)

val norm_hhf_eq =
  let
    val cert = Thm.cterm_of ProtoPure.thy;
    val aT = TFree ("'a", []);
    val all = Term.all aT;
    val x = Free ("x", aT);
    val phi = Free ("phi", propT);
    val psi = Free ("psi", aT --> propT);

    val cx = cert x;
    val cphi = cert phi;
    val lhs = cert (Logic.mk_implies (phi, all $ Abs ("x", aT, psi $ Bound 0)));
    val rhs = cert (all $ Abs ("x", aT, Logic.mk_implies (phi, psi $ Bound 0)));
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
    |> store_standard_thm_open "norm_hhf_eq"
  end;

val norm_hhf_prop = Logic.dest_equals (Thm.prop_of norm_hhf_eq);

fun is_norm_hhf tm =
  let
    fun is_norm (Const ("==>", _) $ _ $ (Const ("all", _) $ _)) = false
      | is_norm (t $ u) = is_norm t andalso is_norm u
      | is_norm (Abs (_, _, t)) = is_norm t
      | is_norm _ = true;
  in is_norm (Pattern.beta_eta_contract tm) end;

fun norm_hhf thy t =
  if is_norm_hhf t then t
  else Pattern.rewrite_term thy [norm_hhf_prop] [] t;



(*** Instantiate theorem th, reading instantiations in theory thy ****)

(*Version that normalizes the result: Thm.instantiate no longer does that*)
fun instantiate instpair th = Thm.instantiate instpair th  COMP   asm_rl;

fun read_instantiate_sg' thy sinsts th =
    let val ts = types_sorts th;
        val used = add_used th [];
    in  instantiate (read_insts thy ts ts used sinsts) th  end;

fun read_instantiate_sg thy sinsts th =
  read_instantiate_sg' thy (map (apfst Syntax.indexname) sinsts) th;

(*Instantiate theorem th, reading instantiations under theory of th*)
fun read_instantiate sinsts th =
    read_instantiate_sg (Thm.theory_of_thm th) sinsts th;

fun read_instantiate' sinsts th =
    read_instantiate_sg' (Thm.theory_of_thm th) sinsts th;


(*Left-to-right replacements: tpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms, inferring type instantiations. *)
local
  fun add_types ((ct,cu), (thy,tye,maxidx)) =
    let val {thy=thyt, t=t, T= T, maxidx=maxt,...} = rep_cterm ct
        and {thy=thyu, t=u, T= U, maxidx=maxu,...} = rep_cterm cu;
        val maxi = Int.max(maxidx, Int.max(maxt, maxu));
        val thy' = Theory.merge(thy, Theory.merge(thyt, thyu))
        val (tye',maxi') = Sign.typ_unify thy' (T, U) (tye, maxi)
          handle Type.TUNIFY => raise TYPE("Ill-typed instantiation", [T,U], [t,u])
    in  (thy', tye', maxi')  end;
in
fun cterm_instantiate ctpairs0 th =
  let val (thy,tye,_) = foldr add_types (Thm.theory_of_thm th, Vartab.empty, 0) ctpairs0
      fun instT(ct,cu) =
        let val inst = cterm_of thy o Envir.subst_TVars tye o term_of
        in (inst ct, inst cu) end
      fun ctyp2 (ixn, (S, T)) = (ctyp_of thy (TVar (ixn, S)), ctyp_of thy T)
  in  instantiate (map ctyp2 (Vartab.dest tye), map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible theories",0,[th])
       | TYPE (msg, _, _) => raise THM(msg, 0, [th])
end;


(** Derived rules mainly for METAHYPS **)

(*Given the term "a", takes (%x.t)==(%x.u) to t[a/x]==u[a/x]*)
fun equal_abs_elim ca eqth =
  let val {thy=thya, t=a, ...} = rep_cterm ca
      and combth = combination eqth (reflexive ca)
      val {thy,prop,...} = rep_thm eqth
      val (abst,absu) = Logic.dest_equals prop
      val cterm = cterm_of (Theory.merge (thy,thya))
  in  transitive (symmetric (beta_conversion false (cterm (abst$a))))
           (transitive combth (beta_conversion false (cterm (absu$a))))
  end
  handle THM _ => raise THM("equal_abs_elim", 0, [eqth]);

(*Calling equal_abs_elim with multiple terms*)
fun equal_abs_elim_list cts th = foldr (uncurry equal_abs_elim) th (rev cts);


(** protected propositions **)

local
  val cert = Thm.cterm_of ProtoPure.thy;
  val A = cert (Free ("A", propT));
  val prop_def = #1 (freeze_thaw ProtoPure.prop_def);
in
  val protect = Thm.capply (cert Logic.protectC);
  val protectI = store_thm "protectI" (PureThy.kind_rule PureThy.internalK (standard
      (Thm.equal_elim (Thm.symmetric prop_def) (Thm.assume A))));
  val protectD = store_thm "protectD" (PureThy.kind_rule PureThy.internalK (standard
      (Thm.equal_elim prop_def (Thm.assume (protect A)))));
  val protect_cong = store_standard_thm_open "protect_cong" (Thm.reflexive (protect A));
end;

fun implies_intr_protected asms th =
  let val asms' = map protect asms in
    implies_elim_list
      (implies_intr_list asms th)
      (map (fn asm' => Thm.assume asm' RS protectD) asms')
    |> implies_intr_list asms'
  end;


(** variations on instantiate **)

(*shorthand for instantiating just one variable in the current theory*)
fun inst x t = read_instantiate_sg (the_context()) [(x,t)];


(* instantiate by left-to-right occurrence of variables *)

fun instantiate' cTs cts thm =
  let
    fun err msg =
      raise TYPE ("instantiate': " ^ msg,
        List.mapPartial (Option.map Thm.typ_of) cTs,
        List.mapPartial (Option.map Thm.term_of) cts);

    fun inst_of (v, ct) =
      (Thm.cterm_of (Thm.theory_of_cterm ct) (Var v), ct)
        handle TYPE (msg, _, _) => err msg;

    fun tyinst_of (v, cT) =
      (Thm.ctyp_of (Thm.theory_of_ctyp cT) (TVar v), cT)
        handle TYPE (msg, _, _) => err msg;

    fun zip_vars _ [] = []
      | zip_vars (_ :: vs) (NONE :: opt_ts) = zip_vars vs opt_ts
      | zip_vars (v :: vs) (SOME t :: opt_ts) = (v, t) :: zip_vars vs opt_ts
      | zip_vars [] _ = err "more instantiations than variables in thm";

    (*instantiate types first!*)
    val thm' =
      if forall is_none cTs then thm
      else Thm.instantiate (map tyinst_of (zip_vars (tvars_of thm) cTs), []) thm;
    in
      if forall is_none cts then thm'
      else Thm.instantiate ([], map inst_of (zip_vars (vars_of thm') cts)) thm'
    end;



(** renaming of bound variables **)

(* replace bound variables x_i in thm by y_i *)
(* where vs = [(x_1, y_1), ..., (x_n, y_n)]  *)

fun rename_bvars [] thm = thm
  | rename_bvars vs thm =
    let
      val {thy, prop, ...} = rep_thm thm;
      fun ren (Abs (x, T, t)) = Abs (AList.lookup (op =) vs x |> the_default x, T, ren t)
        | ren (t $ u) = ren t $ ren u
        | ren t = t;
    in equal_elim (reflexive (cterm_of thy (ren prop))) thm end;


(* renaming in left-to-right order *)

fun rename_bvars' xs thm =
  let
    val {thy, prop, ...} = rep_thm thm;
    fun rename [] t = ([], t)
      | rename (x' :: xs) (Abs (x, T, t)) =
          let val (xs', t') = rename xs t
          in (xs', Abs (getOpt (x',x), T, t')) end
      | rename xs (t $ u) =
          let
            val (xs', t') = rename xs t;
            val (xs'', u') = rename xs' u
          in (xs'', t' $ u') end
      | rename xs t = (xs, t);
  in case rename xs prop of
      ([], prop') => equal_elim (reflexive (cterm_of thy prop')) thm
    | _ => error "More names than abstractions in theorem"
  end;



(* unvarify(T) *)

(*assume thm in standard form, i.e. no frees, 0 var indexes*)

fun unvarifyT thm =
  let
    val cT = Thm.ctyp_of (Thm.theory_of_thm thm);
    val tfrees = map (fn ((x, _), S) => SOME (cT (TFree (x, S)))) (tvars_of thm);
  in instantiate' tfrees [] thm end;

fun unvarify raw_thm =
  let
    val thm = unvarifyT raw_thm;
    val ct = Thm.cterm_of (Thm.theory_of_thm thm);
    val frees = map (fn ((x, _), T) => SOME (ct (Free (x, T)))) (vars_of thm);
  in instantiate' [] frees thm end;


(* tvars_intr_list *)

fun tvars_intr_list tfrees thm =
  apfst (map (fn ((s, S), ixn) => (s, (ixn, S)))) (Thm.varifyT'
    (gen_rems (op = o apfst fst) (tfrees_of thm, tfrees)) thm);


(* increment var indexes *)

fun incr_indexes th = Thm.incr_indexes (#maxidx (Thm.rep_thm th) + 1);

fun incr_indexes_wrt is cTs cts thms =
  let
    val maxidx =
      Library.foldl Int.max (~1, is @
        map (maxidx_of_typ o #T o Thm.rep_ctyp) cTs @
        map (#maxidx o Thm.rep_cterm) cts @
        map (#maxidx o Thm.rep_thm) thms);
  in Thm.incr_indexes (maxidx + 1) end;


(* freeze_all *)

(*freeze all (T)Vars; assumes thm in standard form*)

fun freeze_all_TVars thm =
  (case tvars_of thm of
    [] => thm
  | tvars =>
      let val cert = Thm.ctyp_of (Thm.theory_of_thm thm)
      in instantiate' (map (fn ((x, _), S) => SOME (cert (TFree (x, S)))) tvars) [] thm end);

fun freeze_all_Vars thm =
  (case vars_of thm of
    [] => thm
  | vars =>
      let val cert = Thm.cterm_of (Thm.theory_of_thm thm)
      in instantiate' [] (map (fn ((x, _), T) => SOME (cert (Free (x, T)))) vars) thm end);

val freeze_all = freeze_all_Vars o freeze_all_TVars;



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



(** meta-level conjunction **)

local
  val A = read_prop "PROP A";
  val B = read_prop "PROP B";
  val C = read_prop "PROP C";
  val ABC = read_prop "PROP A ==> PROP B ==> PROP C";

  val proj1 =
    forall_intr_list [A, B] (implies_intr_list [A, B] (Thm.assume A))
    |> forall_elim_vars 0;

  val proj2 =
    forall_intr_list [A, B] (implies_intr_list [A, B] (Thm.assume B))
    |> forall_elim_vars 0;

  val conj_intr_rule =
    forall_intr_list [A, B] (implies_intr_list [A, B]
      (Thm.forall_intr C (Thm.implies_intr ABC
        (implies_elim_list (Thm.assume ABC) [Thm.assume A, Thm.assume B]))))
    |> forall_elim_vars 0;
in

fun conj_intr tha thb = thb COMP (tha COMP incr_indexes_wrt [] [] [] [tha, thb] conj_intr_rule);

fun conj_intr_list [] = asm_rl
  | conj_intr_list ths = foldr1 (uncurry conj_intr) ths;

fun conj_elim th =
  let val th' = forall_elim_var (#maxidx (Thm.rep_thm th) + 1) th
  in (incr_indexes th' proj1 COMP th', incr_indexes th' proj2 COMP th') end;

(*((A && B) && C) && D && E -- flat*)
fun conj_elim_list th =
  let val (th1, th2) = conj_elim th
  in conj_elim_list th1 @ conj_elim_list th2 end handle THM _ => [th];

(*(A1 && B1 && C1) && (A2 && B2 && C2 && D2) && A3 && B3 -- improper*)
fun conj_elim_precise spans =
  let
    fun elim 0 _ = []
      | elim 1 th = [th]
      | elim n th =
          let val (th1, th2) = conj_elim th
          in th1 :: elim (n - 1) th2 end;
    fun elims (0 :: ns) ths = [] :: elims ns ths
      | elims (n :: ns) (th :: ths) = elim n th :: elims ns ths
      | elims _ _ = [];
  in elims spans o elim (length (filter_out (equal 0) spans)) end;

val conj_intr_thm = store_standard_thm_open "conjunctionI"
  (implies_intr_list [A, B] (conj_intr (Thm.assume A) (Thm.assume B)));

end;

fun conj_curry th =
  let
    val {thy, maxidx, ...} = Thm.rep_thm th;
    val n = Thm.nprems_of th;
  in
    if n < 2 then th
    else
      let
        val cert = Thm.cterm_of thy;
        val As = map (fn i => Free ("A" ^ string_of_int i, propT)) (1 upto n);
        val B = Free ("B", propT);
        val C = cert (Logic.mk_conjunction_list As);
        val D = cert (Logic.list_implies (As, B));
        val rule =
          implies_elim_list (Thm.assume D) (conj_elim_list (Thm.assume C))
          |> implies_intr_list [D, C]
          |> forall_intr_frees
          |> forall_elim_vars (maxidx + 1)
      in Thm.adjust_maxidx_thm (th COMP rule) end
  end;

end;

structure BasicDrule: BASIC_DRULE = Drule;
open BasicDrule;
