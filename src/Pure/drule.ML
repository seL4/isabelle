(*  Title:      Pure/drule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Derived rules and other operations on theorems.
*)

infix 0 RS RSN RL RLN MRS MRL OF COMP;

signature BASIC_DRULE =
sig
  val mk_implies        : cterm * cterm -> cterm
  val list_implies      : cterm list * cterm -> cterm
  val dest_implies      : cterm -> cterm * cterm
  val dest_equals       : cterm -> cterm * cterm
  val skip_flexpairs    : cterm -> cterm
  val strip_imp_prems   : cterm -> cterm list
  val strip_imp_concl   : cterm -> cterm
  val cprems_of         : thm -> cterm list
  val read_insts        :
          Sign.sg -> (indexname -> typ option) * (indexname -> sort option)
                  -> (indexname -> typ option) * (indexname -> sort option)
                  -> string list -> (string*string)list
                  -> (indexname*ctyp)list * (cterm*cterm)list
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val strip_shyps_warning : thm -> thm
  val forall_intr_list  : cterm list -> thm -> thm
  val forall_intr_frees : thm -> thm
  val forall_intr_vars  : thm -> thm
  val forall_elim_list  : cterm list -> thm -> thm
  val forall_elim_var   : int -> thm -> thm
  val forall_elim_vars  : int -> thm -> thm
  val forall_elim_vars_safe  : thm -> thm
  val freeze_thaw       : thm -> thm * (thm -> thm)
  val implies_elim_list : thm -> thm list -> thm
  val implies_intr_list : cterm list -> thm -> thm
  val instantiate       :
    (indexname * ctyp) list * (cterm * cterm) list -> thm -> thm
  val zero_var_indexes  : thm -> thm
  val standard          : thm -> thm
  val standard'         : thm -> thm
  val rotate_prems      : int -> thm -> thm
  val rearrange_prems   : int list -> thm -> thm
  val assume_ax         : theory -> string -> thm
  val RSN               : thm * (int * thm) -> thm
  val RS                : thm * thm -> thm
  val RLN               : thm list * (int * thm list) -> thm list
  val RL                : thm list * thm list -> thm list
  val MRS               : thm list * thm -> thm
  val MRL               : thm list list * thm list -> thm list
  val OF                : thm * thm list -> thm
  val compose           : thm * int * thm -> thm list
  val COMP              : thm * thm -> thm
  val read_instantiate_sg: Sign.sg -> (string*string)list -> thm -> thm
  val read_instantiate  : (string*string)list -> thm -> thm
  val cterm_instantiate : (cterm*cterm)list -> thm -> thm
  val weak_eq_thm       : thm * thm -> bool
  val eq_thm_sg         : thm * thm -> bool
  val size_of_thm       : thm -> int
  val reflexive_thm     : thm
  val symmetric_thm     : thm
  val transitive_thm    : thm
  val refl_implies      : thm
  val symmetric_fun     : thm -> thm
  val extensional       : thm -> thm
  val imp_cong          : thm
  val swap_prems_eq     : thm
  val equal_abs_elim    : cterm  -> thm -> thm
  val equal_abs_elim_list: cterm list -> thm -> thm
  val flexpair_abs_elim_list: cterm list -> thm -> thm
  val asm_rl            : thm
  val cut_rl            : thm
  val revcut_rl         : thm
  val thin_rl           : thm
  val triv_forall_equality: thm
  val swap_prems_rl     : thm
  val equal_intr_rule   : thm
  val inst              : string -> string -> thm -> thm
  val instantiate'      : ctyp option list -> cterm option list -> thm -> thm
  val incr_indexes_wrt  : int list -> ctyp list -> cterm list -> thm list -> thm -> thm
end;

signature DRULE =
sig
  include BASIC_DRULE
  val rule_attribute: ('a -> thm -> thm) -> 'a attribute
  val tag_rule: tag -> thm -> thm
  val untag_rule: string -> thm -> thm
  val tag: tag -> 'a attribute
  val untag: string -> 'a attribute
  val get_kind: thm -> string
  val kind: string -> 'a attribute
  val theoremK: string
  val lemmaK: string
  val corollaryK: string
  val internalK: string
  val kind_internal: 'a attribute
  val has_internal: tag list -> bool
  val impose_hyps: cterm list -> thm -> thm
  val close_derivation: thm -> thm
  val local_standard: thm -> thm
  val compose_single: thm * int * thm -> thm
  val add_rules: thm list -> thm list -> thm list
  val del_rules: thm list -> thm list -> thm list
  val merge_rules: thm list * thm list -> thm list
  val norm_hhf_eq: thm
  val triv_goal: thm
  val rev_triv_goal: thm
  val implies_intr_goals: cterm list -> thm -> thm
  val freeze_all: thm -> thm
  val mk_triv_goal: cterm -> thm
  val tvars_of_terms: term list -> (indexname * sort) list
  val vars_of_terms: term list -> (indexname * typ) list
  val tvars_of: thm -> (indexname * sort) list
  val vars_of: thm -> (indexname * typ) list
  val unvarifyT: thm -> thm
  val unvarify: thm -> thm
  val tvars_intr_list: string list -> thm -> thm
  val conj_intr: thm -> thm -> thm
  val conj_intr_list: thm list -> thm
  val conj_elim: thm -> thm * thm
  val conj_elim_list: thm -> thm list
end;

structure Drule: DRULE =
struct


(** some cterm->cterm operations: much faster than calling cterm_of! **)

(** SAME NAMES as in structure Logic: use compound identifiers! **)

(*dest_implies for cterms. Note T=prop below*)
fun dest_implies ct =
    case term_of ct of
        (Const("==>", _) $ _ $ _) =>
            let val (ct1,ct2) = Thm.dest_comb ct
            in  (#2 (Thm.dest_comb ct1), ct2)  end
      | _ => raise TERM ("dest_implies", [term_of ct]) ;

fun dest_equals ct =
    case term_of ct of
        (Const("==", _) $ _ $ _) =>
            let val (ct1,ct2) = Thm.dest_comb ct
            in  (#2 (Thm.dest_comb ct1), ct2)  end
      | _ => raise TERM ("dest_equals", [term_of ct]) ;


(*Discard flexflex pairs; return a cterm*)
fun skip_flexpairs ct =
    case term_of ct of
        (Const("==>", _) $ (Const("=?=",_)$_$_) $ _) =>
            skip_flexpairs (#2 (dest_implies ct))
      | _ => ct;

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
val cprems_of = strip_imp_prems o skip_flexpairs o cprop_of;

val proto_sign = Theory.sign_of ProtoPure.thy;

val implies = cterm_of proto_sign Term.implies;

(*cterm version of mk_implies*)
fun mk_implies(A,B) = Thm.capply (Thm.capply implies A) B;

(*cterm version of list_implies: [A1,...,An], B  goes to [|A1;==>;An|]==>B *)
fun list_implies([], B) = B
  | list_implies(A::AS, B) = mk_implies (A, list_implies(AS,B));


(** reading of instantiations **)

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

fun read_insts sign (rtypes,rsorts) (types,sorts) used insts =
let
    fun split([],tvs,vs) = (tvs,vs)
      | split((sv,st)::l,tvs,vs) = (case Symbol.explode sv of
                  "'"::cs => split(l,(Syntax.indexname cs,st)::tvs,vs)
                | cs => split(l,tvs,(Syntax.indexname cs,st)::vs));
    val (tvs,vs) = split(insts,[],[]);
    fun readT((a,i),st) =
        let val ixn = ("'" ^ a,i);
            val S = case rsorts ixn of Some S => S | None => absent ixn;
            val T = Sign.read_typ (sign,sorts) st;
        in if Sign.typ_instance sign (T, TVar(ixn,S)) then (ixn,T)
           else inst_failure ixn
        end
    val tye = map readT tvs;
    fun mkty(ixn,st) = (case rtypes ixn of
                          Some T => (ixn,(st,typ_subst_TVars tye T))
                        | None => absent ixn);
    val ixnsTs = map mkty vs;
    val ixns = map fst ixnsTs
    and sTs  = map snd ixnsTs
    val (cts,tye2) = read_def_cterms(sign,types,sorts) used false sTs;
    fun mkcVar(ixn,T) =
        let val U = typ_subst_TVars tye2 T
        in cterm_of sign (Var(ixn,U)) end
    val ixnTs = ListPair.zip(ixns, map snd sTs)
in (map (fn (ixn,T) => (ixn,ctyp_of sign T)) (tye2 @ tye),
    ListPair.zip(map mkcVar ixnTs,cts))
end;


(*** Find the type (sort) associated with a (T)Var or (T)Free in a term
     Used for establishing default types (of variables) and sorts (of
     type variables) when reading another term.
     Index -1 indicates that a (T)Free rather than a (T)Var is wanted.
***)

fun types_sorts thm =
    let val {prop,hyps,...} = rep_thm thm;
        val big = list_comb(prop,hyps); (* bogus term! *)
        val vars = map dest_Var (term_vars big);
        val frees = map dest_Free (term_frees big);
        val tvars = term_tvars big;
        val tfrees = term_tfrees big;
        fun typ(a,i) = if i<0 then assoc(frees,a) else assoc(vars,(a,i));
        fun sort(a,i) = if i<0 then assoc(tfrees,a) else assoc(tvars,(a,i));
    in (typ,sort) end;



(** basic attributes **)

(* dependent rules *)

fun rule_attribute f (x, thm) = (x, (f x thm));


(* add / delete tags *)

fun map_tags f thm =
  Thm.put_name_tags (Thm.name_of_thm thm, f (#2 (Thm.get_name_tags thm))) thm;

fun tag_rule tg = map_tags (fn tgs => if tg mem tgs then tgs else tgs @ [tg]);
fun untag_rule s = map_tags (filter_out (equal s o #1));

fun tag tg x = rule_attribute (K (tag_rule tg)) x;
fun untag s x = rule_attribute (K (untag_rule s)) x;

fun simple_tag name x = tag (name, []) x;


(* theorem kinds *)

val theoremK = "theorem";
val lemmaK = "lemma";
val corollaryK = "corollary";
val internalK = "internal";

fun get_kind thm =
  (case Library.assoc (#2 (Thm.get_name_tags thm), "kind") of
    Some (k :: _) => k
  | _ => "unknown");

fun kind_rule k = tag_rule ("kind", [k]) o untag_rule "kind";
fun kind k x = rule_attribute (K (kind_rule k)) x;
fun kind_internal x = kind internalK x;
fun has_internal tags = exists (equal internalK o fst) tags;



(** Standardization of rules **)

(*Strip extraneous shyps as far as possible*)
fun strip_shyps_warning thm =
  let
    val str_of_sort = Sign.str_of_sort (Thm.sign_of_thm thm);
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
    let val {prop,sign,...} = rep_thm th
    in  forall_intr_list
         (map (cterm_of sign) (sort (make_ord atless) (term_frees prop)))
         th
    end;

val forall_elim_var = PureThy.forall_elim_var;
val forall_elim_vars = PureThy.forall_elim_vars;

fun forall_elim_vars_safe th =
  forall_elim_vars_safe (forall_elim_var (#maxidx (Thm.rep_thm th) + 1) th)
    handle THM _ => th;


(*Specialization over a list of cterms*)
fun forall_elim_list cts th = foldr (uncurry forall_elim) (rev cts, th);

(* maps A1,...,An |- B   to   [| A1;...;An |] ==> B  *)
fun implies_intr_list cAs th = foldr (uncurry implies_intr) (cAs,th);

(* maps [| A1;...;An |] ==> B and [A1,...,An]   to   B *)
fun implies_elim_list impth ths = foldl (uncurry implies_elim) (impth,ths);

(* maps |- B to A1,...,An |- B *)
fun impose_hyps chyps th =
  implies_elim_list (implies_intr_list chyps th) (map Thm.assume chyps);

(*Reset Var indexes to zero, renaming to preserve distinctness*)
fun zero_var_indexes th =
    let val {prop,sign,...} = rep_thm th;
        val vars = term_vars prop
        val bs = foldl add_new_id ([], map (fn Var((a,_),_)=>a) vars)
        val inrs = add_term_tvars(prop,[]);
        val nms' = rev(foldl add_new_id ([], map (#1 o #1) inrs));
        val tye = ListPair.map (fn ((v,rs),a) => (v, TVar((a,0),rs)))
                     (inrs, nms')
        val ctye = map (fn (v,T) => (v,ctyp_of sign T)) tye;
        fun varpairs([],[]) = []
          | varpairs((var as Var(v,T)) :: vars, b::bs) =
                let val T' = typ_subst_TVars tye T
                in (cterm_of sign (Var(v,T')),
                    cterm_of sign (Var((b,0),T'))) :: varpairs(vars,bs)
                end
          | varpairs _ = raise TERM("varpairs", []);
    in Thm.instantiate (ctye, varpairs(vars,rev bs)) th end;


(*Standard form of object-rule: no hypotheses, Frees, or outer quantifiers;
    all generality expressed by Vars having index 0.*)

fun close_derivation thm =
  if Thm.get_name_tags thm = ("", []) then Thm.name_thm ("", thm)
  else thm;

fun standard' th =
  let val {maxidx,...} = rep_thm th in
    th
    |> implies_intr_hyps
    |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
    |> strip_shyps_warning
    |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;

val standard = close_derivation o standard';

fun local_standard th =
  th |> strip_shyps_warning |> zero_var_indexes
  |> Thm.compress |> close_derivation;


(*Convert all Vars in a theorem to Frees.  Also return a function for
  reversing that operation.  DOES NOT WORK FOR TYPE VARIABLES.
  Similar code in type/freeze_thaw*)
fun freeze_thaw th =
 let val fth = freezeT th
     val {prop,sign,...} = rep_thm fth
 in
   case term_vars prop of
       [] => (fth, fn x => x)
     | vars =>
         let fun newName (Var(ix,_), (pairs,used)) =
                   let val v = variant used (string_of_indexname ix)
                   in  ((ix,v)::pairs, v::used)  end;
             val (alist, _) = foldr newName
                                (vars, ([], add_term_names (prop, [])))
             fun mk_inst (Var(v,T)) =
                 (cterm_of sign (Var(v,T)),
                  cterm_of sign (Free(the (assoc(alist,v)), T)))
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
    let val sign = Theory.sign_of thy
        val prop = Logic.close_form (term_of (read_cterm sign (sP, propT)))
    in forall_elim_vars 0 (assume (cterm_of sign prop))  end;

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

(*Do the two theorems have the same signature?*)
fun eq_thm_sg (th1,th2) = Sign.eq_sg(#sign(rep_thm th1), #sign(rep_thm th2));

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o #prop o rep_thm;

(*maintain lists of theorems --- preserving canonical order*)
fun del_rules rs rules = Library.gen_rems Thm.eq_thm (rules, rs);
fun add_rules rs rules = rs @ del_rules rs rules;
fun merge_rules (rules1, rules2) = Library.generic_merge Thm.eq_thm I I rules1 rules2;


(** Mark Staples's weaker version of eq_thm: ignores variable renaming and
    (some) type variable renaming **)

 (* Can't use term_vars, because it sorts the resulting list of variable names.
    We instead need the unique list noramlised by the order of appearance
    in the term. *)
fun term_vars' (t as Var(v,T)) = [t]
  | term_vars' (Abs(_,_,b)) = term_vars' b
  | term_vars' (f$a) = (term_vars' f) @ (term_vars' a)
  | term_vars' _ = [];

fun forall_intr_vars th =
  let val {prop,sign,...} = rep_thm th;
      val vars = distinct (term_vars' prop);
  in forall_intr_list (map (cterm_of sign) vars) th end;

fun weak_eq_thm (tha,thb) =
    eq_thm(forall_intr_vars (freezeT tha), forall_intr_vars (freezeT thb));



(*** Meta-Rewriting Rules ***)

fun read_prop s = read_cterm proto_sign (s, propT);

fun store_thm name thm = hd (PureThy.smart_store_thms (name, [thm]));
fun store_standard_thm name thm = store_thm name (standard thm);
fun open_store_thm name thm = hd (PureThy.open_smart_store_thms (name, [thm]));
fun open_store_standard_thm name thm = open_store_thm name (standard' thm);

val reflexive_thm =
  let val cx = cterm_of proto_sign (Var(("x",0),TVar(("'a",0),logicS)))
  in store_standard_thm "reflexive" (Thm.reflexive cx) end;

val symmetric_thm =
  let val xy = read_prop "x::'a::logic == y"
  in store_standard_thm "symmetric" (Thm.implies_intr_hyps (Thm.symmetric (Thm.assume xy))) end;

val transitive_thm =
  let val xy = read_prop "x::'a::logic == y"
      val yz = read_prop "y::'a::logic == z"
      val xythm = Thm.assume xy and yzthm = Thm.assume yz
  in store_standard_thm "transitive" (Thm.implies_intr yz (Thm.transitive xythm yzthm)) end;

fun symmetric_fun thm = thm RS symmetric_thm;

fun extensional eq =
  let val eq' =
    abstract_rule "x" (snd (Thm.dest_comb (fst (dest_equals (cprop_of eq))))) eq
  in equal_elim (eta_conversion (cprop_of eq')) eq' end;

val imp_cong =
  let
    val ABC = read_prop "PROP A ==> PROP B == PROP C"
    val AB = read_prop "PROP A ==> PROP B"
    val AC = read_prop "PROP A ==> PROP C"
    val A = read_prop "PROP A"
  in
    open_store_standard_thm "imp_cong" (implies_intr ABC (equal_intr
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
    open_store_standard_thm "swap_prems_eq" (equal_intr
      (implies_intr ABC (implies_intr B (implies_intr A
        (implies_elim (implies_elim (assume ABC) (assume A)) (assume B)))))
      (implies_intr BAC (implies_intr A (implies_intr B
        (implies_elim (implies_elim (assume BAC) (assume B)) (assume A))))))
  end;

val refl_implies = reflexive implies;


(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl = open_store_standard_thm "asm_rl" (Thm.trivial (read_prop "PROP ?psi"));
val _ = store_thm "_" asm_rl;

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl =
  open_store_standard_thm "cut_rl"
    (Thm.trivial (read_prop "PROP ?psi ==> PROP ?theta"));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let val V = read_prop "PROP V"
      and VW = read_prop "PROP V ==> PROP W";
  in
    open_store_standard_thm "revcut_rl"
      (implies_intr V (implies_intr VW (implies_elim (assume VW) (assume V))))
  end;

(*for deleting an unwanted assumption*)
val thin_rl =
  let val V = read_prop "PROP V"
      and W = read_prop "PROP W";
  in  open_store_standard_thm "thin_rl" (implies_intr V (implies_intr W (assume W)))
  end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let val V  = read_prop "PROP V"
      and QV = read_prop "!!x::'a. PROP V"
      and x  = read_cterm proto_sign ("x", TypeInfer.logicT);
  in
    open_store_standard_thm "triv_forall_equality"
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
  in open_store_standard_thm "swap_prems_rl"
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
    open_store_standard_thm "equal_intr_rule"
      (implies_intr PQ (implies_intr QP (equal_intr (assume PQ) (assume QP))))
  end;


(*(PROP ?phi ==> (!!x. PROP ?psi(x))) == (!!x. PROP ?phi ==> PROP ?psi(x))
  Rewrite rule for HHF normalization.
*)

val norm_hhf_eq =
  let
    val cert = Thm.cterm_of proto_sign;
    val aT = TFree ("'a", Term.logicS);
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
    |> open_store_standard_thm "norm_hhf_eq"
  end;


(*** Instantiate theorem th, reading instantiations under signature sg ****)

(*Version that normalizes the result: Thm.instantiate no longer does that*)
fun instantiate instpair th = Thm.instantiate instpair th  COMP   asm_rl;

fun read_instantiate_sg sg sinsts th =
    let val ts = types_sorts th;
        val used = add_term_tvarnames(#prop(rep_thm th),[]);
    in  instantiate (read_insts sg ts ts used sinsts) th  end;

(*Instantiate theorem th, reading instantiations under theory of th*)
fun read_instantiate sinsts th =
    read_instantiate_sg (#sign (rep_thm th)) sinsts th;


(*Left-to-right replacements: tpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms, inferring type instantiations. *)
local
  fun add_types ((ct,cu), (sign,tye,maxidx)) =
    let val {sign=signt, t=t, T= T, maxidx=maxt,...} = rep_cterm ct
        and {sign=signu, t=u, T= U, maxidx=maxu,...} = rep_cterm cu;
        val maxi = Int.max(maxidx, Int.max(maxt, maxu));
        val sign' = Sign.merge(sign, Sign.merge(signt, signu))
        val (tye',maxi') = Type.unify (#tsig(Sign.rep_sg sign')) maxi tye (T,U)
          handle Type.TUNIFY => raise TYPE("Ill-typed instantiation", [T,U], [t,u])
    in  (sign', tye', maxi')  end;
in
fun cterm_instantiate ctpairs0 th =
  let val (sign,tye,_) = foldr add_types (ctpairs0, (#sign(rep_thm th), Vartab.empty, 0))
      fun instT(ct,cu) = let val inst = subst_TVars_Vartab tye
                         in (cterm_fun inst ct, cterm_fun inst cu) end
      fun ctyp2 (ix,T) = (ix, ctyp_of sign T)
  in  instantiate (map ctyp2 (Vartab.dest tye), map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible signatures",0,[th])
       | TYPE (msg, _, _) => raise THM(msg, 0, [th])
end;


(** Derived rules mainly for METAHYPS **)

(*Given the term "a", takes (%x.t)==(%x.u) to t[a/x]==u[a/x]*)
fun equal_abs_elim ca eqth =
  let val {sign=signa, t=a, ...} = rep_cterm ca
      and combth = combination eqth (reflexive ca)
      val {sign,prop,...} = rep_thm eqth
      val (abst,absu) = Logic.dest_equals prop
      val cterm = cterm_of (Sign.merge (sign,signa))
  in  transitive (symmetric (beta_conversion false (cterm (abst$a))))
           (transitive combth (beta_conversion false (cterm (absu$a))))
  end
  handle THM _ => raise THM("equal_abs_elim", 0, [eqth]);

(*Calling equal_abs_elim with multiple terms*)
fun equal_abs_elim_list cts th = foldr (uncurry equal_abs_elim) (rev cts, th);

local
  val alpha = TVar(("'a",0), [])     (*  type ?'a::{}  *)
  fun err th = raise THM("flexpair_inst: ", 0, [th])
  fun flexpair_inst def th =
    let val {prop = Const _ $ t $ u,  sign,...} = rep_thm th
        val cterm = cterm_of sign
        fun cvar a = cterm(Var((a,0),alpha))
        val def' = cterm_instantiate [(cvar"t", cterm t), (cvar"u", cterm u)]
                   def
    in  equal_elim def' th
    end
    handle THM _ => err th | Bind => err th
in
val flexpair_intr = flexpair_inst (symmetric ProtoPure.flexpair_def)
and flexpair_elim = flexpair_inst ProtoPure.flexpair_def
end;

(*Version for flexflex pairs -- this supports lifting.*)
fun flexpair_abs_elim_list cts =
    flexpair_intr o equal_abs_elim_list cts o flexpair_elim;


(*** Goal (PROP A) <==> PROP A ***)

local
  val cert = Thm.cterm_of proto_sign;
  val A = Free ("A", propT);
  val G = Logic.mk_goal A;
  val (G_def, _) = freeze_thaw ProtoPure.Goal_def;
in
  val triv_goal = store_thm "triv_goal" (kind_rule internalK (standard
      (Thm.equal_elim (Thm.symmetric G_def) (Thm.assume (cert A)))));
  val rev_triv_goal = store_thm "rev_triv_goal" (kind_rule internalK (standard
      (Thm.equal_elim G_def (Thm.assume (cert G)))));
end;

val mk_cgoal = Thm.capply (Thm.cterm_of proto_sign Logic.goal_const);
fun assume_goal ct = Thm.assume (mk_cgoal ct) RS rev_triv_goal;

fun implies_intr_goals cprops thm =
  implies_elim_list (implies_intr_list cprops thm) (map assume_goal cprops)
  |> implies_intr_list (map mk_cgoal cprops);



(** variations on instantiate **)

(*shorthand for instantiating just one variable in the current theory*)
fun inst x t = read_instantiate_sg (sign_of (the_context())) [(x,t)];


(* collect vars *)

val add_tvarsT = foldl_atyps (fn (vs, TVar v) => v ins vs | (vs, _) => vs);
val add_tvars = foldl_types add_tvarsT;
val add_vars = foldl_aterms (fn (vs, Var v) => v ins vs | (vs, _) => vs);

fun tvars_of_terms ts = rev (foldl add_tvars ([], ts));
fun vars_of_terms ts = rev (foldl add_vars ([], ts));

fun tvars_of thm = tvars_of_terms [#prop (Thm.rep_thm thm)];
fun vars_of thm = vars_of_terms [#prop (Thm.rep_thm thm)];


(* instantiate by left-to-right occurrence of variables *)

fun instantiate' cTs cts thm =
  let
    fun err msg =
      raise TYPE ("instantiate': " ^ msg,
        mapfilter (apsome Thm.typ_of) cTs,
        mapfilter (apsome Thm.term_of) cts);

    fun inst_of (v, ct) =
      (Thm.cterm_of (#sign (Thm.rep_cterm ct)) (Var v), ct)
        handle TYPE (msg, _, _) => err msg;

    fun zip_vars _ [] = []
      | zip_vars (_ :: vs) (None :: opt_ts) = zip_vars vs opt_ts
      | zip_vars (v :: vs) (Some t :: opt_ts) = (v, t) :: zip_vars vs opt_ts
      | zip_vars [] _ = err "more instantiations than variables in thm";

    (*instantiate types first!*)
    val thm' =
      if forall is_none cTs then thm
      else Thm.instantiate (zip_vars (map fst (tvars_of thm)) cTs, []) thm;
    in
      if forall is_none cts then thm'
      else Thm.instantiate ([], map inst_of (zip_vars (vars_of thm') cts)) thm'
    end;


(* unvarify(T) *)

(*assume thm in standard form, i.e. no frees, 0 var indexes*)

fun unvarifyT thm =
  let
    val cT = Thm.ctyp_of (Thm.sign_of_thm thm);
    val tfrees = map (fn ((x, _), S) => Some (cT (TFree (x, S)))) (tvars_of thm);
  in instantiate' tfrees [] thm end;

fun unvarify raw_thm =
  let
    val thm = unvarifyT raw_thm;
    val ct = Thm.cterm_of (Thm.sign_of_thm thm);
    val frees = map (fn ((x, _), T) => Some (ct (Free (x, T)))) (vars_of thm);
  in instantiate' [] frees thm end;


(* tvars_intr_list *)

fun tfrees_of thm =
  let val {hyps, prop, ...} = Thm.rep_thm thm
  in foldr Term.add_term_tfree_names (prop :: hyps, []) end;

fun tvars_intr_list tfrees thm =
  Thm.varifyT' (tfrees_of thm \\ tfrees) thm;


(* increment var indexes *)

fun incr_indexes_wrt is cTs cts thms =
  let
    val maxidx =
      foldl Int.max (~1, is @
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
      let val cert = Thm.ctyp_of (Thm.sign_of_thm thm)
      in instantiate' (map (fn ((x, _), S) => Some (cert (TFree (x, S)))) tvars) [] thm end);

fun freeze_all_Vars thm =
  (case vars_of thm of
    [] => thm
  | vars =>
      let val cert = Thm.cterm_of (Thm.sign_of_thm thm)
      in instantiate' [] (map (fn ((x, _), T) => Some (cert (Free (x, T)))) vars) thm end);

val freeze_all = freeze_all_Vars o freeze_all_TVars;


(* mk_triv_goal *)

(*make an initial proof state, "PROP A ==> (PROP A)" *)
fun mk_triv_goal ct = instantiate' [] [Some ct] triv_goal;



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

  val incr = incr_indexes_wrt [] [] [];
in

fun conj_intr tha thb = thb COMP (tha COMP incr [tha, thb] conj_intr_rule);
val conj_intr_list = foldr1 (uncurry conj_intr);

fun conj_elim th =
  let val th' = forall_elim_var (#maxidx (Thm.rep_thm th) + 1) th
  in (incr [th'] proj1 COMP th', incr [th'] proj2 COMP th') end;

fun conj_elim_list th =
  let val (th1, th2) = conj_elim th
  in conj_elim_list th1 @ conj_elim_list th2 end handle THM _ => [th];

end;

end;

structure BasicDrule: BASIC_DRULE = Drule;
open BasicDrule;
