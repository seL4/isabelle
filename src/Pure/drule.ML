(*  Title:      Pure/drule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Derived rules and other operations on theorems and theories
*)

infix 0 RS RSN RL RLN MRS MRL COMP;

signature DRULE =
  sig
  val add_defs		: (string * string) list -> theory -> theory
  val add_defs_i	: (string * term) list -> theory -> theory
  val asm_rl		: thm
  val assume_ax		: theory -> string -> thm
  val COMP		: thm * thm -> thm
  val compose		: thm * int * thm -> thm list
  val cprems_of		: thm -> cterm list
  val cterm_instantiate	: (cterm*cterm)list -> thm -> thm
  val cut_rl		: thm
  val equal_abs_elim	: cterm  -> thm -> thm
  val equal_abs_elim_list: cterm list -> thm -> thm
  val eq_thm		: thm * thm -> bool
  val same_thm		: thm * thm -> bool
  val eq_thm_sg		: thm * thm -> bool
  val flexpair_abs_elim_list: cterm list -> thm -> thm
  val forall_intr_list	: cterm list -> thm -> thm
  val forall_intr_frees	: thm -> thm
  val forall_intr_vars	: thm -> thm
  val forall_elim_list	: cterm list -> thm -> thm
  val forall_elim_var	: int -> thm -> thm
  val forall_elim_vars	: int -> thm -> thm
  val implies_elim_list	: thm -> thm list -> thm
  val implies_intr_list	: cterm list -> thm -> thm
  val dest_implies      : cterm -> cterm * cterm
  val MRL		: thm list list * thm list -> thm list
  val MRS		: thm list * thm -> thm
  val read_instantiate	: (string*string)list -> thm -> thm
  val read_instantiate_sg: Sign.sg -> (string*string)list -> thm -> thm
  val read_insts	:
          Sign.sg -> (indexname -> typ option) * (indexname -> sort option)
                  -> (indexname -> typ option) * (indexname -> sort option)
                  -> string list -> (string*string)list
                  -> (indexname*ctyp)list * (cterm*cterm)list
  val reflexive_thm	: thm
  val refl_implies      : thm
  val revcut_rl		: thm
  val rewrite_goal_rule	: bool * bool -> (meta_simpset -> thm -> thm option)
        -> meta_simpset -> int -> thm -> thm
  val rewrite_goals_rule_aux: (meta_simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_rule_aux	: (meta_simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_thm	: bool * bool -> (meta_simpset -> thm -> thm option)
	-> meta_simpset -> thm -> thm
  val RS		: thm * thm -> thm
  val RSN		: thm * (int * thm) -> thm
  val RL		: thm list * thm list -> thm list
  val RLN		: thm list * (int * thm list) -> thm list
  val size_of_thm	: thm -> int
  val skip_flexpairs	: cterm -> cterm
  val standard		: thm -> thm
  val strip_imp_prems	: cterm -> cterm list
  val swap_prems_rl     : thm
  val symmetric_thm	: thm
  val thin_rl		: thm
  val transitive_thm	: thm
  val triv_forall_equality: thm
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val zero_var_indexes	: thm -> thm
  end;


structure Drule : DRULE =
struct

(**** Extend Theories ****)

(** add constant definitions **)

(* all_axioms_of *)

(*results may contain duplicates!*)

fun ancestry_of thy =
  thy :: List.concat (map ancestry_of (parents_of thy));

val all_axioms_of =
  List.concat o map (Symtab.dest o #new_axioms o rep_theory) o ancestry_of;


(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)*)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in
    Type.raw_unify (ty1', ty2')
  end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;


(* clash_defns *)

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals tm))) in
    if clash_consts c_ty (c, ty') then Some (name, ty') else None
  end handle TERM _ => None;

fun clash_defns c_ty axms =
  distinct (mapfilter (clash_defn c_ty) axms);


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise_term msg [tm];

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun occs_const (Const c_ty') = (c_ty' = (c, ty))
      | occs_const (Abs (_, _, t)) = occs_const t
      | occs_const (t $ u) = occs_const t orelse occs_const u
      | occs_const _ = false;

    val show_frees = commas_quote o map (fst o dest_Free);
    val show_tfrees = commas_quote o map fst;

    val lhs_dups = duplicates args;
    val rhs_extras = gen_rems (op =) (term_frees rhs, args);
    val rhs_extrasT = gen_rems (op =) (term_tfrees rhs, typ_tfrees ty);
  in
    if not (forall is_Free args) then
      err "Arguments (on lhs) must be variables"
    else if not (null lhs_dups) then
      err ("Duplicate variables on lhs: " ^ show_frees lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ show_frees rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ show_tfrees rhs_extrasT)
    else if occs_const rhs then
      err ("Constant to be defined occurs on rhs")
    else (c, ty)
  end;


(* check_defn *)

fun err_in_defn name msg =
  (writeln msg; error ("The error(s) above occurred in definition " ^ quote name));

fun check_defn sign (axms, (name, tm)) =
  let
    fun show_const (c, ty) = quote (Pretty.string_of (Pretty.block
      [Pretty.str (c ^ " ::"), Pretty.brk 1, Sign.pretty_typ sign ty]));

    fun show_defn c (dfn, ty') = show_const (c, ty') ^ " in " ^ dfn;
    fun show_defns c = cat_lines o map (show_defn c);

    val (c, ty) = dest_defn tm
      handle TERM (msg, _) => err_in_defn name msg;
    val defns = clash_defns (c, ty) axms;
  in
    if not (null defns) then
      err_in_defn name ("Definition of " ^ show_const (c, ty) ^
        "\nclashes with " ^ show_defns c defns)
    else (name, tm) :: axms
  end;


(* add_defs *)

fun ext_defns prep_axm raw_axms thy =
  let
    val axms = map (prep_axm (sign_of thy)) raw_axms;
    val all_axms = all_axioms_of thy;
  in
    foldl (check_defn (sign_of thy)) (all_axms, axms);
    add_axioms_i axms thy
  end;

val add_defs_i = ext_defns cert_axm;
val add_defs = ext_defns read_axm;



(**** More derived rules and operations on theorems ****)

(** some cterm->cterm operations: much faster than calling cterm_of! **)

(** SAME NAMES as in structure Logic: use compound identifiers! **)

(*dest_implies for cterms. Note T=prop below*)
fun dest_implies ct =
    case term_of ct of 
	(Const("==>", _) $ _ $ _) => 
	    let val (ct1,ct2) = dest_comb ct
	    in  (#2 (dest_comb ct1), ct2)  end	     
      | _ => raise TERM ("dest_implies", [term_of ct]) ;


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
	strip_imp_concl (#2 (dest_comb ct))
  | _ => ct;

(*The premises of a theorem, as a cterm list*)
val cprems_of = strip_imp_prems o skip_flexpairs o cprop_of;


(** reading of instantiations **)

fun indexname cs = case Syntax.scan_varname cs of (v,[]) => v
        | _ => error("Lexical error in variable name " ^ quote (implode cs));

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

(* this code is a bit of a mess. add_cterm could be simplified greatly if
   simultaneous instantiations were read or at least type checked
   simultaneously rather than one after the other. This would make the tricky
   composition of implicit type instantiations (parameter tye) superfluous.
*)
fun read_insts sign (rtypes,rsorts) (types,sorts) used insts =
let val {tsig,...} = Sign.rep_sg sign
    fun split([],tvs,vs) = (tvs,vs)
      | split((sv,st)::l,tvs,vs) = (case explode sv of
                  "'"::cs => split(l,(indexname cs,st)::tvs,vs)
                | cs => split(l,tvs,(indexname cs,st)::vs));
    val (tvs,vs) = split(insts,[],[]);
    fun readT((a,i),st) =
        let val ixn = ("'" ^ a,i);
            val S = case rsorts ixn of Some S => S | None => absent ixn;
            val T = Sign.read_typ (sign,sorts) st;
        in if Type.typ_instance(tsig,T,TVar(ixn,S)) then (ixn,T)
           else inst_failure ixn
        end
    val tye = map readT tvs;
    fun add_cterm ((cts,tye,used), (ixn,st)) =
        let val T = case rtypes ixn of
                      Some T => typ_subst_TVars tye T
                    | None => absent ixn;
            val (ct,tye2) = read_def_cterm(sign,types,sorts) used false (st,T);
            val cts' = (ixn,T,ct)::cts
            fun inst(ixn,T,ct) = (ixn,typ_subst_TVars tye2 T,ct)
            val used' = add_term_tvarnames(term_of ct,used);
        in (map inst cts',tye2 @ tye,used') end
    val (cterms,tye',_) = foldl add_cterm (([],tye,used), vs);
in (map (fn (ixn,T) => (ixn,ctyp_of sign T)) tye',
    map (fn (ixn,T,ct) => (cterm_of sign (Var(ixn,T)), ct)) cterms)
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

(** Standardization of rules **)

(*Generalization over a list of variables, IGNORING bad ones*)
fun forall_intr_list [] th = th
  | forall_intr_list (y::ys) th =
        let val gth = forall_intr_list ys th
        in  forall_intr y gth   handle THM _ =>  gth  end;

(*Generalization over all suitable Free variables*)
fun forall_intr_frees th =
    let val {prop,sign,...} = rep_thm th
    in  forall_intr_list
         (map (cterm_of sign) (sort atless (term_frees prop)))
         th
    end;

(*Replace outermost quantified variable by Var of given index.
    Could clash with Vars already present.*)
fun forall_elim_var i th =
    let val {prop,sign,...} = rep_thm th
    in case prop of
          Const("all",_) $ Abs(a,T,_) =>
              forall_elim (cterm_of sign (Var((a,i), T)))  th
        | _ => raise THM("forall_elim_var", i, [th])
    end;

(*Repeat forall_elim_var until all outer quantifiers are removed*)
fun forall_elim_vars i th =
    forall_elim_vars i (forall_elim_var i th)
        handle THM _ => th;

(*Specialization over a list of cterms*)
fun forall_elim_list cts th = foldr (uncurry forall_elim) (rev cts, th);

(* maps [A1,...,An], B   to   [| A1;...;An |] ==> B  *)
fun implies_intr_list cAs th = foldr (uncurry implies_intr) (cAs,th);

(* maps [| A1;...;An |] ==> B and [A1,...,An]   to   B *)
fun implies_elim_list impth ths = foldl (uncurry implies_elim) (impth,ths);

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
    in instantiate (ctye, varpairs(vars,rev bs)) th end;


(*Standard form of object-rule: no hypotheses, Frees, or outer quantifiers;
    all generality expressed by Vars having index 0.*)
fun standard th =
  let val {maxidx,...} = rep_thm th
  in
    th |> implies_intr_hyps
       |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Thm.strip_shyps |> Thm.implies_intr_shyps
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;


(*Assume a new formula, read following the same conventions as axioms.
  Generalizes over Free variables,
  creates the assumption, and then strips quantifiers.
  Example is [| ALL x:?A. ?P(x) |] ==> [| ?P(?a) |]
             [ !(A,P,a)[| ALL x:A. P(x) |] ==> [| P(a) |] ]    *)
fun assume_ax thy sP =
    let val sign = sign_of thy
        val prop = Logic.close_form (term_of (read_cterm sign
                         (sP, propT)))
    in forall_elim_vars 0 (assume (cterm_of sign prop))  end;

(*Resolution: exactly one resolvent must be produced.*)
fun tha RSN (i,thb) =
  case Sequence.chop (2, biresolution false [(false,tha)] i thb) of
      ([th],_) => th
    | ([],_)   => raise THM("RSN: no unifiers", i, [tha,thb])
    |      _   => raise THM("RSN: multiple unifiers", i, [tha,thb]);

(*resolution: P==>Q, Q==>R gives P==>R. *)
fun tha RS thb = tha RSN (1,thb);

(*For joining lists of rules*)
fun thas RLN (i,thbs) =
  let val resolve = biresolution false (map (pair false) thas) i
      fun resb thb = Sequence.list_of_s (resolve thb) handle THM _ => []
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

(*compose Q and [...,Qi,Q(i+1),...]==>R to [...,Q(i+1),...]==>R
  with no lifting or renaming!  Q may contain ==> or meta-quants
  ALWAYS deletes premise i *)
fun compose(tha,i,thb) =
    Sequence.list_of_s (bicompose false (false,tha,0) i thb);

(*compose Q and [Q1,Q2,...,Qk]==>R to [Q2,...,Qk]==>R getting unique result*)
fun tha COMP thb =
    case compose(tha,1,thb) of
        [th] => th
      | _ =>   raise THM("COMP", 1, [tha,thb]);

(*Instantiate theorem th, reading instantiations under signature sg*)
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
          handle Type.TUNIFY => raise TYPE("add_types", [T,U], [t,u])
    in  (sign', tye', maxi')  end;
in
fun cterm_instantiate ctpairs0 th =
  let val (sign,tye,_) = foldr add_types (ctpairs0, (#sign(rep_thm th),[],0))
      val tsig = #tsig(Sign.rep_sg sign);
      fun instT(ct,cu) = let val inst = subst_TVars tye
                         in (cterm_fun inst ct, cterm_fun inst cu) end
      fun ctyp2 (ix,T) = (ix, ctyp_of sign T)
  in  instantiate (map ctyp2 tye, map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible signatures",0,[th])
       | TYPE _ => raise THM("cterm_instantiate: types", 0, [th])
end;


(** theorem equality test is exported and used by BEST_FIRST **)

(*equality of theorems uses equality of signatures and
  the a-convertible test for terms*)
fun eq_thm (th1,th2) =
    let val {sign=sg1, shyps=shyps1, hyps=hyps1, prop=prop1, ...} = rep_thm th1
        and {sign=sg2, shyps=shyps2, hyps=hyps2, prop=prop2, ...} = rep_thm th2
    in  Sign.eq_sg (sg1,sg2) andalso
        eq_set_sort (shyps1, shyps2) andalso
        aconvs(hyps1,hyps2) andalso
        prop1 aconv prop2
    end;

(*equality of theorems using similarity of signatures,
  i.e. the theorems belong to the same theory but not necessarily to the same
  version of this theory*)
fun same_thm (th1,th2) =
    let val {sign=sg1, shyps=shyps1, hyps=hyps1, prop=prop1, ...} = rep_thm th1
        and {sign=sg2, shyps=shyps2, hyps=hyps2, prop=prop2, ...} = rep_thm th2
    in  Sign.same_sg (sg1,sg2) andalso
        eq_set_sort (shyps1, shyps2) andalso
        aconvs(hyps1,hyps2) andalso
        prop1 aconv prop2
    end;

(*Do the two theorems have the same signature?*)
fun eq_thm_sg (th1,th2) = Sign.eq_sg(#sign(rep_thm th1), #sign(rep_thm th2));

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o #prop o rep_thm;


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

val reflexive_thm =
  let val cx = cterm_of Sign.proto_pure (Var(("x",0),TVar(("'a",0),logicS)))
  in Thm.reflexive cx end;

val symmetric_thm =
  let val xy = read_cterm Sign.proto_pure ("x::'a::logic == y",propT)
  in standard(Thm.implies_intr_hyps(Thm.symmetric(Thm.assume xy))) end;

val transitive_thm =
  let val xy = read_cterm Sign.proto_pure ("x::'a::logic == y",propT)
      val yz = read_cterm Sign.proto_pure ("y::'a::logic == z",propT)
      val xythm = Thm.assume xy and yzthm = Thm.assume yz
  in standard(Thm.implies_intr yz (Thm.transitive xythm yzthm)) end;

(** Below, a "conversion" has type cterm -> thm **)

val refl_implies = reflexive (cterm_of Sign.proto_pure implies);

(*In [A1,...,An]==>B, rewrite the selected A's only -- for rewrite_goals_tac*)
(*Do not rewrite flex-flex pairs*)
fun goals_conv pred cv =
  let fun gconv i ct =
        let val (A,B) = dest_implies ct
            val (thA,j) = case term_of A of
                  Const("=?=",_)$_$_ => (reflexive A, i)
                | _ => (if pred i then cv A else reflexive A, i+1)
        in  combination (combination refl_implies thA) (gconv j B) end
        handle TERM _ => reflexive ct
  in gconv 1 end;

(*Use a conversion to transform a theorem*)
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

(*rewriting conversion*)
fun rew_conv mode prover mss = rewrite_cterm mode mss prover;

(*Rewrite a theorem*)
fun rewrite_rule_aux _ []   th = th
  | rewrite_rule_aux prover thms th =
      fconv_rule (rew_conv (true,false) prover (Thm.mss_of thms)) th;

fun rewrite_thm mode prover mss = fconv_rule (rew_conv mode prover mss);

(*Rewrite the subgoals of a proof state (represented by a theorem) *)
fun rewrite_goals_rule_aux _ []   th = th
  | rewrite_goals_rule_aux prover thms th =
      fconv_rule (goals_conv (K true) (rew_conv (true, true) prover
        (Thm.mss_of thms))) th;

(*Rewrite the subgoal of a proof state (represented by a theorem) *)
fun rewrite_goal_rule mode prover mss i thm =
  if 0 < i  andalso  i <= nprems_of thm
  then fconv_rule (goals_conv (fn j => j=i) (rew_conv mode prover mss)) thm
  else raise THM("rewrite_goal_rule",i,[thm]);


(** Derived rules mainly for METAHYPS **)

(*Given the term "a", takes (%x.t)==(%x.u) to t[a/x]==u[a/x]*)
fun equal_abs_elim ca eqth =
  let val {sign=signa, t=a, ...} = rep_cterm ca
      and combth = combination eqth (reflexive ca)
      val {sign,prop,...} = rep_thm eqth
      val (abst,absu) = Logic.dest_equals prop
      val cterm = cterm_of (Sign.merge (sign,signa))
  in  transitive (symmetric (beta_conversion (cterm (abst$a))))
           (transitive combth (beta_conversion (cterm (absu$a))))
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
    handle THM _ => err th | bind => err th
in
val flexpair_intr = flexpair_inst (symmetric flexpair_def)
and flexpair_elim = flexpair_inst flexpair_def
end;

(*Version for flexflex pairs -- this supports lifting.*)
fun flexpair_abs_elim_list cts =
    flexpair_intr o equal_abs_elim_list cts o flexpair_elim;


(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl = trivial(read_cterm Sign.proto_pure ("PROP ?psi",propT));

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl = trivial(read_cterm Sign.proto_pure
        ("PROP ?psi ==> PROP ?theta", propT));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let val V = read_cterm Sign.proto_pure ("PROP V", propT)
      and VW = read_cterm Sign.proto_pure ("PROP V ==> PROP W", propT);
  in  standard (implies_intr V
                (implies_intr VW
                 (implies_elim (assume VW) (assume V))))
  end;

(*for deleting an unwanted assumption*)
val thin_rl =
  let val V = read_cterm Sign.proto_pure ("PROP V", propT)
      and W = read_cterm Sign.proto_pure ("PROP W", propT);
  in  standard (implies_intr V (implies_intr W (assume W)))
  end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let val V  = read_cterm Sign.proto_pure ("PROP V", propT)
      and QV = read_cterm Sign.proto_pure ("!!x::'a. PROP V", propT)
      and x  = read_cterm Sign.proto_pure ("x", TFree("'a",logicS));
  in  standard (equal_intr (implies_intr QV (forall_elim x (assume QV)))
                           (implies_intr V  (forall_intr x (assume V))))
  end;

(* (PROP ?PhiA ==> PROP ?PhiB ==> PROP ?Psi) ==>
   (PROP ?PhiB ==> PROP ?PhiA ==> PROP ?Psi)
   `thm COMP swap_prems_rl' swaps the first two premises of `thm'
*)
val swap_prems_rl =
  let val cmajor = read_cterm Sign.proto_pure
            ("PROP PhiA ==> PROP PhiB ==> PROP Psi", propT);
      val major = assume cmajor;
      val cminor1 = read_cterm Sign.proto_pure  ("PROP PhiA", propT);
      val minor1 = assume cminor1;
      val cminor2 = read_cterm Sign.proto_pure  ("PROP PhiB", propT);
      val minor2 = assume cminor2;
  in standard
       (implies_intr cmajor (implies_intr cminor2 (implies_intr cminor1
         (implies_elim (implies_elim major minor1) minor2))))
  end;

end;

open Drule;
