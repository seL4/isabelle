(*  Title:      HOL/Tools/Sledgehammer/metis_tactics.ML
    Author:     Kong W. Susanto and Lawrence C. Paulson, CU Computer Laboratory
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)

signature METIS_TACTICS =
sig
  val trace: bool Unsynchronized.ref
  val type_lits: bool Config.T
  val metis_tac: Proof.context -> thm list -> int -> tactic
  val metisF_tac: Proof.context -> thm list -> int -> tactic
  val metisFT_tac: Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end

structure Metis_Tactics : METIS_TACTICS =
struct

open Clausifier
open Metis_Clauses

exception METIS of string * string

val trace = Unsynchronized.ref false;
fun trace_msg msg = if !trace then tracing (msg ()) else ();

val (type_lits, type_lits_setup) = Attrib.config_bool "metis_type_lits" (K true);

datatype mode = FO | HO | FT  (* first-order, higher-order, fully-typed *)

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)
val EXCLUDED_MIDDLE = @{lemma "P ==> ~ P ==> False" by (rule notE)}
val REFL_THM = Thm.incr_indexes 2 @{lemma "t ~= t ==> False" by simp}
val subst_em = @{lemma "s = t ==> P s ==> ~ P t ==> False" by simp}
val ssubst_em = @{lemma "s = t ==> P t ==> ~ P s ==> False" by simp}

(* ------------------------------------------------------------------------- *)
(* Useful Functions                                                          *)
(* ------------------------------------------------------------------------- *)

(* Match untyped terms. *)
fun untyped_aconv (Const (a, _)) (Const(b, _)) = (a = b)
  | untyped_aconv (Free (a, _)) (Free (b, _)) = (a = b)
  | untyped_aconv (Var ((a, _), _)) (Var ((b, _), _)) =
    (a = b) (* The index is ignored, for some reason. *)
  | untyped_aconv (Bound i) (Bound j) = (i = j)
  | untyped_aconv (Abs (_, _, t)) (Abs (_, _, u)) = untyped_aconv t u
  | untyped_aconv (t1 $ t2) (u1 $ u2) =
    untyped_aconv t1 u1 andalso untyped_aconv t2 u2
  | untyped_aconv _ _ = false

(* Finding the relative location of an untyped term within a list of terms *)
fun get_index lit =
  let val lit = Envir.eta_contract lit
      fun get _ [] = raise Empty
        | get n (x::xs) = if untyped_aconv lit (Envir.eta_contract (HOLogic.dest_Trueprop x))
                          then n  else get (n+1) xs
  in get 1 end;

(* ------------------------------------------------------------------------- *)
(* HOL to FOL  (Isabelle to Metis)                                           *)
(* ------------------------------------------------------------------------- *)

fun fn_isa_to_met "equal" = "="
  | fn_isa_to_met x       = x;

fun metis_lit b c args = (b, (c, args));

fun hol_type_to_fol (TyVar (x, _)) = Metis.Term.Var x
  | hol_type_to_fol (TyFree (s, _)) = Metis.Term.Fn (s, [])
  | hol_type_to_fol (TyConstr ((s, _), tps)) =
    Metis.Term.Fn (s, map hol_type_to_fol tps);

(*These two functions insert type literals before the real literals. That is the
  opposite order from TPTP linkup, but maybe OK.*)

fun hol_term_to_fol_FO tm =
  case strip_combterm_comb tm of
      (CombConst ((c, _), _, tys), tms) =>
        let val tyargs = map hol_type_to_fol tys
            val args   = map hol_term_to_fol_FO tms
        in Metis.Term.Fn (c, tyargs @ args) end
    | (CombVar ((v, _), _), []) => Metis.Term.Var v
    | _ => raise Fail "hol_term_to_fol_FO";

fun hol_term_to_fol_HO (CombVar ((s, _), _)) = Metis.Term.Var s
  | hol_term_to_fol_HO (CombConst ((a, _), _, tylist)) =
      Metis.Term.Fn (fn_isa_to_met a, map hol_type_to_fol tylist)
  | hol_term_to_fol_HO (CombApp (tm1, tm2)) =
       Metis.Term.Fn (".", map hol_term_to_fol_HO [tm1, tm2]);

(*The fully-typed translation, to avoid type errors*)
fun wrap_type (tm, ty) = Metis.Term.Fn("ti", [tm, hol_type_to_fol ty]);

fun hol_term_to_fol_FT (CombVar ((s, _), ty)) = wrap_type (Metis.Term.Var s, ty)
  | hol_term_to_fol_FT (CombConst((a, _), ty, _)) =
      wrap_type (Metis.Term.Fn(fn_isa_to_met a, []), ty)
  | hol_term_to_fol_FT (tm as CombApp(tm1,tm2)) =
       wrap_type (Metis.Term.Fn(".", map hol_term_to_fol_FT [tm1,tm2]),
                  type_of_combterm tm);

fun hol_literal_to_fol FO (Literal (pol, tm)) =
      let val (CombConst((p, _), _, tys), tms) = strip_combterm_comb tm
          val tylits = if p = "equal" then [] else map hol_type_to_fol tys
          val lits = map hol_term_to_fol_FO tms
      in metis_lit pol (fn_isa_to_met p) (tylits @ lits) end
  | hol_literal_to_fol HO (Literal (pol, tm)) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pol "=" (map hol_term_to_fol_HO tms)
        | _ => metis_lit pol "{}" [hol_term_to_fol_HO tm])   (*hBOOL*)
  | hol_literal_to_fol FT (Literal (pol, tm)) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pol "=" (map hol_term_to_fol_FT tms)
        | _ => metis_lit pol "{}" [hol_term_to_fol_FT tm])   (*hBOOL*);

fun literals_of_hol_term thy mode t =
      let val (lits, types_sorts) = literals_of_term thy t
      in  (map (hol_literal_to_fol mode) lits, types_sorts) end;

(*Sign should be "true" for conjecture type constraints, "false" for type lits in clauses.*)
fun metis_of_type_literals pos (TyLitVar (s, (s', _))) =
    metis_lit pos s [Metis.Term.Var s']
  | metis_of_type_literals pos (TyLitFree (s, (s', _))) =
    metis_lit pos s [Metis.Term.Fn (s',[])]

fun default_sort _ (TVar _) = false
  | default_sort ctxt (TFree (x, s)) = (s = the_default [] (Variable.def_sort ctxt (x, ~1)));

fun metis_of_tfree tf =
  Metis.Thm.axiom (Metis.LiteralSet.singleton (metis_of_type_literals true tf));

fun hol_thm_to_fol is_conjecture ctxt mode j skolem_somes th =
  let
    val thy = ProofContext.theory_of ctxt
    val (skolem_somes, (mlits, types_sorts)) =
     th |> prop_of |> conceal_skolem_somes j skolem_somes
        ||> (HOLogic.dest_Trueprop #> literals_of_hol_term thy mode)
  in
      if is_conjecture then
          (Metis.Thm.axiom (Metis.LiteralSet.fromList mlits),
           type_literals_for_types types_sorts, skolem_somes)
      else
        let val tylits = filter_out (default_sort ctxt) types_sorts
                         |> type_literals_for_types
            val mtylits = if Config.get ctxt type_lits
                          then map (metis_of_type_literals false) tylits else []
        in
          (Metis.Thm.axiom (Metis.LiteralSet.fromList(mtylits @ mlits)), [],
           skolem_somes)
        end
  end;

(* ARITY CLAUSE *)

fun m_arity_cls (TConsLit (c,t,args)) =
      metis_lit true (make_type_class c) [Metis.Term.Fn(t, map Metis.Term.Var args)]
  | m_arity_cls (TVarLit (c,str))     =
      metis_lit false (make_type_class c) [Metis.Term.Var str];

(*TrueI is returned as the Isabelle counterpart because there isn't any.*)
fun arity_cls (ArityClause {conclLit, premLits, ...}) =
  (TrueI,
   Metis.Thm.axiom (Metis.LiteralSet.fromList (map m_arity_cls (conclLit :: premLits))));

(* CLASSREL CLAUSE *)

fun m_classrel_cls subclass superclass =
  [metis_lit false subclass [Metis.Term.Var "T"], metis_lit true superclass [Metis.Term.Var "T"]];

fun classrel_cls (ClassrelClause {subclass, superclass, ...}) =
  (TrueI, Metis.Thm.axiom (Metis.LiteralSet.fromList (m_classrel_cls subclass superclass)));

(* ------------------------------------------------------------------------- *)
(* FOL to HOL  (Metis to Isabelle)                                           *)
(* ------------------------------------------------------------------------- *)

datatype term_or_type = Term of Term.term | Type of Term.typ;

fun terms_of [] = []
  | terms_of (Term t :: tts) = t :: terms_of tts
  | terms_of (Type _ :: tts) = terms_of tts;

fun types_of [] = []
  | types_of (Term (Term.Var ((a,idx), _)) :: tts) =
      if String.isPrefix "_" a then
          (*Variable generated by Metis, which might have been a type variable.*)
          TVar (("'" ^ a, idx), HOLogic.typeS) :: types_of tts
      else types_of tts
  | types_of (Term _ :: tts) = types_of tts
  | types_of (Type T :: tts) = T :: types_of tts;

fun apply_list rator nargs rands =
  let val trands = terms_of rands
  in  if length trands = nargs then Term (list_comb(rator, trands))
      else raise Fail
        ("apply_list: wrong number of arguments: " ^ Syntax.string_of_term_global Pure.thy rator ^
          " expected " ^ Int.toString nargs ^
          " received " ^ commas (map (Syntax.string_of_term_global Pure.thy) trands))
  end;

fun infer_types ctxt =
  Syntax.check_terms (ProofContext.set_mode ProofContext.mode_pattern ctxt);

(*We use 1 rather than 0 because variable references in clauses may otherwise conflict
  with variable constraints in the goal...at least, type inference often fails otherwise.
  SEE ALSO axiom_inf below.*)
fun mk_var (w,T) = Term.Var((w,1), T);

(*include the default sort, if available*)
fun mk_tfree ctxt w =
  let val ww = "'" ^ w
  in  TFree(ww, the_default HOLogic.typeS (Variable.def_sort ctxt (ww, ~1)))  end;

(*Remove the "apply" operator from an HO term*)
fun strip_happ args (Metis.Term.Fn(".",[t,u])) = strip_happ (u::args) t
  | strip_happ args x = (x, args);

fun make_tvar s = TVar (("'" ^ s, 0), HOLogic.typeS)

fun fol_type_to_isa _ (Metis.Term.Var v) =
     (case strip_prefix tvar_prefix v of
          SOME w => make_tvar w
        | NONE   => make_tvar v)
  | fol_type_to_isa ctxt (Metis.Term.Fn(x, tys)) =
     (case strip_prefix tconst_prefix x of
          SOME tc => Term.Type (invert_const tc, map (fol_type_to_isa ctxt) tys)
        | NONE    =>
      case strip_prefix tfree_prefix x of
          SOME tf => mk_tfree ctxt tf
        | NONE    => raise Fail ("fol_type_to_isa: " ^ x));

fun reveal_skolem_somes skolem_somes =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix skolem_theory_name s then
                   AList.lookup (op =) skolem_somes s
                   |> the |> map_types Type_Infer.paramify_vars
                 else
                   t
               | t => t)

(*Maps metis terms to isabelle terms*)
fun hol_term_from_fol_PT ctxt fol_tm =
  let val thy = ProofContext.theory_of ctxt
      val _ = trace_msg (fn () => "hol_term_from_fol_PT: " ^
                                  Metis.Term.toString fol_tm)
      fun tm_to_tt (Metis.Term.Var v) =
             (case strip_prefix tvar_prefix v of
                  SOME w => Type (make_tvar w)
                | NONE =>
              case strip_prefix schematic_var_prefix v of
                  SOME w => Term (mk_var (w, HOLogic.typeT))
                | NONE   => Term (mk_var (v, HOLogic.typeT)) )
                    (*Var from Metis with a name like _nnn; possibly a type variable*)
        | tm_to_tt (Metis.Term.Fn ("{}", [arg])) = tm_to_tt arg   (*hBOOL*)
        | tm_to_tt (t as Metis.Term.Fn (".",_)) =
            let val (rator,rands) = strip_happ [] t
            in  case rator of
                    Metis.Term.Fn(fname,ts) => applic_to_tt (fname, ts @ rands)
                  | _ => case tm_to_tt rator of
                             Term t => Term (list_comb(t, terms_of (map tm_to_tt rands)))
                           | _ => raise Fail "tm_to_tt: HO application"
            end
        | tm_to_tt (Metis.Term.Fn (fname, args)) = applic_to_tt (fname,args)
      and applic_to_tt ("=",ts) =
            Term (list_comb(Const (@{const_name "op ="}, HOLogic.typeT), terms_of (map tm_to_tt ts)))
        | applic_to_tt (a,ts) =
            case strip_prefix const_prefix a of
                SOME b =>
                  let val c = invert_const b
                      val ntypes = num_type_args thy c
                      val nterms = length ts - ntypes
                      val tts = map tm_to_tt ts
                      val tys = types_of (List.take(tts,ntypes))
                  in if length tys = ntypes then
                         apply_list (Const (c, dummyT)) nterms (List.drop(tts,ntypes))
                     else
                       raise Fail ("Constant " ^ c ^ " expects " ^ Int.toString ntypes ^
                                   " but gets " ^ Int.toString (length tys) ^
                                   " type arguments\n" ^
                                   cat_lines (map (Syntax.string_of_typ ctxt) tys) ^
                                   " the terms are \n" ^
                                   cat_lines (map (Syntax.string_of_term ctxt) (terms_of tts)))
                     end
              | NONE => (*Not a constant. Is it a type constructor?*)
            case strip_prefix tconst_prefix a of
                SOME b =>
                  Type (Term.Type (invert_const b, types_of (map tm_to_tt ts)))
              | NONE => (*Maybe a TFree. Should then check that ts=[].*)
            case strip_prefix tfree_prefix a of
                SOME b => Type (mk_tfree ctxt b)
              | NONE => (*a fixed variable? They are Skolem functions.*)
            case strip_prefix fixed_var_prefix a of
                SOME b =>
                  let val opr = Term.Free(b, HOLogic.typeT)
                  in  apply_list opr (length ts) (map tm_to_tt ts)  end
              | NONE => raise Fail ("unexpected metis function: " ^ a)
  in
    case tm_to_tt fol_tm of
      Term t => t
    | _ => raise Fail "fol_tm_to_tt: Term expected"
  end

(*Maps fully-typed metis terms to isabelle terms*)
fun hol_term_from_fol_FT ctxt fol_tm =
  let val _ = trace_msg (fn () => "hol_term_from_fol_FT: " ^
                                  Metis.Term.toString fol_tm)
      fun cvt (Metis.Term.Fn ("ti", [Metis.Term.Var v, _])) =
             (case strip_prefix schematic_var_prefix v of
                  SOME w =>  mk_var(w, dummyT)
                | NONE   => mk_var(v, dummyT))
        | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn ("=",[]), _])) =
            Const ("op =", HOLogic.typeT)
        | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn (x,[]), ty])) =
           (case strip_prefix const_prefix x of
                SOME c => Const (invert_const c, dummyT)
              | NONE => (*Not a constant. Is it a fixed variable??*)
            case strip_prefix fixed_var_prefix x of
                SOME v => Free (v, fol_type_to_isa ctxt ty)
              | NONE => raise Fail ("hol_term_from_fol_FT bad constant: " ^ x))
        | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn (".",[tm1,tm2]), _])) =
            cvt tm1 $ cvt tm2
        | cvt (Metis.Term.Fn (".",[tm1,tm2])) = (*untyped application*)
            cvt tm1 $ cvt tm2
        | cvt (Metis.Term.Fn ("{}", [arg])) = cvt arg   (*hBOOL*)
        | cvt (Metis.Term.Fn ("=", [tm1,tm2])) =
            list_comb(Const (@{const_name "op ="}, HOLogic.typeT), map cvt [tm1,tm2])
        | cvt (t as Metis.Term.Fn (x, [])) =
           (case strip_prefix const_prefix x of
                SOME c => Const (invert_const c, dummyT)
              | NONE => (*Not a constant. Is it a fixed variable??*)
            case strip_prefix fixed_var_prefix x of
                SOME v => Free (v, dummyT)
              | NONE => (trace_msg (fn () => "hol_term_from_fol_FT bad const: " ^ x);
                  hol_term_from_fol_PT ctxt t))
        | cvt t = (trace_msg (fn () => "hol_term_from_fol_FT bad term: " ^ Metis.Term.toString t);
            hol_term_from_fol_PT ctxt t)
  in fol_tm |> cvt end

fun hol_term_from_fol FT = hol_term_from_fol_FT
  | hol_term_from_fol _ = hol_term_from_fol_PT

fun hol_terms_from_fol ctxt mode skolem_somes fol_tms =
  let val ts = map (hol_term_from_fol mode ctxt) fol_tms
      val _ = trace_msg (fn () => "  calling type inference:")
      val _ = app (fn t => trace_msg (fn () => Syntax.string_of_term ctxt t)) ts
      val ts' = ts |> map (reveal_skolem_somes skolem_somes) |> infer_types ctxt
      val _ = app (fn t => trace_msg
                    (fn () => "  final term: " ^ Syntax.string_of_term ctxt t ^
                              "  of type  " ^ Syntax.string_of_typ ctxt (type_of t)))
                  ts'
  in  ts'  end;

fun mk_not (Const (@{const_name Not}, _) $ b) = b
  | mk_not b = HOLogic.mk_not b;

val metis_eq = Metis.Term.Fn ("=", []);

(* ------------------------------------------------------------------------- *)
(* FOL step Inference Rules                                                  *)
(* ------------------------------------------------------------------------- *)

(*for debugging only*)
fun print_thpair (fth,th) =
  (trace_msg (fn () => "=============================================");
   trace_msg (fn () => "Metis: " ^ Metis.Thm.toString fth);
   trace_msg (fn () => "Isabelle: " ^ Display.string_of_thm_without_context th));

fun lookth thpairs (fth : Metis.Thm.thm) =
  the (AList.lookup (uncurry Metis.Thm.equal) thpairs fth)
  handle Option =>
         raise Fail ("Failed to find a Metis theorem " ^ Metis.Thm.toString fth);

fun is_TrueI th = Thm.eq_thm(TrueI,th);

fun cterm_incr_types thy idx = cterm_of thy o (map_types (Logic.incr_tvar idx));

fun inst_excluded_middle thy i_atm =
  let val th = EXCLUDED_MIDDLE
      val [vx] = Term.add_vars (prop_of th) []
      val substs = [(cterm_of thy (Var vx), cterm_of thy i_atm)]
  in  cterm_instantiate substs th  end;

(* INFERENCE RULE: AXIOM *)
fun axiom_inf thpairs th = Thm.incr_indexes 1 (lookth thpairs th);
    (*This causes variables to have an index of 1 by default. SEE ALSO mk_var above.*)

(* INFERENCE RULE: ASSUME *)
fun assume_inf ctxt mode skolem_somes atm =
  inst_excluded_middle
    (ProofContext.theory_of ctxt)
    (singleton (hol_terms_from_fol ctxt mode skolem_somes) (Metis.Term.Fn atm))

(* INFERENCE RULE: INSTANTIATE (Subst). Type instantiations are ignored. Trying to reconstruct
   them admits new possibilities of errors, e.g. concerning sorts. Instead we try to arrange
   that new TVars are distinct and that types can be inferred from terms.*)
fun inst_inf ctxt mode skolem_somes thpairs fsubst th =
  let val thy = ProofContext.theory_of ctxt
      val i_th   = lookth thpairs th
      val i_th_vars = Term.add_vars (prop_of i_th) []
      fun find_var x = the (List.find (fn ((a,_),_) => a=x) i_th_vars)
      fun subst_translation (x,y) =
            let val v = find_var x
                (* We call "reveal_skolem_somes" and "infer_types" below. *)
                val t = hol_term_from_fol mode ctxt y
            in  SOME (cterm_of thy (Var v), t)  end
            handle Option =>
                (trace_msg (fn() => "List.find failed for the variable " ^ x ^
                                       " in " ^ Display.string_of_thm ctxt i_th);
                 NONE)
      fun remove_typeinst (a, t) =
            case strip_prefix schematic_var_prefix a of
                SOME b => SOME (b, t)
              | NONE   => case strip_prefix tvar_prefix a of
                SOME _ => NONE          (*type instantiations are forbidden!*)
              | NONE   => SOME (a,t)    (*internal Metis var?*)
      val _ = trace_msg (fn () => "  isa th: " ^ Display.string_of_thm ctxt i_th)
      val substs = map_filter remove_typeinst (Metis.Subst.toList fsubst)
      val (vars,rawtms) = ListPair.unzip (map_filter subst_translation substs)
      val tms = rawtms |> map (reveal_skolem_somes skolem_somes)
                       |> infer_types ctxt
      val ctm_of = cterm_incr_types thy (1 + Thm.maxidx_of i_th)
      val substs' = ListPair.zip (vars, map ctm_of tms)
      val _ = trace_msg (fn () =>
        cat_lines ("subst_translations:" ::
          (substs' |> map (fn (x, y) =>
            Syntax.string_of_term ctxt (term_of x) ^ " |-> " ^
            Syntax.string_of_term ctxt (term_of y)))));
  in cterm_instantiate substs' i_th end
  handle THM (msg, _, _) => raise METIS ("inst_inf", msg)
       | ERROR msg => raise METIS ("inst_inf", msg)

(* INFERENCE RULE: RESOLVE *)

(*Like RSN, but we rename apart only the type variables. Vars here typically have an index
  of 1, and the use of RSN would increase this typically to 3. Instantiations of those Vars
  could then fail. See comment on mk_var.*)
fun resolve_inc_tyvars(tha,i,thb) =
  let
      val tha = Drule.incr_type_indexes (1 + Thm.maxidx_of thb) tha
      val ths = Seq.list_of (Thm.bicompose false (false,tha,nprems_of tha) i thb)
  in
      case distinct Thm.eq_thm ths of
        [th] => th
      | _ => raise THM ("resolve_inc_tyvars: unique result expected", i, [tha,thb])
  end
  handle TERM (msg, _) => raise METIS ("resolve_inc_tyvars", msg)

fun resolve_inf ctxt mode skolem_somes thpairs atm th1 th2 =
  let
    val i_th1 = lookth thpairs th1 and i_th2 = lookth thpairs th2
    val _ = trace_msg (fn () => "  isa th1 (pos): " ^ Display.string_of_thm ctxt i_th1)
    val _ = trace_msg (fn () => "  isa th2 (neg): " ^ Display.string_of_thm ctxt i_th2)
  in
    if is_TrueI i_th1 then i_th2 (*Trivial cases where one operand is type info*)
    else if is_TrueI i_th2 then i_th1
    else
      let
        val i_atm = singleton (hol_terms_from_fol ctxt mode skolem_somes)
                              (Metis.Term.Fn atm)
        val _ = trace_msg (fn () => "  atom: " ^ Syntax.string_of_term ctxt i_atm)
        val prems_th1 = prems_of i_th1
        val prems_th2 = prems_of i_th2
        val index_th1 = get_index (mk_not i_atm) prems_th1
              handle Empty => raise Fail "Failed to find literal in th1"
        val _ = trace_msg (fn () => "  index_th1: " ^ Int.toString index_th1)
        val index_th2 = get_index i_atm prems_th2
              handle Empty => raise Fail "Failed to find literal in th2"
        val _ = trace_msg (fn () => "  index_th2: " ^ Int.toString index_th2)
    in  resolve_inc_tyvars (Meson.select_literal index_th1 i_th1, index_th2, i_th2)  end
  end;

(* INFERENCE RULE: REFL *)
val refl_x = cterm_of @{theory} (Var (hd (Term.add_vars (prop_of REFL_THM) [])));
val refl_idx = 1 + Thm.maxidx_of REFL_THM;

fun refl_inf ctxt mode skolem_somes t =
  let val thy = ProofContext.theory_of ctxt
      val i_t = singleton (hol_terms_from_fol ctxt mode skolem_somes) t
      val _ = trace_msg (fn () => "  term: " ^ Syntax.string_of_term ctxt i_t)
      val c_t = cterm_incr_types thy refl_idx i_t
  in  cterm_instantiate [(refl_x, c_t)] REFL_THM  end;

fun get_ty_arg_size _ (Const (@{const_name "op ="}, _)) = 0  (*equality has no type arguments*)
  | get_ty_arg_size thy (Const (c, _)) = (num_type_args thy c handle TYPE _ => 0)
  | get_ty_arg_size _ _ = 0;

(* INFERENCE RULE: EQUALITY *)
fun equality_inf ctxt mode skolem_somes (pos, atm) fp fr =
  let val thy = ProofContext.theory_of ctxt
      val m_tm = Metis.Term.Fn atm
      val [i_atm,i_tm] = hol_terms_from_fol ctxt mode skolem_somes [m_tm, fr]
      val _ = trace_msg (fn () => "sign of the literal: " ^ Bool.toString pos)
      fun replace_item_list lx 0 (_::ls) = lx::ls
        | replace_item_list lx i (l::ls) = l :: replace_item_list lx (i-1) ls
      fun path_finder_FO tm [] = (tm, Term.Bound 0)
        | path_finder_FO tm (p::ps) =
            let val (tm1,args) = strip_comb tm
                val adjustment = get_ty_arg_size thy tm1
                val p' = if adjustment > p then p else p-adjustment
                val tm_p = List.nth(args,p')
                  handle Subscript => raise METIS ("equality_inf", Int.toString p ^ " adj " ^
                    Int.toString adjustment  ^ " term " ^  Syntax.string_of_term ctxt tm)
                val _ = trace_msg (fn () => "path_finder: " ^ Int.toString p ^
                                      "  " ^ Syntax.string_of_term ctxt tm_p)
                val (r,t) = path_finder_FO tm_p ps
            in
                (r, list_comb (tm1, replace_item_list t p' args))
            end
      fun path_finder_HO tm [] = (tm, Term.Bound 0)
        | path_finder_HO (t$u) (0::ps) = (fn(x,y) => (x, y$u)) (path_finder_HO t ps)
        | path_finder_HO (t$u) (_::ps) = (fn(x,y) => (x, t$y)) (path_finder_HO u ps)
        | path_finder_HO tm ps =
          raise Fail ("equality_inf, path_finder_HO: path = " ^
                      space_implode " " (map Int.toString ps) ^
                      " isa-term: " ^  Syntax.string_of_term ctxt tm)
      fun path_finder_FT tm [] _ = (tm, Term.Bound 0)
        | path_finder_FT tm (0::ps) (Metis.Term.Fn ("ti", [t1, _])) =
            path_finder_FT tm ps t1
        | path_finder_FT (t$u) (0::ps) (Metis.Term.Fn (".", [t1, _])) =
            (fn(x,y) => (x, y$u)) (path_finder_FT t ps t1)
        | path_finder_FT (t$u) (1::ps) (Metis.Term.Fn (".", [_, t2])) =
            (fn(x,y) => (x, t$y)) (path_finder_FT u ps t2)
        | path_finder_FT tm ps t =
          raise Fail ("equality_inf, path_finder_FT: path = " ^
                      space_implode " " (map Int.toString ps) ^
                      " isa-term: " ^  Syntax.string_of_term ctxt tm ^
                      " fol-term: " ^ Metis.Term.toString t)
      fun path_finder FO tm ps _ = path_finder_FO tm ps
        | path_finder HO (tm as Const(@{const_name "op ="},_) $ _ $ _) (p::ps) _ =
             (*equality: not curried, as other predicates are*)
             if p=0 then path_finder_HO tm (0::1::ps)  (*select first operand*)
             else path_finder_HO tm (p::ps)        (*1 selects second operand*)
        | path_finder HO tm (_ :: ps) (Metis.Term.Fn ("{}", [_])) =
             path_finder_HO tm ps      (*if not equality, ignore head to skip hBOOL*)
        | path_finder FT (tm as Const(@{const_name "op ="}, _) $ _ $ _) (p::ps)
                            (Metis.Term.Fn ("=", [t1,t2])) =
             (*equality: not curried, as other predicates are*)
             if p=0 then path_finder_FT tm (0::1::ps)
                          (Metis.Term.Fn (".", [Metis.Term.Fn (".", [metis_eq,t1]), t2]))
                          (*select first operand*)
             else path_finder_FT tm (p::ps)
                   (Metis.Term.Fn (".", [metis_eq,t2]))
                   (*1 selects second operand*)
        | path_finder FT tm (_ :: ps) (Metis.Term.Fn ("{}", [t1])) = path_finder_FT tm ps t1
             (*if not equality, ignore head to skip the hBOOL predicate*)
        | path_finder FT tm ps t = path_finder_FT tm ps t  (*really an error case!*)
      fun path_finder_lit ((nt as Const (@{const_name Not}, _)) $ tm_a) idx =
            let val (tm, tm_rslt) = path_finder mode tm_a idx m_tm
            in (tm, nt $ tm_rslt) end
        | path_finder_lit tm_a idx = path_finder mode tm_a idx m_tm
      val (tm_subst, body) = path_finder_lit i_atm fp
      val tm_abs = Term.Abs("x", Term.type_of tm_subst, body)
      val _ = trace_msg (fn () => "abstraction: " ^ Syntax.string_of_term ctxt tm_abs)
      val _ = trace_msg (fn () => "i_tm: " ^ Syntax.string_of_term ctxt i_tm)
      val _ = trace_msg (fn () => "located term: " ^ Syntax.string_of_term ctxt tm_subst)
      val imax = maxidx_of_term (i_tm $ tm_abs $ tm_subst)  (*ill typed but gives right max*)
      val subst' = Thm.incr_indexes (imax+1) (if pos then subst_em else ssubst_em)
      val _ = trace_msg (fn () => "subst' " ^ Display.string_of_thm ctxt subst')
      val eq_terms = map (pairself (cterm_of thy))
        (ListPair.zip (OldTerm.term_vars (prop_of subst'), [tm_abs, tm_subst, i_tm]))
  in  cterm_instantiate eq_terms subst'  end;

val factor = Seq.hd o distinct_subgoals_tac;

fun step ctxt mode skolem_somes thpairs p =
  case p of
    (fol_th, Metis.Proof.Axiom _) => factor (axiom_inf thpairs fol_th)
  | (_, Metis.Proof.Assume f_atm) => assume_inf ctxt mode skolem_somes f_atm
  | (_, Metis.Proof.Subst (f_subst, f_th1)) =>
    factor (inst_inf ctxt mode skolem_somes thpairs f_subst f_th1)
  | (_, Metis.Proof.Resolve(f_atm, f_th1, f_th2)) =>
    factor (resolve_inf ctxt mode skolem_somes thpairs f_atm f_th1 f_th2)
  | (_, Metis.Proof.Refl f_tm) => refl_inf ctxt mode skolem_somes f_tm
  | (_, Metis.Proof.Equality (f_lit, f_p, f_r)) =>
    equality_inf ctxt mode skolem_somes f_lit f_p f_r

fun real_literal (_, (c, _)) = not (String.isPrefix class_prefix c);

(* FIXME: use "fold" instead *)
fun translate _ _ _ thpairs [] = thpairs
  | translate ctxt mode skolem_somes thpairs ((fol_th, inf) :: infpairs) =
      let val _ = trace_msg (fn () => "=============================================")
          val _ = trace_msg (fn () => "METIS THM: " ^ Metis.Thm.toString fol_th)
          val _ = trace_msg (fn () => "INFERENCE: " ^ Metis.Proof.inferenceToString inf)
          val th = Meson.flexflex_first_order (step ctxt mode skolem_somes
                                                    thpairs (fol_th, inf))
          val _ = trace_msg (fn () => "ISABELLE THM: " ^ Display.string_of_thm ctxt th)
          val _ = trace_msg (fn () => "=============================================")
          val n_metis_lits =
            length (filter real_literal (Metis.LiteralSet.toList (Metis.Thm.clause fol_th)))
      in
          if nprems_of th = n_metis_lits then ()
          else raise METIS ("translate", "Proof reconstruction has gone wrong.");
          translate ctxt mode skolem_somes ((fol_th, th) :: thpairs) infpairs
      end;

(*Determining which axiom clauses are actually used*)
fun used_axioms axioms (th, Metis.Proof.Axiom _) = SOME (lookth axioms th)
  | used_axioms _ _ = NONE;

(* ------------------------------------------------------------------------- *)
(* Translation of HO Clauses                                                 *)
(* ------------------------------------------------------------------------- *)

fun cnf_helper_theorem thy raw th =
  if raw then th else the_single (cnf_axiom thy th)

fun type_ext thy tms =
  let val subs = tfree_classes_of_terms tms
      val supers = tvar_classes_of_terms tms
      and tycons = type_consts_of_terms thy tms
      val (supers', arity_clauses) = make_arity_clauses thy tycons supers
      val classrel_clauses = make_classrel_clauses thy subs supers'
  in  map classrel_cls classrel_clauses @ map arity_cls arity_clauses
  end;

(* ------------------------------------------------------------------------- *)
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

type logic_map =
  {axioms: (Metis.Thm.thm * thm) list,
   tfrees: type_literal list,
   skolem_somes: (string * term) list}

fun const_in_metis c (pred, tm_list) =
  let
    fun in_mterm (Metis.Term.Var _) = false
      | in_mterm (Metis.Term.Fn (".", tm_list)) = exists in_mterm tm_list
      | in_mterm (Metis.Term.Fn (nm, tm_list)) = c=nm orelse exists in_mterm tm_list
  in  c = pred orelse exists in_mterm tm_list  end;

(*Extract TFree constraints from context to include as conjecture clauses*)
fun init_tfrees ctxt =
  let fun add ((a,i),s) Ts = if i = ~1 then TFree(a,s) :: Ts else Ts in
    Vartab.fold add (#2 (Variable.constraints_of ctxt)) []
    |> type_literals_for_types
  end;

(*transform isabelle type / arity clause to metis clause *)
fun add_type_thm [] lmap = lmap
  | add_type_thm ((ith, mth) :: cls) {axioms, tfrees, skolem_somes} =
      add_type_thm cls {axioms = (mth, ith) :: axioms, tfrees = tfrees,
                        skolem_somes = skolem_somes}

(*Insert non-logical axioms corresponding to all accumulated TFrees*)
fun add_tfrees {axioms, tfrees, skolem_somes} : logic_map =
     {axioms = map (rpair TrueI o metis_of_tfree) (distinct (op =) tfrees) @
               axioms,
      tfrees = tfrees, skolem_somes = skolem_somes}

fun string_of_mode FO = "FO"
  | string_of_mode HO = "HO"
  | string_of_mode FT = "FT"

val helpers =
  [("c_COMBI", (false, @{thms COMBI_def})),
   ("c_COMBK", (false, @{thms COMBK_def})),
   ("c_COMBB", (false, @{thms COMBB_def})),
   ("c_COMBC", (false, @{thms COMBC_def})),
   ("c_COMBS", (false, @{thms COMBS_def})),
   ("c_fequal", (false, @{thms fequal_imp_equal equal_imp_fequal})),
   ("c_True", (true, @{thms True_or_False})),
   ("c_False", (true, @{thms True_or_False})),
   ("c_If", (true, @{thms if_True if_False True_or_False}))]

(* Function to generate metis clauses, including comb and type clauses *)
fun build_map mode0 ctxt cls ths =
  let val thy = ProofContext.theory_of ctxt
      (*The modes FO and FT are sticky. HO can be downgraded to FO.*)
      fun set_mode FO = FO
        | set_mode HO =
          if forall (is_quasi_fol_theorem thy) (cls @ ths) then FO else HO
        | set_mode FT = FT
      val mode = set_mode mode0
      (*transform isabelle clause to metis clause *)
      fun add_thm is_conjecture ith {axioms, tfrees, skolem_somes} : logic_map =
        let
          val (mth, tfree_lits, skolem_somes) =
            hol_thm_to_fol is_conjecture ctxt mode (length axioms) skolem_somes
                           ith
        in
           {axioms = (mth, Meson.make_meta_clause ith) :: axioms,
            tfrees = union (op =) tfree_lits tfrees,
            skolem_somes = skolem_somes}
        end;
      val lmap = {axioms = [], tfrees = init_tfrees ctxt, skolem_somes = []}
                 |> fold (add_thm true) cls
                 |> add_tfrees
                 |> fold (add_thm false) ths
      val clause_lists = map (Metis.Thm.clause o #1) (#axioms lmap)
      fun is_used c =
        exists (Metis.LiteralSet.exists (const_in_metis c o #2)) clause_lists
      val lmap =
        if mode = FO then
          lmap
        else
          let
            val helper_ths =
              helpers |> filter (is_used o fst)
                      |> maps (fn (_, (raw, thms)) =>
                                  if mode = FT orelse not raw then
                                    map (cnf_helper_theorem @{theory} raw) thms
                                  else
                                    [])
          in lmap |> fold (add_thm false) helper_ths end
  in (mode, add_type_thm (type_ext thy (map prop_of (cls @ ths))) lmap) end

fun refute cls =
    Metis.Resolution.loop (Metis.Resolution.new Metis.Resolution.default cls);

fun is_false t = t aconv (HOLogic.mk_Trueprop HOLogic.false_const);

fun common_thm ths1 ths2 = exists (member Thm.eq_thm ths1) (map Meson.make_meta_clause ths2);


(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE mode ctxt cls ths0 =
  let val thy = ProofContext.theory_of ctxt
      val th_cls_pairs =
        map (fn th => (Thm.get_name_hint th, cnf_axiom thy th)) ths0
      val ths = maps #2 th_cls_pairs
      val _ = trace_msg (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
      val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) cls
      val _ = trace_msg (fn () => "THEOREM CLAUSES")
      val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) ths
      val (mode, {axioms, tfrees, skolem_somes}) = build_map mode ctxt cls ths
      val _ = if null tfrees then ()
              else (trace_msg (fn () => "TFREE CLAUSES");
                    app (fn TyLitFree (s, (s', _)) =>
                            trace_msg (fn _ => s ^ "(" ^ s' ^ ")")) tfrees)
      val _ = trace_msg (fn () => "CLAUSES GIVEN TO METIS")
      val thms = map #1 axioms
      val _ = app (fn th => trace_msg (fn () => Metis.Thm.toString th)) thms
      val _ = trace_msg (fn () => "mode = " ^ string_of_mode mode)
      val _ = trace_msg (fn () => "START METIS PROVE PROCESS")
  in
      case filter (is_false o prop_of) cls of
          false_th::_ => [false_th RS @{thm FalseE}]
        | [] =>
      case refute thms of
          Metis.Resolution.Contradiction mth =>
            let val _ = trace_msg (fn () => "METIS RECONSTRUCTION START: " ^
                          Metis.Thm.toString mth)
                val ctxt' = fold Variable.declare_constraints (map prop_of cls) ctxt
                             (*add constraints arising from converting goal to clause form*)
                val proof = Metis.Proof.proof mth
                val result = translate ctxt' mode skolem_somes axioms proof
                and used = map_filter (used_axioms axioms) proof
                val _ = trace_msg (fn () => "METIS COMPLETED...clauses actually used:")
                val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) used
                val unused = th_cls_pairs |> map_filter (fn (name, cls) =>
                  if common_thm used cls then NONE else SOME name)
            in
                if not (null cls) andalso not (common_thm used cls) then
                  warning "Metis: The assumptions are inconsistent."
                else
                  ();
                if not (null unused) then
                  warning ("Metis: Unused theorems: " ^ commas_quote unused
                           ^ ".")
                else
                  ();
                case result of
                    (_,ith)::_ =>
                        (trace_msg (fn () => "Success: " ^ Display.string_of_thm ctxt ith);
                         [ith])
                  | _ => (trace_msg (fn () => "Metis: No result");
                          raise METIS ("FOL_SOLVE", ""))
            end
        | Metis.Resolution.Satisfiable _ =>
            (trace_msg (fn () => "Metis: No first-order proof with the lemmas supplied");
             raise METIS ("FOL_SOLVE", ""))
  end;

fun generic_metis_tac mode ctxt ths i st0 =
  let val _ = trace_msg (fn () =>
        "Metis called with theorems " ^ cat_lines (map (Display.string_of_thm ctxt) ths))
  in
    if exists_type type_has_topsort (prop_of st0) then
      (warning ("Metis: Proof state contains the universal sort {}"); Seq.empty)
    else
      (Meson.MESON (maps neg_clausify)
                   (fn cls => resolve_tac (FOL_SOLVE mode ctxt cls ths) 1)
                   ctxt i
       THEN Meson_Tactic.expand_defs_tac st0) st0
     handle ERROR msg => raise METIS ("generic_metis_tac", msg)
  end
  handle METIS (loc, msg) =>
         if mode = HO then
           (warning ("Metis: Falling back on \"metisFT\".");
            generic_metis_tac FT ctxt ths i st0)
         else if msg = "" then
           Seq.empty
         else
           raise error ("Metis (" ^ loc ^ "): " ^ msg)

val metis_tac = generic_metis_tac HO
val metisF_tac = generic_metis_tac FO
val metisFT_tac = generic_metis_tac FT

fun method name mode =
  Method.setup name (Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (CHANGED_PROP o generic_metis_tac mode ctxt ths)))

val setup =
  type_lits_setup
  #> method @{binding metis} HO "Metis for FOL/HOL problems"
  #> method @{binding metisF} FO "Metis for FOL problems"
  #> method @{binding metisFT} FT
            "Metis for FOL/HOL problems with fully-typed translation"

end;
