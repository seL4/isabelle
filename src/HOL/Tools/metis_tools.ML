(*  Title:      HOL/Tools/metis_tools.ML
    Author:     Kong W. Susanto and Lawrence C. Paulson, CU Computer Laboratory
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)

signature METIS_TOOLS =
sig
  val type_lits: bool Config.T
  val metis_tac: Proof.context -> thm list -> int -> tactic
  val metisF_tac: Proof.context -> thm list -> int -> tactic
  val metisFT_tac: Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end

structure MetisTools: METIS_TOOLS =
struct

  structure Recon = ResReconstruct;

  val (type_lits, type_lits_setup) = Attrib.config_bool "metis_type_lits" true;

  datatype mode = FO | HO | FT  (*first-order, higher-order, fully-typed*)

  (* ------------------------------------------------------------------------- *)
  (* Useful Theorems                                                           *)
  (* ------------------------------------------------------------------------- *)
  val EXCLUDED_MIDDLE = rotate_prems 1 (read_instantiate @{context} [(("R", 0), "False")] notE);
  val REFL_THM = incr_indexes 2 (Meson.make_meta_clause refl);  (*Rename from 0,1*)
  val subst_em  = zero_var_indexes (subst RS EXCLUDED_MIDDLE);
  val ssubst_em = read_instantiate @{context} [(("t", 0), "?s"), (("s", 0), "?t")] (sym RS subst_em);

  (* ------------------------------------------------------------------------- *)
  (* Useful Functions                                                          *)
  (* ------------------------------------------------------------------------- *)

  (* match untyped terms*)
  fun untyped_aconv (Const(a,_))   (Const(b,_))   = (a=b)
    | untyped_aconv (Free(a,_))    (Free(b,_))    = (a=b)
    | untyped_aconv (Var((a,_),_)) (Var((b,_),_)) = (a=b)   (*the index is ignored!*)
    | untyped_aconv (Bound i)      (Bound j)      = (i=j)
    | untyped_aconv (Abs(a,_,t))  (Abs(b,_,u))    = (a=b) andalso untyped_aconv t u
    | untyped_aconv (t1$t2) (u1$u2)  = untyped_aconv t1 u1 andalso untyped_aconv t2 u2
    | untyped_aconv _              _              = false;

  (* Finding the relative location of an untyped term within a list of terms *)
  fun get_index lit =
    let val lit = Envir.eta_contract lit
        fun get n [] = raise Empty
          | get n (x::xs) = if untyped_aconv lit (Envir.eta_contract (HOLogic.dest_Trueprop x))
                            then n  else get (n+1) xs
    in get 1 end;

  (* ------------------------------------------------------------------------- *)
  (* HOL to FOL  (Isabelle to Metis)                                           *)
  (* ------------------------------------------------------------------------- *)

  fun fn_isa_to_met "equal" = "="
    | fn_isa_to_met x       = x;

  fun metis_lit b c args = (b, (c, args));

  fun hol_type_to_fol (ResClause.AtomV x) = Metis.Term.Var x
    | hol_type_to_fol (ResClause.AtomF x) = Metis.Term.Fn(x,[])
    | hol_type_to_fol (ResClause.Comp(tc,tps)) = Metis.Term.Fn(tc, map hol_type_to_fol tps);

  (*These two functions insert type literals before the real literals. That is the
    opposite order from TPTP linkup, but maybe OK.*)

  fun hol_term_to_fol_FO tm =
    case ResHolClause.strip_comb tm of
        (ResHolClause.CombConst(c,_,tys), tms) =>
          let val tyargs = map hol_type_to_fol tys
              val args   = map hol_term_to_fol_FO tms
          in Metis.Term.Fn (c, tyargs @ args) end
      | (ResHolClause.CombVar(v,_), []) => Metis.Term.Var v
      | _ => error "hol_term_to_fol_FO";

  fun hol_term_to_fol_HO (ResHolClause.CombVar(a, ty)) = Metis.Term.Var a
    | hol_term_to_fol_HO (ResHolClause.CombConst(a, ty, tylist)) =
        Metis.Term.Fn(fn_isa_to_met a, map hol_type_to_fol tylist)
    | hol_term_to_fol_HO (ResHolClause.CombApp(tm1,tm2)) =
         Metis.Term.Fn(".", map hol_term_to_fol_HO [tm1,tm2]);

  (*The fully-typed translation, to avoid type errors*)
  fun wrap_type (tm, ty) = Metis.Term.Fn("ti", [tm, hol_type_to_fol ty]);
  
  fun hol_term_to_fol_FT (ResHolClause.CombVar(a, ty)) = 
        wrap_type (Metis.Term.Var a, ty)
    | hol_term_to_fol_FT (ResHolClause.CombConst(a, ty, _)) =
        wrap_type (Metis.Term.Fn(fn_isa_to_met a, []), ty)
    | hol_term_to_fol_FT (tm as ResHolClause.CombApp(tm1,tm2)) =
         wrap_type (Metis.Term.Fn(".", map hol_term_to_fol_FT [tm1,tm2]),    
                    ResHolClause.type_of_combterm tm);

  fun hol_literal_to_fol FO (ResHolClause.Literal (pol, tm)) =  
        let val (ResHolClause.CombConst(p,_,tys), tms) = ResHolClause.strip_comb tm
            val tylits = if p = "equal" then [] else map hol_type_to_fol tys
            val lits = map hol_term_to_fol_FO tms
        in metis_lit pol (fn_isa_to_met p) (tylits @ lits) end
    | hol_literal_to_fol HO (ResHolClause.Literal (pol, tm)) =
       (case ResHolClause.strip_comb tm of
            (ResHolClause.CombConst("equal",_,_), tms) =>
              metis_lit pol "=" (map hol_term_to_fol_HO tms)
          | _ => metis_lit pol "{}" [hol_term_to_fol_HO tm])   (*hBOOL*)
    | hol_literal_to_fol FT (ResHolClause.Literal (pol, tm)) = 
       (case ResHolClause.strip_comb tm of
            (ResHolClause.CombConst("equal",_,_), tms) =>
              metis_lit pol "=" (map hol_term_to_fol_FT tms)
          | _ => metis_lit pol "{}" [hol_term_to_fol_FT tm])   (*hBOOL*);

  fun literals_of_hol_thm thy mode t =
        let val (lits, types_sorts) = ResHolClause.literals_of_term thy t
        in  (map (hol_literal_to_fol mode) lits, types_sorts) end;

  (*Sign should be "true" for conjecture type constraints, "false" for type lits in clauses.*)
  fun metis_of_typeLit pos (ResClause.LTVar (s,x))  = metis_lit pos s [Metis.Term.Var x]
    | metis_of_typeLit pos (ResClause.LTFree (s,x)) = metis_lit pos s [Metis.Term.Fn(x,[])];

  fun default_sort ctxt (TVar _) = false
    | default_sort ctxt (TFree(x,s)) = (s = Option.getOpt (Variable.def_sort ctxt (x,~1), []));

  fun metis_of_tfree tf =
    Metis.Thm.axiom (Metis.LiteralSet.singleton (metis_of_typeLit true tf));

  fun hol_thm_to_fol is_conjecture ctxt mode th =
    let val thy = ProofContext.theory_of ctxt
        val (mlits, types_sorts) =
               (literals_of_hol_thm thy mode o HOLogic.dest_Trueprop o prop_of) th
    in
        if is_conjecture then
            (Metis.Thm.axiom (Metis.LiteralSet.fromList mlits), ResClause.add_typs types_sorts)
        else
          let val tylits = ResClause.add_typs
                             (filter (not o default_sort ctxt) types_sorts)
              val mtylits = if Config.get ctxt type_lits
                            then map (metis_of_typeLit false) tylits else []
          in
            (Metis.Thm.axiom (Metis.LiteralSet.fromList(mtylits @ mlits)), [])
          end
    end;

  (* ARITY CLAUSE *)

  fun m_arity_cls (ResClause.TConsLit (c,t,args)) =
        metis_lit true (ResClause.make_type_class c) [Metis.Term.Fn(t, map Metis.Term.Var args)]
    | m_arity_cls (ResClause.TVarLit (c,str))     =
        metis_lit false (ResClause.make_type_class c) [Metis.Term.Var str];

  (*TrueI is returned as the Isabelle counterpart because there isn't any.*)
  fun arity_cls (ResClause.ArityClause{conclLit,premLits,...}) =
    (TrueI,
     Metis.Thm.axiom (Metis.LiteralSet.fromList (map m_arity_cls (conclLit :: premLits))));

  (* CLASSREL CLAUSE *)

  fun m_classrel_cls subclass superclass =
    [metis_lit false subclass [Metis.Term.Var "T"], metis_lit true superclass [Metis.Term.Var "T"]];

  fun classrel_cls (ResClause.ClassrelClause {axiom_name,subclass,superclass,...}) =
    (TrueI, Metis.Thm.axiom (Metis.LiteralSet.fromList (m_classrel_cls subclass superclass)));

  (* ------------------------------------------------------------------------- *)
  (* FOL to HOL  (Metis to Isabelle)                                           *)
  (* ------------------------------------------------------------------------- *)

 datatype term_or_type = Term of Term.term | Type of Term.typ;

  fun terms_of [] = []
    | terms_of (Term t :: tts) = t :: terms_of tts
    | terms_of (Type _ :: tts) = terms_of tts;

  fun types_of [] = []
    | types_of (Term (Term.Var((a,idx), T)) :: tts) =
        if String.isPrefix "_" a then
            (*Variable generated by Metis, which might have been a type variable.*)
            TVar(("'" ^ a, idx), HOLogic.typeS) :: types_of tts
        else types_of tts
    | types_of (Term _ :: tts) = types_of tts
    | types_of (Type T :: tts) = T :: types_of tts;

  fun apply_list rator nargs rands =
    let val trands = terms_of rands
    in  if length trands = nargs then Term (list_comb(rator, trands))
        else error
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
    in  TFree(ww, getOpt (Variable.def_sort ctxt (ww,~1), HOLogic.typeS))  end;

  (*Remove the "apply" operator from an HO term*)
  fun strip_happ args (Metis.Term.Fn(".",[t,u])) = strip_happ (u::args) t
    | strip_happ args x = (x, args);

  fun fol_type_to_isa ctxt (Metis.Term.Var v) = 
       (case Recon.strip_prefix ResClause.tvar_prefix v of
	    SOME w => Recon.make_tvar w
	  | NONE   => Recon.make_tvar v)
    | fol_type_to_isa ctxt (Metis.Term.Fn(x, tys)) =
       (case Recon.strip_prefix ResClause.tconst_prefix x of
	    SOME tc => Term.Type (Recon.invert_type_const tc, map (fol_type_to_isa ctxt) tys)
	  | NONE    => 
        case Recon.strip_prefix ResClause.tfree_prefix x of
	    SOME tf => mk_tfree ctxt tf
	  | NONE    => error ("fol_type_to_isa: " ^ x));

  (*Maps metis terms to isabelle terms*)
  fun fol_term_to_hol_RAW ctxt fol_tm =
    let val thy = ProofContext.theory_of ctxt
        val _ = Output.debug (fn () => "fol_term_to_hol: " ^ Metis.Term.toString fol_tm)
        fun tm_to_tt (Metis.Term.Var v) =
               (case Recon.strip_prefix ResClause.tvar_prefix v of
                    SOME w => Type (Recon.make_tvar w)
                  | NONE =>
                case Recon.strip_prefix ResClause.schematic_var_prefix v of
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
                             | _ => error "tm_to_tt: HO application"
              end
          | tm_to_tt (Metis.Term.Fn (fname, args)) = applic_to_tt (fname,args)
        and applic_to_tt ("=",ts) =
              Term (list_comb(Const ("op =", HOLogic.typeT), terms_of (map tm_to_tt ts)))
          | applic_to_tt (a,ts) =
              case Recon.strip_prefix ResClause.const_prefix a of
                  SOME b =>
                    let val c = Recon.invert_const b
                        val ntypes = Recon.num_typargs thy c
                        val nterms = length ts - ntypes
                        val tts = map tm_to_tt ts
                        val tys = types_of (List.take(tts,ntypes))
                        val ntyargs = Recon.num_typargs thy c
                    in if length tys = ntyargs then
                           apply_list (Const (c, dummyT)) nterms (List.drop(tts,ntypes))
                       else error ("Constant " ^ c ^ " expects " ^ Int.toString ntyargs ^
                                   " but gets " ^ Int.toString (length tys) ^
                                   " type arguments\n" ^
                                   cat_lines (map (Syntax.string_of_typ ctxt) tys) ^
                                   " the terms are \n" ^
                                   cat_lines (map (Syntax.string_of_term ctxt) (terms_of tts)))
                       end
                | NONE => (*Not a constant. Is it a type constructor?*)
              case Recon.strip_prefix ResClause.tconst_prefix a of
                  SOME b => Type (Term.Type(Recon.invert_type_const b, types_of (map tm_to_tt ts)))
                | NONE => (*Maybe a TFree. Should then check that ts=[].*)
              case Recon.strip_prefix ResClause.tfree_prefix a of
                  SOME b => Type (mk_tfree ctxt b)
                | NONE => (*a fixed variable? They are Skolem functions.*)
              case Recon.strip_prefix ResClause.fixed_var_prefix a of
                  SOME b =>
                    let val opr = Term.Free(b, HOLogic.typeT)
                    in  apply_list opr (length ts) (map tm_to_tt ts)  end
                | NONE => error ("unexpected metis function: " ^ a)
    in  case tm_to_tt fol_tm of Term t => t | _ => error "fol_tm_to_tt: Term expected"  end;

  (*Maps fully-typed metis terms to isabelle terms*)
  fun fol_term_to_hol_FT ctxt fol_tm =
    let val _ = Output.debug (fn () => "fol_term_to_hol_FT: " ^ Metis.Term.toString fol_tm)
        fun cvt (Metis.Term.Fn ("ti", [Metis.Term.Var v, ty])) =
               (case Recon.strip_prefix ResClause.schematic_var_prefix v of
                    SOME w =>  mk_var(w, dummyT)
                  | NONE   => mk_var(v, dummyT))
          | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn ("=",[]), ty])) = 
              Const ("op =", HOLogic.typeT)
          | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn (x,[]), ty])) =
             (case Recon.strip_prefix ResClause.const_prefix x of
                  SOME c => Const (Recon.invert_const c, dummyT)
                | NONE => (*Not a constant. Is it a fixed variable??*)
              case Recon.strip_prefix ResClause.fixed_var_prefix x of
                  SOME v => Free (v, fol_type_to_isa ctxt ty)
                | NONE => error ("fol_term_to_hol_FT bad constant: " ^ x))
          | cvt (Metis.Term.Fn ("ti", [Metis.Term.Fn (".",[tm1,tm2]), _])) =
              cvt tm1 $ cvt tm2
          | cvt (Metis.Term.Fn (".",[tm1,tm2])) = (*untyped application*)
              cvt tm1 $ cvt tm2
          | cvt (Metis.Term.Fn ("{}", [arg])) = cvt arg   (*hBOOL*)
          | cvt (Metis.Term.Fn ("=", [tm1,tm2])) = 
              list_comb(Const ("op =", HOLogic.typeT), map cvt [tm1,tm2])
          | cvt (t as Metis.Term.Fn (x, [])) = 
             (case Recon.strip_prefix ResClause.const_prefix x of
                  SOME c => Const (Recon.invert_const c, dummyT)
                | NONE => (*Not a constant. Is it a fixed variable??*)
              case Recon.strip_prefix ResClause.fixed_var_prefix x of
                  SOME v => Free (v, dummyT)
                | NONE =>  (Output.debug (fn () => "fol_term_to_hol_FT bad const: " ^ x); fol_term_to_hol_RAW ctxt t))
          | cvt t = (Output.debug (fn () => "fol_term_to_hol_FT bad term: " ^ Metis.Term.toString t); fol_term_to_hol_RAW ctxt t)
    in  cvt fol_tm   end;

  fun fol_term_to_hol ctxt FO = fol_term_to_hol_RAW ctxt
    | fol_term_to_hol ctxt HO = fol_term_to_hol_RAW ctxt
    | fol_term_to_hol ctxt FT = fol_term_to_hol_FT ctxt;

  fun fol_terms_to_hol ctxt mode fol_tms =
    let val ts = map (fol_term_to_hol ctxt mode) fol_tms
        val _ = Output.debug (fn () => "  calling type inference:")
        val _ = app (fn t => Output.debug (fn () => Syntax.string_of_term ctxt t)) ts
        val ts' = infer_types ctxt ts;
        val _ = app (fn t => Output.debug
                      (fn () => "  final term: " ^ Syntax.string_of_term ctxt t ^
                                "  of type  " ^ Syntax.string_of_typ ctxt (type_of t)))
                    ts'
    in  ts'  end;

  fun mk_not (Const ("Not", _) $ b) = b
    | mk_not b = HOLogic.mk_not b;

  val metis_eq = Metis.Term.Fn ("=", []);

  (* ------------------------------------------------------------------------- *)
  (* FOL step Inference Rules                                                  *)
  (* ------------------------------------------------------------------------- *)

  (*for debugging only*)
  fun print_thpair (fth,th) =
    (Output.debug (fn () => "=============================================");
     Output.debug (fn () => "Metis: " ^ Metis.Thm.toString fth);
     Output.debug (fn () => "Isabelle: " ^ Display.string_of_thm_without_context th));

  fun lookth thpairs (fth : Metis.Thm.thm) =
    valOf (AList.lookup (uncurry Metis.Thm.equal) thpairs fth)
    handle Option => error ("Failed to find a Metis theorem " ^ Metis.Thm.toString fth);

  fun is_TrueI th = Thm.eq_thm(TrueI,th);

  fun cterm_incr_types thy idx = cterm_of thy o (map_types (Logic.incr_tvar idx));

  fun inst_excluded_middle thy i_atm =
    let val th = EXCLUDED_MIDDLE
        val [vx] = Term.add_vars (prop_of th) []
        val substs = [(cterm_of thy (Var vx), cterm_of thy i_atm)]
    in  cterm_instantiate substs th  end;

  (* INFERENCE RULE: AXIOM *)
  fun axiom_inf ctxt thpairs th = incr_indexes 1 (lookth thpairs th);
      (*This causes variables to have an index of 1 by default. SEE ALSO mk_var above.*)

  (* INFERENCE RULE: ASSUME *)
  fun assume_inf ctxt mode atm =
    inst_excluded_middle
      (ProofContext.theory_of ctxt)
      (singleton (fol_terms_to_hol ctxt mode) (Metis.Term.Fn atm));

  (* INFERENCE RULE: INSTANTIATE (Subst). Type instantiations are ignored. Trying to reconstruct
     them admits new possibilities of errors, e.g. concerning sorts. Instead we try to arrange
     that new TVars are distinct and that types can be inferred from terms.*)
  fun inst_inf ctxt mode thpairs fsubst th =    
    let val thy = ProofContext.theory_of ctxt
        val i_th   = lookth thpairs th
        val i_th_vars = Term.add_vars (prop_of i_th) []
        fun find_var x = valOf (List.find (fn ((a,_),_) => a=x) i_th_vars)
        fun subst_translation (x,y) =
              let val v = find_var x
                  val t = fol_term_to_hol ctxt mode y (*we call infer_types below*)
              in  SOME (cterm_of thy (Var v), t)  end
              handle Option =>
                  (Output.debug (fn() => "List.find failed for the variable " ^ x ^
                                         " in " ^ Display.string_of_thm ctxt i_th);
                   NONE)
        fun remove_typeinst (a, t) =
              case Recon.strip_prefix ResClause.schematic_var_prefix a of
                  SOME b => SOME (b, t)
                | NONE   => case Recon.strip_prefix ResClause.tvar_prefix a of
                  SOME _ => NONE          (*type instantiations are forbidden!*)
                | NONE   => SOME (a,t)    (*internal Metis var?*)
        val _ = Output.debug (fn () => "  isa th: " ^ Display.string_of_thm ctxt i_th)
        val substs = List.mapPartial remove_typeinst (Metis.Subst.toList fsubst)
        val (vars,rawtms) = ListPair.unzip (List.mapPartial subst_translation substs)
        val tms = infer_types ctxt rawtms;
        val ctm_of = cterm_incr_types thy (1 + Thm.maxidx_of i_th)
        val substs' = ListPair.zip (vars, map ctm_of tms)
        val _ = Output.debug (fn () =>
          cat_lines ("subst_translations:" ::
            (substs' |> map (fn (x, y) =>
              Syntax.string_of_term ctxt (term_of x) ^ " |-> " ^
              Syntax.string_of_term ctxt (term_of y)))));
    in  cterm_instantiate substs' i_th  
        handle THM (msg, _, _) => error ("metis error (inst_inf): " ^ msg)
    end;

  (* INFERENCE RULE: RESOLVE *)

  (*Like RSN, but we rename apart only the type variables. Vars here typically have an index
    of 1, and the use of RSN would increase this typically to 3. Instantiations of those Vars
    could then fail. See comment on mk_var.*)
  fun resolve_inc_tyvars(tha,i,thb) =
    let val tha = Drule.incr_type_indexes (1 + Thm.maxidx_of thb) tha
	val ths = Seq.list_of (Thm.bicompose false (false,tha,nprems_of tha) i thb)
    in
	case distinct Thm.eq_thm ths of
	  [th] => th
	| _ => raise THM ("resolve_inc_tyvars: unique result expected", i, [tha,thb])
    end;

  fun resolve_inf ctxt mode thpairs atm th1 th2 =
    let
      val thy = ProofContext.theory_of ctxt
      val i_th1 = lookth thpairs th1 and i_th2 = lookth thpairs th2
      val _ = Output.debug (fn () => "  isa th1 (pos): " ^ Display.string_of_thm ctxt i_th1)
      val _ = Output.debug (fn () => "  isa th2 (neg): " ^ Display.string_of_thm ctxt i_th2)
    in
      if is_TrueI i_th1 then i_th2 (*Trivial cases where one operand is type info*)
      else if is_TrueI i_th2 then i_th1
      else
        let
          val i_atm = singleton (fol_terms_to_hol ctxt mode) (Metis.Term.Fn atm)
          val _ = Output.debug (fn () => "  atom: " ^ Syntax.string_of_term ctxt i_atm)
          val prems_th1 = prems_of i_th1
          val prems_th2 = prems_of i_th2
          val index_th1 = get_index (mk_not i_atm) prems_th1
                handle Empty => error "Failed to find literal in th1"
          val _ = Output.debug (fn () => "  index_th1: " ^ Int.toString index_th1)
          val index_th2 = get_index i_atm prems_th2
                handle Empty => error "Failed to find literal in th2"
          val _ = Output.debug (fn () => "  index_th2: " ^ Int.toString index_th2)
      in  resolve_inc_tyvars (Meson.select_literal index_th1 i_th1, index_th2, i_th2)  end
    end;

  (* INFERENCE RULE: REFL *)
  val refl_x = cterm_of @{theory} (Var (hd (Term.add_vars (prop_of REFL_THM) [])));
  val refl_idx = 1 + Thm.maxidx_of REFL_THM;

  fun refl_inf ctxt mode t =
    let val thy = ProofContext.theory_of ctxt
        val i_t = singleton (fol_terms_to_hol ctxt mode) t
        val _ = Output.debug (fn () => "  term: " ^ Syntax.string_of_term ctxt i_t)
        val c_t = cterm_incr_types thy refl_idx i_t
    in  cterm_instantiate [(refl_x, c_t)] REFL_THM  end;

  fun get_ty_arg_size thy (Const("op =",_)) = 0  (*equality has no type arguments*)
    | get_ty_arg_size thy (Const(c,_))      = (Recon.num_typargs thy c handle TYPE _ => 0)
    | get_ty_arg_size thy _      = 0;

  (* INFERENCE RULE: EQUALITY *)
  fun equality_inf ctxt mode thpairs (pos,atm) fp fr =
    let val thy = ProofContext.theory_of ctxt
        val m_tm = Metis.Term.Fn atm
        val [i_atm,i_tm] = fol_terms_to_hol ctxt mode [m_tm, fr]
        val _ = Output.debug (fn () => "sign of the literal: " ^ Bool.toString pos)
        fun replace_item_list lx 0 (l::ls) = lx::ls
          | replace_item_list lx i (l::ls) = l :: replace_item_list lx (i-1) ls
        fun path_finder_FO tm [] = (tm, Term.Bound 0)
          | path_finder_FO tm (p::ps) =
              let val (tm1,args) = Term.strip_comb tm
                  val adjustment = get_ty_arg_size thy tm1
                  val p' = if adjustment > p then p else p-adjustment
                  val tm_p = List.nth(args,p')
                    handle Subscript => error ("equality_inf: " ^ Int.toString p ^ " adj " ^
                      Int.toString adjustment  ^ " term " ^  Syntax.string_of_term ctxt tm)
                  val _ = Output.debug (fn () => "path_finder: " ^ Int.toString p ^
                                        "  " ^ Syntax.string_of_term ctxt tm_p)
		  val (r,t) = path_finder_FO tm_p ps
              in
                  (r, list_comb (tm1, replace_item_list t p' args)) 
              end
        fun path_finder_HO tm [] = (tm, Term.Bound 0)
          | path_finder_HO (t$u) (0::ps) = (fn(x,y) => (x, y$u)) (path_finder_HO t ps)
          | path_finder_HO (t$u) (p::ps) = (fn(x,y) => (x, t$y)) (path_finder_HO u ps)
        fun path_finder_FT tm [] _ = (tm, Term.Bound 0)
          | path_finder_FT tm (0::ps) (Metis.Term.Fn ("ti", [t1,t2])) = 
              path_finder_FT tm ps t1
          | path_finder_FT (t$u) (0::ps) (Metis.Term.Fn (".", [t1,t2])) = 
              (fn(x,y) => (x, y$u)) (path_finder_FT t ps t1)
          | path_finder_FT (t$u) (1::ps) (Metis.Term.Fn (".", [t1,t2])) = 
              (fn(x,y) => (x, t$y)) (path_finder_FT u ps t2)
          | path_finder_FT tm ps t = error ("equality_inf, path_finder_FT: path = " ^
                                          space_implode " " (map Int.toString ps) ^ 
                                          " isa-term: " ^  Syntax.string_of_term ctxt tm ^
                                          " fol-term: " ^ Metis.Term.toString t)
        fun path_finder FO tm ps _ = path_finder_FO tm ps
          | path_finder HO (tm as Const("op =",_) $ _ $ _) (p::ps) _ =
               (*equality: not curried, as other predicates are*)
               if p=0 then path_finder_HO tm (0::1::ps)  (*select first operand*)
               else path_finder_HO tm (p::ps)        (*1 selects second operand*)
          | path_finder HO tm (p::ps) (Metis.Term.Fn ("{}", [t1])) =
               path_finder_HO tm ps      (*if not equality, ignore head to skip hBOOL*)
          | path_finder FT (tm as Const("op =",_) $ _ $ _) (p::ps) 
                              (Metis.Term.Fn ("=", [t1,t2])) =
               (*equality: not curried, as other predicates are*)
               if p=0 then path_finder_FT tm (0::1::ps) 
                            (Metis.Term.Fn (".", [Metis.Term.Fn (".", [metis_eq,t1]), t2])) 
                            (*select first operand*)
               else path_finder_FT tm (p::ps) 
                     (Metis.Term.Fn (".", [metis_eq,t2])) 
                     (*1 selects second operand*)
          | path_finder FT tm (p::ps) (Metis.Term.Fn ("{}", [t1])) = path_finder_FT tm ps t1     
               (*if not equality, ignore head to skip the hBOOL predicate*)
          | path_finder FT tm ps t = path_finder_FT tm ps t  (*really an error case!*)
        fun path_finder_lit ((nt as Term.Const ("Not", _)) $ tm_a) idx =
              let val (tm, tm_rslt) = path_finder mode tm_a idx m_tm
              in (tm, nt $ tm_rslt) end
          | path_finder_lit tm_a idx = path_finder mode tm_a idx m_tm
        val (tm_subst, body) = path_finder_lit i_atm fp
        val tm_abs = Term.Abs("x", Term.type_of tm_subst, body)
        val _ = Output.debug (fn () => "abstraction: " ^ Syntax.string_of_term ctxt tm_abs)
        val _ = Output.debug (fn () => "i_tm: " ^ Syntax.string_of_term ctxt i_tm)
        val _ = Output.debug (fn () => "located term: " ^ Syntax.string_of_term ctxt tm_subst)
        val imax = maxidx_of_term (i_tm $ tm_abs $ tm_subst)  (*ill typed but gives right max*)
        val subst' = incr_indexes (imax+1) (if pos then subst_em else ssubst_em)
        val _ = Output.debug (fn () => "subst' " ^ Display.string_of_thm ctxt subst')
        val eq_terms = map (pairself (cterm_of thy))
                           (ListPair.zip (OldTerm.term_vars (prop_of subst'), [tm_abs, tm_subst, i_tm]))
    in  cterm_instantiate eq_terms subst'  end;

  val factor = Seq.hd o distinct_subgoals_tac;

  fun step ctxt mode thpairs (fol_th, Metis.Proof.Axiom _)                        =
        factor (axiom_inf ctxt thpairs fol_th)
    | step ctxt mode thpairs (_, Metis.Proof.Assume f_atm)                        =
        assume_inf ctxt mode f_atm
    | step ctxt mode thpairs (_, Metis.Proof.Subst(f_subst, f_th1))               =
        factor (inst_inf ctxt mode thpairs f_subst f_th1)
    | step ctxt mode thpairs (_, Metis.Proof.Resolve(f_atm, f_th1, f_th2))        =
        factor (resolve_inf ctxt mode thpairs f_atm f_th1 f_th2)
    | step ctxt mode thpairs (_, Metis.Proof.Refl f_tm)                           =
        refl_inf ctxt mode f_tm
    | step ctxt mode thpairs (_, Metis.Proof.Equality(f_lit, f_p, f_r)) =
        equality_inf ctxt mode thpairs f_lit f_p f_r;

  fun real_literal (b, (c, _)) = not (String.isPrefix ResClause.class_prefix c);

  fun translate mode _    thpairs [] = thpairs
    | translate mode ctxt thpairs ((fol_th, inf) :: infpairs) =
        let val _ = Output.debug (fn () => "=============================================")
            val _ = Output.debug (fn () => "METIS THM: " ^ Metis.Thm.toString fol_th)
            val _ = Output.debug (fn () => "INFERENCE: " ^ Metis.Proof.inferenceToString inf)
            val th = Meson.flexflex_first_order (step ctxt mode thpairs (fol_th, inf))
            val _ = Output.debug (fn () => "ISABELLE THM: " ^ Display.string_of_thm ctxt th)
            val _ = Output.debug (fn () => "=============================================")
            val n_metis_lits = length (filter real_literal (Metis.LiteralSet.toList (Metis.Thm.clause fol_th)))
        in
            if nprems_of th = n_metis_lits then ()
            else error "Metis: proof reconstruction has gone wrong";
            translate mode ctxt ((fol_th, th) :: thpairs) infpairs
        end;

  (*Determining which axiom clauses are actually used*)
  fun used_axioms axioms (th, Metis.Proof.Axiom _) = SOME (lookth axioms th)
    | used_axioms axioms _                         = NONE;

  (* ------------------------------------------------------------------------- *)
  (* Translation of HO Clauses                                                 *)
  (* ------------------------------------------------------------------------- *)

  fun cnf_th thy th = hd (ResAxioms.cnf_axiom thy th);

  val equal_imp_fequal' = cnf_th @{theory} @{thm equal_imp_fequal};
  val fequal_imp_equal' = cnf_th @{theory} @{thm fequal_imp_equal};

  val comb_I = cnf_th @{theory} ResHolClause.comb_I;
  val comb_K = cnf_th @{theory} ResHolClause.comb_K;
  val comb_B = cnf_th @{theory} ResHolClause.comb_B;
  val comb_C = cnf_th @{theory} ResHolClause.comb_C;
  val comb_S = cnf_th @{theory} ResHolClause.comb_S;

  fun type_ext thy tms =
    let val subs = ResAtp.tfree_classes_of_terms tms
        val supers = ResAtp.tvar_classes_of_terms tms
        and tycons = ResAtp.type_consts_of_terms thy tms
        val arity_clauses = ResClause.make_arity_clauses thy tycons supers
        val (supers',arity_clauses) = ResClause.make_arity_clauses thy tycons supers
        val classrel_clauses = ResClause.make_classrel_clauses thy subs supers'
    in  map classrel_cls classrel_clauses @ map arity_cls arity_clauses
    end;

  (* ------------------------------------------------------------------------- *)
  (* Logic maps manage the interface between HOL and first-order logic.        *)
  (* ------------------------------------------------------------------------- *)

  type logic_map =
    {axioms : (Metis.Thm.thm * Thm.thm) list,
     tfrees : ResClause.type_literal list};

  fun const_in_metis c (pol,(pred,tm_list)) =
    let
      fun in_mterm (Metis.Term.Var nm) = false
        | in_mterm (Metis.Term.Fn (".", tm_list)) = exists in_mterm tm_list
        | in_mterm (Metis.Term.Fn (nm, tm_list)) = c=nm orelse exists in_mterm tm_list
    in  c=pred orelse exists in_mterm tm_list  end;

  (*Extract TFree constraints from context to include as conjecture clauses*)
  fun init_tfrees ctxt =
    let fun add ((a,i),s) Ts = if i = ~1 then TFree(a,s) :: Ts else Ts
    in  ResClause.add_typs (Vartab.fold add (#2 (Variable.constraints_of ctxt)) []) end;

  (*transform isabelle type / arity clause to metis clause *)
  fun add_type_thm [] lmap = lmap
    | add_type_thm ((ith, mth) :: cls) {axioms, tfrees} =
        add_type_thm cls {axioms = (mth, ith) :: axioms,
                          tfrees = tfrees}

  (*Insert non-logical axioms corresponding to all accumulated TFrees*)
  fun add_tfrees {axioms, tfrees} : logic_map =
       {axioms = (map (fn tf => (metis_of_tfree tf, TrueI)) (distinct op= tfrees)) @ axioms,
        tfrees = tfrees};

  fun string_of_mode FO = "FO"
    | string_of_mode HO = "HO"
    | string_of_mode FT = "FT"

  (* Function to generate metis clauses, including comb and type clauses *)
  fun build_map mode0 ctxt cls ths =
    let val thy = ProofContext.theory_of ctxt
        (*The modes FO and FT are sticky. HO can be downgraded to FO.*)
	fun set_mode FO = FO
	  | set_mode HO = if forall (Meson.is_fol_term thy o prop_of) (cls@ths) then FO else HO
	  | set_mode FT = FT
        val mode = set_mode mode0 
	(*transform isabelle clause to metis clause *)
	fun add_thm is_conjecture (ith, {axioms, tfrees}) : logic_map =
	  let val (mth, tfree_lits) = hol_thm_to_fol is_conjecture ctxt mode ith
	  in
	     {axioms = (mth, Meson.make_meta_clause ith) :: axioms,
	      tfrees = tfree_lits union tfrees}
	  end;
        val lmap0 = List.foldl (add_thm true)
                          {axioms = [], tfrees = init_tfrees ctxt} cls
        val lmap = List.foldl (add_thm false) (add_tfrees lmap0) ths
        val clause_lists = map (Metis.Thm.clause o #1) (#axioms lmap)
        fun used c = exists (Metis.LiteralSet.exists (const_in_metis c)) clause_lists
        (*Now check for the existence of certain combinators*)
        val thI  = if used "c_COMBI" then [comb_I] else []
        val thK  = if used "c_COMBK" then [comb_K] else []
        val thB   = if used "c_COMBB" then [comb_B] else []
        val thC   = if used "c_COMBC" then [comb_C] else []
        val thS   = if used "c_COMBS" then [comb_S] else []
        val thEQ  = if used "c_fequal" then [fequal_imp_equal', equal_imp_fequal'] else []
        val lmap' = if mode=FO then lmap
                    else List.foldl (add_thm false) lmap (thEQ @ thS @ thC @ thB @ thK @ thI)
    in
        (mode, add_type_thm (type_ext thy (map prop_of (cls @ ths))) lmap')
    end;

  fun refute cls =
      Metis.Resolution.loop (Metis.Resolution.new Metis.Resolution.default cls);

  fun is_false t = t aconv (HOLogic.mk_Trueprop HOLogic.false_const);

  fun common_thm ths1 ths2 = exists (member Thm.eq_thm ths1) (map Meson.make_meta_clause ths2);

  exception METIS of string;

  (* Main function to start metis prove and reconstruction *)
  fun FOL_SOLVE mode ctxt cls ths0 =
    let val thy = ProofContext.theory_of ctxt
        val th_cls_pairs = map (fn th => (Thm.get_name_hint th, ResAxioms.cnf_axiom thy th)) ths0
        val ths = List.concat (map #2 th_cls_pairs)
        val _ = Output.debug (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
        val _ = app (fn th => Output.debug (fn () => Display.string_of_thm ctxt th)) cls
        val _ = Output.debug (fn () => "THEOREM CLAUSES")
        val _ = app (fn th => Output.debug (fn () => Display.string_of_thm ctxt th)) ths
        val (mode, {axioms,tfrees}) = build_map mode ctxt cls ths
        val _ = if null tfrees then ()
                else (Output.debug (fn () => "TFREE CLAUSES");
                      app (fn tf => Output.debug (fn _ => ResClause.tptp_of_typeLit true tf)) tfrees)
        val _ = Output.debug (fn () => "CLAUSES GIVEN TO METIS")
        val thms = map #1 axioms
        val _ = app (fn th => Output.debug (fn () => Metis.Thm.toString th)) thms
        val _ = Output.debug (fn () => "mode = " ^ string_of_mode mode)
        val _ = Output.debug (fn () => "START METIS PROVE PROCESS")
    in
        case List.filter (is_false o prop_of) cls of
            false_th::_ => [false_th RS @{thm FalseE}]
          | [] =>
        case refute thms of
            Metis.Resolution.Contradiction mth =>
              let val _ = Output.debug (fn () => "METIS RECONSTRUCTION START: " ^
                            Metis.Thm.toString mth)
                  val ctxt' = fold Variable.declare_constraints (map prop_of cls) ctxt
                               (*add constraints arising from converting goal to clause form*)
                  val proof = Metis.Proof.proof mth
                  val result = translate mode ctxt' axioms proof
                  and used = List.mapPartial (used_axioms axioms) proof
                  val _ = Output.debug (fn () => "METIS COMPLETED...clauses actually used:")
	          val _ = app (fn th => Output.debug (fn () => Display.string_of_thm ctxt th)) used
	          val unused = filter (fn (a,cls) => not (common_thm used cls)) th_cls_pairs
              in
                  if null unused then ()
                  else warning ("Metis: unused theorems " ^ commas_quote (map #1 unused));
                  case result of
                      (_,ith)::_ => 
                          (Output.debug (fn () => "success: " ^ Display.string_of_thm ctxt ith); 
                           [ith])
                    | _ => (Output.debug (fn () => "Metis: no result"); 
                            [])
              end
          | Metis.Resolution.Satisfiable _ => 
	      (Output.debug (fn () => "Metis: No first-order proof with the lemmas supplied"); 
	       [])
    end;

  fun metis_general_tac mode ctxt ths i st0 =
    let val _ = Output.debug (fn () =>
          "Metis called with theorems " ^ cat_lines (map (Display.string_of_thm ctxt) ths))
    in
       if exists_type ResAxioms.type_has_empty_sort (prop_of st0)  
       then (warning "Proof state contains the empty sort"; Seq.empty)
       else 
	 (Meson.MESON ResAxioms.neg_clausify
	   (fn cls => resolve_tac (FOL_SOLVE mode ctxt cls ths) 1) ctxt i
	  THEN ResAxioms.expand_defs_tac st0) st0
    end
    handle METIS s => (warning ("Metis: " ^ s); Seq.empty);

  val metis_tac = metis_general_tac HO;
  val metisF_tac = metis_general_tac FO;
  val metisFT_tac = metis_general_tac FT;

  fun method name mode comment = Method.setup name (Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (CHANGED_PROP o metis_general_tac mode ctxt ths))) comment;

  val setup =
    type_lits_setup #>
    method @{binding metis} HO "METIS for FOL & HOL problems" #>
    method @{binding metisF} FO "METIS for FOL problems" #>
    method @{binding metisFT} FT "METIS With-fully typed translation" #>
    Method.setup @{binding finish_clausify}
      (Scan.succeed (K (SIMPLE_METHOD (ResAxioms.expand_defs_tac refl))))
      "cleanup after conversion to clauses";

end;
