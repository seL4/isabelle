(*  Title:      Pure/Proof/proof_syntax.ML
    Author:     Stefan Berghofer, TU Muenchen

Function for parsing and printing proof terms.
*)

signature PROOF_SYNTAX =
sig
  val add_proof_syntax: theory -> theory
  val proof_of_term: theory -> bool -> term -> Proofterm.proof
  val cterm_of_proof: theory -> Proofterm.proof -> cterm * (cterm -> Proofterm.proof)
  val read_term: theory -> bool -> typ -> string -> term
  val read_proof: theory -> bool -> bool -> string -> Proofterm.proof
  val proof_syntax: Proofterm.proof -> theory -> theory
  val proof_of: Proof.context -> bool -> thm -> Proofterm.proof
  val pretty_proof: Proof.context -> Proofterm.proof -> Pretty.T
  val pretty_clean_proof_of: Proof.context -> bool -> thm -> Pretty.T
end;

structure Proof_Syntax : PROOF_SYNTAX =
struct

(**** add special syntax for embedding proof terms ****)

val proofT = Proofterm.proofT;

local

val paramT = Type ("param", []);
val paramsT = Type ("params", []);
val idtT = Type ("idt", []);
val aT = Term.aT [];

fun mixfix (sy, ps, p) = Mixfix (Input.string sy, ps, p, Position.no_range);

in

fun add_proof_syntax thy =
  thy
  |> Sign.root_path
  |> Sign.set_defsort []
  |> Sign.add_nonterminals_global
    [Binding.make ("param", \<^here>),
     Binding.make ("params", \<^here>)]
  |> Sign.add_syntax Syntax.mode_default
    [("_Lam", [paramsT, proofT] ---> proofT, mixfix ("(1\<^bold>\<lambda>_./ _)", [0, 3], 3)),
     ("_Lam0", [paramT, paramsT] ---> paramsT, mixfix ("_/ _", [1, 0], 0)),
     ("_Lam0", [idtT, paramsT] ---> paramsT, mixfix ("_/ _", [1, 0], 0)),
     ("_Lam1", [idtT, propT] ---> paramT, mixfix ("_: _", [0, 0], 0)),
     ("", paramT --> paramT, Mixfix.mixfix "'(_')"),
     ("", idtT --> paramsT, Mixfix.mixfix "_"),
     ("", paramT --> paramsT, Mixfix.mixfix "_"),
     (Lexicon.mark_const "Pure.Appt", [proofT, aT] ---> proofT, mixfix ("(1_ \<cdot>/ _)", [4, 5], 4)),
     (Lexicon.mark_const "Pure.AppP", [proofT, proofT] ---> proofT, mixfix ("(1_ \<bullet>/ _)", [4, 5], 4)),
     (Lexicon.mark_const "Pure.MinProof", proofT, Mixfix.mixfix "?")]
  |> Sign.add_trrules (map Syntax.Parse_Print_Rule
    [(Ast.mk_appl (Ast.Constant "_Lam")
        [Ast.mk_appl (Ast.Constant "_Lam0")
          [Ast.Variable "l", Ast.Variable "m"], Ast.Variable "A"],
      Ast.mk_appl (Ast.Constant "_Lam")
        [Ast.Variable "l",
          Ast.mk_appl (Ast.Constant "_Lam") [Ast.Variable "m", Ast.Variable "A"]]),
     (Ast.mk_appl (Ast.Constant "_Lam")
        [Ast.mk_appl (Ast.Constant "_Lam1")
          [Ast.Variable "x", Ast.Variable "A"], Ast.Variable "B"],
      Ast.mk_appl (Ast.Constant (Lexicon.mark_const "Pure.AbsP")) [Ast.Variable "A",
        (Ast.mk_appl (Ast.Constant "_abs") [Ast.Variable "x", Ast.Variable "B"])]),
     (Ast.mk_appl (Ast.Constant "_Lam") [Ast.Variable "x", Ast.Variable "A"],
      Ast.mk_appl (Ast.Constant (Lexicon.mark_const "Pure.Abst"))
        [(Ast.mk_appl (Ast.Constant "_abs") [Ast.Variable "x", Ast.Variable "A"])])]);

end;


(** constants for theorems and axioms **)

fun add_proof_atom_consts names thy =
  thy
  |> Sign.root_path
  |> Sign.add_consts (map (fn name => (Binding.qualified_name name, proofT, NoSyn)) names);


(**** translation between proof terms and pure terms ****)

fun proof_of_term thy ty =
  let
    val thms = Global_Theory.all_thms_of thy true;
    val axms = Theory.all_axioms_of thy;

    fun mk_term t = (if ty then I else map_types (K dummyT))
      (Term.no_dummy_patterns t);

    fun prf_of [] (Bound i) = PBound i
      | prf_of Ts (Const (s, Type ("Pure.proof", _))) =
          Proofterm.change_type (if ty then SOME Ts else NONE)
            (case Long_Name.explode s of
               "axm" :: xs =>
                 let
                   val name = Long_Name.implode xs;
                   val prop = (case AList.lookup (op =) axms name of
                       SOME prop => prop
                     | NONE => error ("Unknown axiom " ^ quote name))
                 in PAxm (name, prop, NONE) end
             | "thm" :: xs =>
                 let val name = Long_Name.implode xs;
                 in (case AList.lookup (op =) thms name of
                     SOME thm =>
                      fst (Proofterm.strip_combt (fst (Proofterm.strip_combP (Thm.proof_of thm))))
                   | NONE => error ("Unknown theorem " ^ quote name))
                 end
             | _ => error ("Illegal proof constant name: " ^ quote s))
      | prf_of Ts (Const ("Pure.OfClass", _) $ Const (c_class, _)) =
          (case try Logic.class_of_const c_class of
            SOME c =>
              Proofterm.change_type (if ty then SOME Ts else NONE)
                (OfClass (TVar ((Name.aT, 0), []), c))
          | NONE => error ("Bad class constant: " ^ quote c_class))
      | prf_of Ts (Const ("Pure.Hyp", _) $ prop) = Hyp prop
      | prf_of Ts (v as Var ((_, Type ("Pure.proof", _)))) = Hyp v
      | prf_of [] (Const ("Pure.Abst", _) $ Abs (s, T, prf)) =
          if T = proofT then
            error ("Term variable abstraction may not bind proof variable " ^ quote s)
          else Abst (s, if ty then SOME T else NONE,
            Proofterm.incr_pboundvars (~1) 0 (prf_of [] prf))
      | prf_of [] (Const ("Pure.AbsP", _) $ t $ Abs (s, _, prf)) =
          AbsP (s, case t of
                Const ("Pure.dummy_pattern", _) => NONE
              | _ $ Const ("Pure.dummy_pattern", _) => NONE
              | _ => SOME (mk_term t),
            Proofterm.incr_pboundvars 0 (~1) (prf_of [] prf))
      | prf_of [] (Const ("Pure.AppP", _) $ prf1 $ prf2) =
          prf_of [] prf1 %% prf_of [] prf2
      | prf_of Ts (Const ("Pure.Appt", _) $ prf $ Const ("Pure.type", Type (_, [T]))) =
          prf_of (T::Ts) prf
      | prf_of [] (Const ("Pure.Appt", _) $ prf $ t) = prf_of [] prf %
          (case t of Const ("Pure.dummy_pattern", _) => NONE | _ => SOME (mk_term t))
      | prf_of _ t = error ("Not a proof term:\n" ^
          Syntax.string_of_term_global thy t)

  in prf_of [] end;


fun cterm_of_proof thy prf =
  let
    val thm_names = map fst (Global_Theory.all_thms_of thy true);
    val axm_names = map fst (Theory.all_axioms_of thy);
    val thy' = thy
      |> add_proof_syntax
      |> add_proof_atom_consts
        (map (Long_Name.append "axm") axm_names @ map (Long_Name.append "thm") thm_names);
  in
    (Thm.global_cterm_of thy' (Proofterm.term_of_proof prf), proof_of_term thy true o Thm.term_of)
  end;

fun read_term thy topsort =
  let
    val thm_names = filter_out (fn s => s = "") (map fst (Global_Theory.all_thms_of thy true));
    val axm_names = map fst (Theory.all_axioms_of thy);
    val ctxt = thy
      |> add_proof_syntax
      |> add_proof_atom_consts
        (map (Long_Name.append "axm") axm_names @ map (Long_Name.append "thm") thm_names)
      |> Proof_Context.init_global
      |> Proof_Context.allow_dummies
      |> Proof_Context.set_mode Proof_Context.mode_schematic
      |> topsort ?
        (Proof_Context.set_defsort [] #>
         Config.put Type_Infer.object_logic false #>
         Config.put Type_Infer_Context.const_sorts false);
  in
    fn ty => fn s =>
      (if ty = propT then Syntax.parse_prop else Syntax.parse_term) ctxt s
      |> Type.constraint ty |> Syntax.check_term ctxt
  end;

fun read_proof thy topsort =
  let val rd = read_term thy topsort proofT
  in fn ty => fn s => proof_of_term thy ty (Logic.varify_global (rd s)) end;

fun proof_syntax prf =
  let
    val thm_names = Symtab.keys (Proofterm.fold_proof_atoms true
      (fn PThm (_, ((name, _, _), _)) => if name <> "" then Symtab.update (name, ()) else I
        | _ => I) [prf] Symtab.empty);
    val axm_names = Symtab.keys (Proofterm.fold_proof_atoms true
      (fn PAxm (name, _, _) => Symtab.update (name, ()) | _ => I) [prf] Symtab.empty);
  in
    add_proof_syntax #>
    add_proof_atom_consts
      (map (Long_Name.append "thm") thm_names @ map (Long_Name.append "axm") axm_names)
  end;

fun proof_of ctxt full raw_thm =
  let
    val thm = Thm.transfer' ctxt raw_thm;
    val prop = Thm.full_prop_of thm;
    val prf = Thm.proof_of thm;
    val prf' =
      (case Proofterm.strip_combt (fst (Proofterm.strip_combP prf)) of
        (PThm (_, ((_, prop', _), body)), _) =>
          if prop = prop' then Proofterm.join_proof body else prf
      | _ => prf)
  in if full then Reconstruct.reconstruct_proof ctxt prop prf' else prf' end;

fun pretty_proof ctxt prf =
  Proof_Context.pretty_term_abbrev
    (Proof_Context.transfer (proof_syntax prf (Proof_Context.theory_of ctxt)) ctxt)
    (Proofterm.term_of_proof prf);

fun pretty_clean_proof_of ctxt full thm =
  pretty_proof ctxt (Reconstruct.clean_proof_of ctxt full thm);

end;
