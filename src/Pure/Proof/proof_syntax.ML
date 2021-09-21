(*  Title:      Pure/Proof/proof_syntax.ML
    Author:     Stefan Berghofer, TU Muenchen

Function for parsing and printing proof terms.
*)

signature PROOF_SYNTAX =
sig
  val add_proof_syntax: theory -> theory
  val term_of_proof: proof -> term
  val proof_of_term: theory -> bool -> term -> Proofterm.proof
  val read_term: theory -> bool -> typ -> string -> term
  val read_proof: theory -> bool -> bool -> string -> Proofterm.proof
  val proof_syntax: Proofterm.proof -> theory -> theory
  val proof_of: bool -> thm -> Proofterm.proof
  val pretty_proof: Proof.context -> Proofterm.proof -> Pretty.T
  val pretty_proof_boxes_of: Proof.context ->
    {full: bool, preproc: theory -> proof -> proof} -> thm -> Pretty.T
  val standard_proof_of: {full: bool, expand_name: Proofterm.thm_header -> string option} ->
    thm -> Proofterm.proof
  val pretty_standard_proof_of: Proof.context -> bool -> thm -> Pretty.T
end;

structure Proof_Syntax : PROOF_SYNTAX =
struct

(**** add special syntax for embedding proof terms ****)

val proofT = Type ("Pure.proof", []);

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
  |> Sign.syntax true Syntax.mode_default
    [("_Lam", [paramsT, proofT] ---> proofT, mixfix ("(1\<^bold>\<lambda>_./ _)", [0, 3], 3)),
     ("_Lam0", [paramT, paramsT] ---> paramsT, mixfix ("_/ _", [1, 0], 0)),
     ("_Lam0", [idtT, paramsT] ---> paramsT, mixfix ("_/ _", [1, 0], 0)),
     ("_Lam1", [idtT, propT] ---> paramT, mixfix ("_: _", [0, 0], 0)),
     ("", paramT --> paramT, Mixfix.mixfix "'(_')"),
     ("", idtT --> paramsT, Mixfix.mixfix "_"),
     ("", paramT --> paramsT, Mixfix.mixfix "_"),
     (Lexicon.mark_const "Pure.Appt", [proofT, aT] ---> proofT, mixfix ("(1_ \<cdot>/ _)", [4, 5], 4)),
     (Lexicon.mark_const "Pure.AppP", [proofT, proofT] ---> proofT, mixfix ("(1_ \<bullet>/ _)", [4, 5], 4)),
     (Lexicon.mark_const "Pure.MinProof", proofT, Mixfix.mixfix "\<^bold>?")]
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



(** proof terms as pure terms **)

(* term_of_proof *)

local

val AbsPt = Const ("Pure.AbsP", propT --> (proofT --> proofT) --> proofT);
val AppPt = Const ("Pure.AppP", proofT --> proofT --> proofT);
val Hypt = Const ("Pure.Hyp", propT --> proofT);
val Oraclet = Const ("Pure.Oracle", propT --> proofT);
val MinProoft = Const ("Pure.MinProof", proofT);

fun AppT T prf =
  Const ("Pure.Appt", proofT --> Term.itselfT T --> proofT) $ prf $ Logic.mk_type T;

fun PClasst (T, c) =
  let val U = Term.itselfT T --> propT
  in Const ("Pure.PClass", U --> proofT) $ Const (Logic.const_of_class c, U) end;

fun term_of _ (PThm ({serial = i, name, types = Ts, ...}, _)) =
      fold AppT (these Ts)
        (Const (Long_Name.append "thm" (if name = "" then string_of_int i else name), proofT))
  | term_of _ (PAxm (name, _, Ts)) =
      fold AppT (these Ts) (Const (Long_Name.append "axm" name, proofT))
  | term_of _ (PClass (T, c)) = AppT T (PClasst (T, c))
  | term_of _ (PBound i) = Bound i
  | term_of Ts (Abst (s, opT, prf)) =
      let val T = the_default dummyT opT in
        Const ("Pure.Abst", (T --> proofT) --> proofT) $
          Abs (s, T, term_of (T::Ts) (Proofterm.incr_pboundvars 1 0 prf))
      end
  | term_of Ts (AbsP (s, t, prf)) =
      AbsPt $ the_default Term.dummy_prop t $
        Abs (s, proofT, term_of (proofT::Ts) (Proofterm.incr_pboundvars 0 1 prf))
  | term_of Ts (prf1 %% prf2) =
      AppPt $ term_of Ts prf1 $ term_of Ts prf2
  | term_of Ts (prf % opt) =
      let
        val t = the_default Term.dummy opt;
        val T = fastype_of1 (Ts, t) handle TERM _ => dummyT;
      in Const ("Pure.Appt", proofT --> T --> proofT) $ term_of Ts prf $ t end
  | term_of _ (Hyp t) = Hypt $ t
  | term_of _ (Oracle (_, t, _)) = Oraclet $ t
  | term_of _ MinProof = MinProoft;

in

val term_of_proof = term_of [];

end;


(* proof_of_term *)

fun proof_of_term thy ty =
  let
    val thms = Global_Theory.all_thms_of thy true;
    val axms = Theory.all_axioms_of thy;

    fun mk_term t = (if ty then I else map_types (K dummyT))
      (Term.no_dummy_patterns t);

    fun prf_of [] (Bound i) = PBound i
      | prf_of Ts (Const (s, Type ("Pure.proof", _))) =
          Proofterm.change_types (if ty then SOME Ts else NONE)
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
      | prf_of Ts (Const ("Pure.PClass", _) $ Const (c_class, _)) =
          (case try Logic.class_of_const c_class of
            SOME c =>
              Proofterm.change_types (if ty then SOME Ts else NONE)
                (PClass (TVar ((Name.aT, 0), []), c))
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
      | prf_of Ts (Const ("Pure.Appt", _) $ prf $ Const ("Pure.type", Type ("itself", [T]))) =
          prf_of (T::Ts) prf
      | prf_of [] (Const ("Pure.Appt", _) $ prf $ t) = prf_of [] prf %
          (case t of Const ("Pure.dummy_pattern", _) => NONE | _ => SOME (mk_term t))
      | prf_of _ t = error ("Not a proof term:\n" ^
          Syntax.string_of_term_global thy t)

  in prf_of [] end;


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
      (fn PThm ({name, ...}, _) => if name <> "" then Symtab.update (name, ()) else I
        | _ => I) [prf] Symtab.empty);
    val axm_names = Symtab.keys (Proofterm.fold_proof_atoms true
      (fn PAxm (name, _, _) => Symtab.update (name, ()) | _ => I) [prf] Symtab.empty);
  in
    add_proof_syntax #>
    add_proof_atom_consts
      (map (Long_Name.append "thm") thm_names @ map (Long_Name.append "axm") axm_names)
  end;

fun proof_of full thm =
  let
    val thy = Thm.theory_of_thm thm;
    val prop = Thm.full_prop_of thm;
    val prf = Thm.proof_of thm;
  in
    (case fst (Proofterm.strip_combt (fst (Proofterm.strip_combP prf))) of
      PThm ({prop = prop', ...}, thm_body) =>
        if prop = prop' then Proofterm.thm_body_proof_raw thm_body else prf
    | _ => prf)
    |> full ? Proofterm.reconstruct_proof thy prop
  end;

fun pretty_proof ctxt prf =
  Proof_Context.pretty_term_abbrev
    (Proof_Context.transfer (proof_syntax prf (Proof_Context.theory_of ctxt)) ctxt)
    (term_of_proof prf);

fun pretty_proof_boxes_of ctxt {full, preproc} thm =
  let
    val thy = Proof_Context.theory_of ctxt;
    val selection =
      {included = Proofterm.this_id (Thm.derivation_id thm),
       excluded = is_some o Global_Theory.lookup_thm_id thy}
  in
    Proofterm.proof_boxes selection [Thm.proof_of thm]
    |> map (fn ({serial = i, pos, prop, ...}, proof) =>
        let
          val proof' = proof
            |> Proofterm.reconstruct_proof thy prop
            |> preproc thy
            |> not full ? Proofterm.shrink_proof
            |> Proofterm.forall_intr_variables prop;
          val prop' = prop
            |> Proofterm.forall_intr_variables_term;
          val name = Long_Name.append "thm" (string_of_int i);
        in
          Pretty.item
           [Pretty.str (name ^ Position.here_list pos ^ ":"), Pretty.brk 1,
            Syntax.pretty_term ctxt prop', Pretty.fbrk, pretty_proof ctxt proof']
        end)
    |> Pretty.chunks
  end;


(* standardized proofs *)

fun standard_proof_of {full, expand_name} thm =
  let val thy = Thm.theory_of_thm thm in
    Thm.reconstruct_proof_of thm
    |> Proofterm.expand_proof thy expand_name
    |> Proofterm.rewrite_proof thy ([], Proof_Rewrite_Rules.rprocs true)
    |> Proofterm.no_thm_proofs
    |> not full ? Proofterm.shrink_proof
  end;

fun pretty_standard_proof_of ctxt full thm =
  pretty_proof ctxt (standard_proof_of {full = full, expand_name = Thm.expand_name thm} thm);

end;
