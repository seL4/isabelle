(*  Title:      Pure/Proof/proof_syntax.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Function for parsing and printing proof terms.
*)

signature PROOF_SYNTAX =
sig
  val proofT : typ
  val add_proof_syntax : Sign.sg -> Sign.sg
  val disambiguate_names : theory -> Proofterm.proof ->
    Proofterm.proof * Proofterm.proof Symtab.table
  val proof_of_term : theory -> Proofterm.proof Symtab.table ->
    bool -> term -> Proofterm.proof
  val term_of_proof : Proofterm.proof -> term
  val cterm_of_proof : theory -> Proofterm.proof -> cterm * (cterm -> Proofterm.proof)
  val read_term : theory -> typ -> string -> term
  val read_proof : theory -> bool -> string -> Proofterm.proof
  val pretty_proof : Sign.sg -> Proofterm.proof -> Pretty.T
  val pretty_proof_of : bool -> thm -> Pretty.T
  val print_proof_of : bool -> thm -> unit
end;

structure ProofSyntax : PROOF_SYNTAX =
struct

open Proofterm;

(**** add special syntax for embedding proof terms ****)

val proofT = Type ("proof", []);
val paramT = Type ("param", []);
val paramsT = Type ("params", []);
val idtT = Type ("idt", []);
val aT = TFree ("'a", ["logic"]);

(** constants for theorems and axioms **)

fun add_prefix a b = NameSpace.pack (a :: NameSpace.unpack b);

fun add_proof_atom_consts names sg = Sign.add_consts_i
  (map (fn name => (name, proofT, NoSyn)) names) (Sign.add_path "//" sg);

(** constants for application and abstraction **)

fun add_proof_syntax sg =
  sg
  |> Sign.copy
  |> Sign.add_path "/"
  |> Sign.add_defsort_i ["logic"]
  |> Sign.add_types [("proof", 0, NoSyn)]
  |> Sign.add_arities [("proof", [], "logic")]
  |> Sign.add_consts_i
      [("Appt", [proofT, aT] ---> proofT, Mixfix ("(1_ %/ _)", [4, 5], 4)),
       ("AppP", [proofT, proofT] ---> proofT, Mixfix ("(1_ %%/ _)", [4, 5], 4)),
       ("Abst", (aT --> proofT) --> proofT, NoSyn),
       ("AbsP", [propT, proofT --> proofT] ---> proofT, NoSyn)]
  |> Sign.add_nonterminals ["param", "params"]
  |> Sign.add_syntax_i
      [("_Lam", [paramsT, proofT] ---> proofT, Mixfix ("(1Lam _./ _)", [0, 3], 3)),
       ("_Lam0", [paramT, paramsT] ---> paramsT, Mixfix ("_/ _", [1, 0], 0)),
       ("_Lam0", [idtT, paramsT] ---> paramsT, Mixfix ("_/ _", [1, 0], 0)),
       ("_Lam1", [idtT, propT] ---> paramT, Mixfix ("_: _", [0, 0], 0)),
       ("", paramT --> paramT, Delimfix "'(_')"),
       ("", idtT --> paramsT, Delimfix "_"),
       ("", paramT --> paramsT, Delimfix "_")]
  |> Sign.add_modesyntax_i (("xsymbols", true),
      [("_Lam", [paramsT, proofT] ---> proofT, Mixfix ("(1\\<Lambda>_./ _)", [0, 3], 3)),
       ("Appt", [proofT, aT] ---> proofT, Mixfix ("(1_ \\<cdot>/ _)", [4, 5], 4)),
       ("AppP", [proofT, proofT] ---> proofT, Mixfix ("(1_ \\<bullet>/ _)", [4, 5], 4))])
  |> Sign.add_modesyntax_i (("latex", false),
      [("_Lam", [paramsT, proofT] ---> proofT, Mixfix ("(1\\<^bold>\\<lambda>_./ _)", [0, 3], 3))])
  |> Sign.add_trrules_i (map Syntax.ParsePrintRule
      [(Syntax.mk_appl (Constant "_Lam")
          [Syntax.mk_appl (Constant "_Lam0") [Variable "l", Variable "m"], Variable "A"],
        Syntax.mk_appl (Constant "_Lam")
          [Variable "l", Syntax.mk_appl (Constant "_Lam") [Variable "m", Variable "A"]]),
       (Syntax.mk_appl (Constant "_Lam")
          [Syntax.mk_appl (Constant "_Lam1") [Variable "x", Variable "A"], Variable "B"],
        Syntax.mk_appl (Constant "AbsP") [Variable "A",
          (Syntax.mk_appl (Constant "_abs") [Variable "x", Variable "B"])]),
       (Syntax.mk_appl (Constant "_Lam") [Variable "x", Variable "A"],
        Syntax.mk_appl (Constant "Abst")
          [(Syntax.mk_appl (Constant "_abs") [Variable "x", Variable "A"])])]);


(**** create unambiguous theorem names ****)

fun disambiguate_names thy prf =
  let
    val thms = thms_of_proof Symtab.empty prf;
    val thms' = map (apsnd (#prop o rep_thm)) (flat
      (map PureThy.thms_of (thy :: Theory.ancestors_of thy)));

    val tab = Symtab.foldl (fn (tab, (key, ps)) =>
      let val prop = if_none (assoc (thms', key)) (Bound 0)
      in fst (foldr (fn ((prop', prf), x as (tab, i)) =>
        if prop <> prop' then
          (Symtab.update ((key ^ "_" ^ string_of_int i, prf), tab), i+1)
        else x) (ps, (tab, 1)))
      end) (Symtab.empty, thms);

    fun rename (Abst (s, T, prf)) = Abst (s, T, rename prf)
      | rename (AbsP (s, t, prf)) = AbsP (s, t, rename prf)
      | rename (prf1 %% prf2) = rename prf1 %% rename prf2
      | rename (prf % t) = rename prf % t
      | rename (prf' as PThm ((s, tags), prf, prop, Ts)) =
          let
            val prop' = if_none (assoc (thms', s)) (Bound 0);
            val ps = map fst (the (Symtab.lookup (thms, s))) \ prop'
          in if prop = prop' then prf' else
            PThm ((s ^ "_" ^ string_of_int (length ps - find_index_eq prop ps), tags),
              prf, prop, Ts)
          end
      | rename prf = prf

  in (rename prf, tab) end;


(**** translation between proof terms and pure terms ****)

fun change_type T (PThm (name, prf, prop, _)) = PThm (name, prf, prop, T)
  | change_type T (PAxm (name, prop, _)) = PAxm (name, prop, T)
  | change_type _ _ = error "Not a proper theorem";

fun proof_of_term thy tab ty =
  let
    val thys = thy :: Theory.ancestors_of thy;
    val thms = flat (map thms_of thys);
    val axms = flat (map (Symtab.dest o #axioms o rep_theory) thys);

    fun mk_term t = (if ty then I else map_term_types (K dummyT))
      (Term.no_dummy_patterns t);

    fun prf_of [] (Bound i) = PBound i
      | prf_of Ts (Const (s, Type ("proof", _))) =
          change_type (if ty then Some Ts else None)
            (case NameSpace.unpack s of
               "axm" :: xs =>
                 let
                   val name = NameSpace.pack xs;
                   val prop = (case assoc (axms, name) of
                       Some prop => prop
                     | None => error ("Unknown axiom " ^ quote name))
                 in PAxm (name, prop, None) end
             | "thm" :: xs =>
                 let val name = NameSpace.pack xs;
                 in (case assoc (thms, name) of
                     Some thm => fst (strip_combt (#2 (#der (rep_thm thm))))
                   | None => (case Symtab.lookup (tab, name) of
                         Some prf => prf
                       | None => error ("Unknown theorem " ^ quote name)))
                 end
             | _ => error ("Illegal proof constant name: " ^ quote s))
      | prf_of Ts (v as Var ((_, Type ("proof", _)))) = Hyp v
      | prf_of [] (Const ("Abst", _) $ Abs (s, T, prf)) =
          Abst (s, if ty then Some T else None,
            incr_pboundvars (~1) 0 (prf_of [] prf))
      | prf_of [] (Const ("AbsP", _) $ t $ Abs (s, _, prf)) =
          AbsP (s, case t of
                Const ("dummy_pattern", _) => None
              | _ $ Const ("dummy_pattern", _) => None
              | _ => Some (mk_term t),
            incr_pboundvars 0 (~1) (prf_of [] prf))
      | prf_of [] (Const ("AppP", _) $ prf1 $ prf2) =
          prf_of [] prf1 %% prf_of [] prf2
      | prf_of Ts (Const ("Appt", _) $ prf $ Const ("TYPE", Type (_, [T]))) =
          prf_of (T::Ts) prf
      | prf_of [] (Const ("Appt", _) $ prf $ t) = prf_of [] prf %
          (case t of Const ("dummy_pattern", _) => None | _ => Some (mk_term t))
      | prf_of _ t = error ("Not a proof term:\n" ^
          Sign.string_of_term (sign_of thy) t)

  in prf_of [] end;


val AbsPt = Const ("AbsP", [propT, proofT --> proofT] ---> proofT);
val AppPt = Const ("AppP", [proofT, proofT] ---> proofT);
val Hypt = Free ("Hyp", propT --> proofT);
val Oraclet = Free ("Oracle", propT --> proofT);
val MinProoft = Free ("?", proofT);

val mk_tyapp = foldl (fn (prf, T) => Const ("Appt",
  [proofT, itselfT T] ---> proofT) $ prf $ Logic.mk_type T);

fun term_of _ (PThm ((name, _), _, _, None)) =
      Const (add_prefix "thm" name, proofT)
  | term_of _ (PThm ((name, _), _, _, Some Ts)) =
      mk_tyapp (Const (add_prefix "thm" name, proofT), Ts)
  | term_of _ (PAxm (name, _, None)) = Const (add_prefix "axm" name, proofT)
  | term_of _ (PAxm (name, _, Some Ts)) =
      mk_tyapp (Const (add_prefix "axm" name, proofT), Ts)
  | term_of _ (PBound i) = Bound i
  | term_of Ts (Abst (s, opT, prf)) = 
      let val T = if_none opT dummyT
      in Const ("Abst", (T --> proofT) --> proofT) $
        Abs (s, T, term_of (T::Ts) (incr_pboundvars 1 0 prf))
      end
  | term_of Ts (AbsP (s, t, prf)) =
      AbsPt $ if_none t (Const ("dummy_pattern", propT)) $
        Abs (s, proofT, term_of (proofT::Ts) (incr_pboundvars 0 1 prf))
  | term_of Ts (prf1 %% prf2) =
      AppPt $ term_of Ts prf1 $ term_of Ts prf2
  | term_of Ts (prf % opt) = 
      let val t = if_none opt (Const ("dummy_pattern", dummyT))
      in Const ("Appt",
        [proofT, fastype_of1 (Ts, t) handle TERM _ => dummyT] ---> proofT) $
          term_of Ts prf $ t
      end
  | term_of Ts (Hyp t) = Hypt $ t
  | term_of Ts (Oracle (_, t, _)) = Oraclet $ t
  | term_of Ts (MinProof _) = MinProoft;

val term_of_proof = term_of [];

fun cterm_of_proof thy prf =
  let
    val (prf', tab) = disambiguate_names thy prf;
    val thys = thy :: Theory.ancestors_of thy;
    val thm_names = filter_out (equal "") (map fst (flat (map thms_of thys))) @
      map fst (Symtab.dest tab);
    val axm_names = map fst (flat (map (Symtab.dest o #axioms o rep_theory) thys));
    val sg = sign_of thy |>
      add_proof_syntax |>
      add_proof_atom_consts
        (map (add_prefix "thm") thm_names @ map (add_prefix "axm") axm_names)
  in
    (cterm_of sg (term_of_proof prf'),
     proof_of_term thy tab true o Thm.term_of)
  end;

fun read_term thy =
  let
    val thys = thy :: Theory.ancestors_of thy;
    val thm_names = filter_out (equal "") (map fst (flat (map thms_of thys)));
    val axm_names = map fst (flat (map (Symtab.dest o #axioms o rep_theory) thys));
    val sg = sign_of thy |>
      add_proof_syntax |>
      add_proof_atom_consts
        (map (add_prefix "thm") thm_names @ map (add_prefix "axm") axm_names)
  in
    (fn T => fn s => Thm.term_of (read_cterm sg (s, T)))
  end;

fun read_proof thy =
  let val rd = read_term thy proofT
  in
    (fn ty => fn s => proof_of_term thy Symtab.empty ty (Logic.varify (rd s)))
  end;

fun pretty_proof sg prf =
  let
    val thm_names = map fst (Symtab.dest (thms_of_proof Symtab.empty prf)) \ "";
    val axm_names = map fst (Symtab.dest (axms_of_proof Symtab.empty prf));
    val sg' = sg |>
      add_proof_syntax |>
      add_proof_atom_consts
        (map (add_prefix "thm") thm_names @ map (add_prefix "axm") axm_names)
  in
    Sign.pretty_term sg' (term_of_proof prf)
  end;

fun pretty_proof_of full thm =
  let
    val {sign, der = (_, prf), prop, ...} = rep_thm thm;
    val prf' = (case strip_combt (fst (strip_combP prf)) of
        (PThm (_, prf', prop', _), _) => if prop=prop' then prf' else prf
      | _ => prf)
  in
    pretty_proof sign
      (if full then Reconstruct.reconstruct_proof sign prop prf' else prf')
  end;

val print_proof_of = Pretty.writeln oo pretty_proof_of;

end;
