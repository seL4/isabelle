(*  Title:      HOL/Nominal/nominal_inductive.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Infrastructure for proving additional properties of inductive predicates
involving nominal datatypes
*)

signature NOMINAL_INDUCTIVE =
sig
  val nominal_inductive: string -> theory -> theory
end

structure NominalInductive : NOMINAL_INDUCTIVE =
struct

val perm_boolI = thm "perm_boolI";
val (_, [perm_boolI_pi, _]) = Drule.strip_comb (snd (Thm.dest_comb
  (Drule.strip_imp_concl (cprop_of perm_boolI))));

fun transp ([] :: _) = []
  | transp xs = map hd xs :: transp (map tl xs);

fun nominal_inductive s thy =
  let
    val ctxt = ProofContext.init thy;
    val ({names, ...}, {raw_induct, intrs, ...}) =
      InductivePackage.the_inductive ctxt (Sign.intern_const thy s);
    val atoms = NominalAtoms.atoms_of thy;
    val eqvt_ss = HOL_basic_ss addsimps NominalThmDecls.get_eqvt_thms thy;
    val t = Logic.unvarify (concl_of raw_induct);
    val pi = Name.variant (add_term_names (t, [])) "pi";
    val ps = map (fst o HOLogic.dest_imp)
      (HOLogic.dest_conj (HOLogic.dest_Trueprop t));
    fun eqvt_tac th intr = SUBPROOF (fn {prems, ...} =>
      let val prems' = map (fn th' => th' RS th) prems
      in (rtac intr THEN_ALL_NEW
        (resolve_tac prems ORELSE'
          (cut_facts_tac prems' THEN' full_simp_tac eqvt_ss))) 1
      end) ctxt;
    val thss = map (fn atom =>
      let
        val pi' = Free (pi, NominalAtoms.mk_permT (Type (atom, [])));
        val perm_boolI' = Drule.cterm_instantiate
          [(perm_boolI_pi, cterm_of thy pi')] perm_boolI
      in map (fn th => standard (th RS mp))
        (DatatypeAux.split_conj_thm (Goal.prove_global thy [] []
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map (fn p =>
            HOLogic.mk_imp (p, list_comb
             (apsnd (map (NominalPackage.mk_perm [] pi')) (strip_comb p)))) ps)))
          (fn _ => EVERY (rtac raw_induct 1 :: map (fn (intr, i) =>
              full_simp_tac eqvt_ss i THEN TRY (eqvt_tac perm_boolI' intr i))
            (rev intrs ~~ (length intrs downto 1))))))
      end) atoms;
    val (_, thy') = PureThy.add_thmss (map (fn (name, ths) =>
        ((Sign.base_name name ^ "_eqvt", ths), [NominalThmDecls.eqvt_add]))
      (names ~~ transp thss)) thy;
  in thy' end;


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val nominal_inductiveP =
  OuterSyntax.command "nominal_inductive"
    "prove additional properties of inductive predicate involving nominal datatypes" K.thy_decl
    (P.name >> (Toplevel.theory o nominal_inductive));

val _ = OuterSyntax.add_parsers [nominal_inductiveP];

end;

end
