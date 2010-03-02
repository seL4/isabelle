(*  Title:      HOLCF/Tools/Domain/domain_axioms.ML
    Author:     David von Oheimb

Syntax generator for domain command.
*)

signature DOMAIN_AXIOMS =
sig
  val copy_of_dtyp :
      string Symtab.table -> (int -> term) -> Datatype.dtyp -> term

  val calc_axioms :
      bool ->
      Domain_Library.eq list -> int -> Domain_Library.eq ->
      string * (string * term) list * (string * term) list

  val add_axioms :
      bool ->
      ((string * typ list) *
       (binding * (bool * binding option * typ) list * mixfix) list) list ->
      Domain_Library.eq list -> theory -> theory
end;


structure Domain_Axioms : DOMAIN_AXIOMS =
struct

open Domain_Library;

infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

(* FIXME: use theory data for this *)
val copy_tab : string Symtab.table =
    Symtab.make [(@{type_name "->"}, @{const_name "cfun_map"}),
                 (@{type_name "++"}, @{const_name "ssum_map"}),
                 (@{type_name "**"}, @{const_name "sprod_map"}),
                 (@{type_name "*"}, @{const_name "cprod_map"}),
                 (@{type_name "u"}, @{const_name "u_map"})];

fun copy_of_dtyp tab r dt =
    if Datatype_Aux.is_rec_type dt then copy tab r dt else ID
and copy tab r (Datatype_Aux.DtRec i) = r i
  | copy tab r (Datatype_Aux.DtTFree a) = ID
  | copy tab r (Datatype_Aux.DtType (c, ds)) =
    case Symtab.lookup tab c of
      SOME f => list_ccomb (%%:f, map (copy_of_dtyp tab r) ds)
    | NONE => (warning ("copy_of_dtyp: unknown type constructor " ^ c); ID);

fun calc_axioms
    (definitional : bool)
    (eqs : eq list)
    (n : int)
    (eqn as ((dname,_),cons) : eq)
    : string * (string * term) list * (string * term) list =
  let

(* ----- axioms and definitions concerning the isomorphism ------------------ *)

    val dc_abs = %%:(dname^"_abs");
    val dc_rep = %%:(dname^"_rep");
    val x_name'= "x";
    val x_name = idx_name eqs x_name' (n+1);
    val dnam = Long_Name.base_name dname;

    val abs_iso_ax = ("abs_iso", mk_trp(dc_rep`(dc_abs`%x_name') === %:x_name'));
    val rep_iso_ax = ("rep_iso", mk_trp(dc_abs`(dc_rep`%x_name') === %:x_name'));

(* ----- axiom and definitions concerning induction ------------------------- *)

    val finite_def =
        ("finite_def",
         %%:(dname^"_finite") ==
            mk_lam(x_name,
                   mk_ex("n",(%%:(dname^"_take") $ Bound 0)`Bound 1 === Bound 1)));

  in (dnam,
      (if definitional then [] else [abs_iso_ax, rep_iso_ax]),
      [finite_def])
  end; (* let (calc_axioms) *)


(* legacy type inference *)

fun legacy_infer_term thy t =
    singleton (Syntax.check_terms (ProofContext.init thy)) (Sign.intern_term thy t);

fun legacy_infer_prop thy t = legacy_infer_term thy (TypeInfer.constrain propT t);

fun infer_props thy = map (apsnd (legacy_infer_prop thy));


fun add_axioms_i x = snd o PureThy.add_axioms (map (Thm.no_attributes o apfst Binding.name) x);
fun add_axioms_infer axms thy = add_axioms_i (infer_props thy axms) thy;

fun add_defs_i x = snd o (PureThy.add_defs false) (map (Thm.no_attributes o apfst Binding.name) x);
fun add_defs_infer defs thy = add_defs_i (infer_props thy defs) thy;

fun add_axioms definitional eqs' (eqs : eq list) thy' =
  let
    val dnames = map (fst o fst) eqs;
    val x_name = idx_name dnames "x"; 

    fun add_one (dnam, axs, dfs) =
        Sign.add_path dnam
          #> add_axioms_infer axs
          #> Sign.parent_path;

    val axs = mapn (calc_axioms definitional eqs) 0 eqs;
    val thy = thy' |> fold add_one axs;

    fun get_iso_info ((dname, tyvars), cons') =
      let
        fun opt_lazy (lazy,_,t) = if lazy then mk_uT t else t
        fun prod     (_,args,_) =
            case args of [] => oneT
                       | _ => foldr1 mk_sprodT (map opt_lazy args);
        val ax_abs_iso = PureThy.get_thm thy (dname ^ ".abs_iso");
        val ax_rep_iso = PureThy.get_thm thy (dname ^ ".rep_iso");
        val lhsT = Type(dname,tyvars);
        val rhsT = foldr1 mk_ssumT (map prod cons');
        val rep_const = Const(dname^"_rep", lhsT ->> rhsT);
        val abs_const = Const(dname^"_abs", rhsT ->> lhsT);
      in
        {
          absT = lhsT,
          repT = rhsT,
          abs_const = abs_const,
          rep_const = rep_const,
          abs_inverse = ax_abs_iso,
          rep_inverse = ax_rep_iso
        }
      end;
    val dom_binds = map (Binding.name o Long_Name.base_name) dnames;
    val thy =
        if definitional then thy
        else snd (Domain_Take_Proofs.define_take_functions
                    (dom_binds ~~ map get_iso_info eqs') thy);

    fun add_one' (dnam, axs, dfs) =
        Sign.add_path dnam
          #> add_defs_infer dfs
          #> Sign.parent_path;
    val thy = fold add_one' axs thy;

    (* declare lub_take axioms *)
    local
      fun ax_lub_take dname =
        let
          val dnam : string = Long_Name.base_name dname;
          val take_const = %%:(dname^"_take");
          val lub = %%: @{const_name lub};
          val image = %%: @{const_name image};
          val UNIV = @{term "UNIV :: nat set"};
          val lhs = lub $ (image $ take_const $ UNIV);
          val ax = mk_trp (lhs === ID);
        in
          add_one (dnam, [("lub_take", ax)], [])
        end
    in
      val thy =
          if definitional then thy
          else fold ax_lub_take dnames thy
    end;
  in
    thy
  end; (* let (add_axioms) *)

end; (* struct *)
