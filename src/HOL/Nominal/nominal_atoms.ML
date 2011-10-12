(*  Title:      HOL/Nominal/nominal_atoms.ML
    Author:     Christian Urban and Stefan Berghofer, TU Muenchen

Declaration of atom types to be used in nominal datatypes.
*)

signature NOMINAL_ATOMS =
sig
  val create_nom_typedecls : string list -> theory -> theory
  type atom_info
  val get_atom_infos : theory -> atom_info Symtab.table
  val get_atom_info : theory -> string -> atom_info option
  val the_atom_info : theory -> string -> atom_info
  val fs_class_of : theory -> string -> string
  val pt_class_of : theory -> string -> string
  val cp_class_of : theory -> string -> string -> string
  val at_inst_of : theory -> string -> thm
  val pt_inst_of : theory -> string -> thm
  val cp_inst_of : theory -> string -> string -> thm
  val dj_thm_of : theory -> string -> string -> thm
  val atoms_of : theory -> string list
  val mk_permT : typ -> typ
end

structure NominalAtoms : NOMINAL_ATOMS =
struct

val finite_emptyI = @{thm "finite.emptyI"};
val Collect_const = @{thm "Collect_const"};

val inductive_forall_def = @{thm "induct_forall_def"};


(* theory data *)

type atom_info =
  {pt_class : string,
   fs_class : string,
   cp_classes : string Symtab.table,
   at_inst : thm,
   pt_inst : thm,
   cp_inst : thm Symtab.table,
   dj_thms : thm Symtab.table};

structure NominalData = Theory_Data
(
  type T = atom_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun make_atom_info ((((((pt_class, fs_class), cp_classes), at_inst), pt_inst), cp_inst), dj_thms) =
  {pt_class = pt_class,
   fs_class = fs_class,
   cp_classes = cp_classes,
   at_inst = at_inst,
   pt_inst = pt_inst,
   cp_inst = cp_inst,
   dj_thms = dj_thms};

val get_atom_infos = NominalData.get;
val get_atom_info = Symtab.lookup o NominalData.get;

fun gen_lookup lookup name = case lookup name of
    SOME info => info
  | NONE => error ("Unknown atom type " ^ quote name);

fun the_atom_info thy = gen_lookup (get_atom_info thy);

fun gen_lookup' f thy = the_atom_info thy #> f;
fun gen_lookup'' f thy =
  gen_lookup' (f #> Symtab.lookup #> gen_lookup) thy;

val fs_class_of = gen_lookup' #fs_class;
val pt_class_of = gen_lookup' #pt_class;
val at_inst_of = gen_lookup' #at_inst;
val pt_inst_of = gen_lookup' #pt_inst;
val cp_class_of = gen_lookup'' #cp_classes;
val cp_inst_of = gen_lookup'' #cp_inst;
val dj_thm_of = gen_lookup'' #dj_thms;

fun atoms_of thy = map fst (Symtab.dest (NominalData.get thy));

fun mk_permT T = HOLogic.listT (HOLogic.mk_prodT (T, T));

fun mk_Cons x xs =
  let val T = fastype_of x
  in Const ("List.list.Cons", T --> HOLogic.listT T --> HOLogic.listT T) $ x $ xs end;

fun add_thms_string args = Global_Theory.add_thms ((map o apfst o apfst) Binding.name args);
fun add_thmss_string args = Global_Theory.add_thmss ((map o apfst o apfst) Binding.name args);

(* this function sets up all matters related to atom-  *)
(* kinds; the user specifies a list of atom-kind names *)
(* atom_decl <ak1> ... <akn>                           *)
fun create_nom_typedecls ak_names thy =
  let
    
    val (_,thy1) = 
    fold_map (fn ak => fn thy => 
          let val dt = ([], Binding.name ak, NoSyn, [(Binding.name ak, [@{typ nat}], NoSyn)])
              val (dt_names, thy1) = Datatype.add_datatype
                Datatype.default_config [ak] [dt] thy;
            
              val injects = maps (#inject o Datatype.the_info thy1) dt_names;
              val ak_type = Type (Sign.intern_type thy1 ak,[])
              val ak_sign = Sign.intern_const thy1 ak 
              
              val inj_type = @{typ nat} --> ak_type
              val inj_on_type = inj_type --> @{typ "nat set"} --> @{typ bool}

              (* first statement *)
              val stmnt1 = HOLogic.mk_Trueprop 
                  (Const (@{const_name "inj_on"},inj_on_type) $ 
                         Const (ak_sign,inj_type) $ HOLogic.mk_UNIV @{typ nat})

              val simp1 = @{thm inj_on_def} :: injects;
              
              val proof1 = fn _ => EVERY [simp_tac (HOL_basic_ss addsimps simp1) 1,
                                          rtac @{thm ballI} 1,
                                          rtac @{thm ballI} 1,
                                          rtac @{thm impI} 1,
                                          atac 1]
             
              val (inj_thm,thy2) = 
                   add_thms_string [((ak^"_inj",Goal.prove_global thy1 [] [] stmnt1 proof1), [])] thy1
              
              (* second statement *)
              val y = Free ("y",ak_type)  
              val stmnt2 = HOLogic.mk_Trueprop
                  (HOLogic.mk_exists ("x",@{typ nat},HOLogic.mk_eq (y,Const (ak_sign,inj_type) $ Bound 0)))

              val proof2 = fn {prems, context} =>
                Induct_Tacs.case_tac context "y" 1 THEN
                asm_simp_tac (HOL_basic_ss addsimps simp1) 1 THEN
                rtac @{thm exI} 1 THEN
                rtac @{thm refl} 1

              (* third statement *)
              val (inject_thm,thy3) =
                  add_thms_string [((ak^"_injection",Goal.prove_global thy2 [] [] stmnt2 proof2), [])] thy2
  
              val stmnt3 = HOLogic.mk_Trueprop
                           (HOLogic.mk_not
                              (Const ("Finite_Set.finite", HOLogic.mk_setT ak_type --> HOLogic.boolT) $
                                  HOLogic.mk_UNIV ak_type))
             
              val simp2 = [@{thm image_def},@{thm bex_UNIV}]@inject_thm
              val simp3 = [@{thm UNIV_def}]

              val proof3 = fn _ => EVERY [cut_facts_tac inj_thm 1,
                                          dtac @{thm range_inj_infinite} 1,
                                          asm_full_simp_tac (HOL_basic_ss addsimps simp2) 1,
                                          simp_tac (HOL_basic_ss addsimps simp3) 1]  
           
              val (inf_thm,thy4) =  
                    add_thms_string [((ak^"_infinite",Goal.prove_global thy3 [] [] stmnt3 proof3), [])] thy3
          in 
            ((inj_thm,inject_thm,inf_thm),thy4)
          end) ak_names thy

    (* produces a list consisting of pairs:         *)
    (*  fst component is the atom-kind name         *)
    (*  snd component is its type                   *)
    val full_ak_names = map (Sign.intern_type thy1) ak_names;
    val ak_names_types = ak_names ~~ map (Type o rpair []) full_ak_names;
     
    (* declares a swapping function for every atom-kind, it is         *)
    (* const swap_<ak> :: <akT> * <akT> => <akT> => <akT>              *)
    (* swap_<ak> (a,b) c = (if a=c then b (else if b=c then a else c)) *)
    (* overloades then the general swap-function                       *) 
    val (swap_eqs, thy3) = fold_map (fn (ak_name, T) => fn thy =>
      let
        val thy' = Sign.add_path "rec" thy;
        val swapT = HOLogic.mk_prodT (T, T) --> T --> T;
        val swap_name = "swap_" ^ ak_name;
        val full_swap_name = Sign.full_bname thy' swap_name;
        val a = Free ("a", T);
        val b = Free ("b", T);
        val c = Free ("c", T);
        val ab = Free ("ab", HOLogic.mk_prodT (T, T))
        val cif = Const ("HOL.If", HOLogic.boolT --> T --> T --> T);
        val cswap_akname = Const (full_swap_name, swapT);
        val cswap = Const ("Nominal.swap", swapT)

        val name = swap_name ^ "_def";
        val def1 = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (Free (swap_name, swapT) $ HOLogic.mk_prod (a,b) $ c,
                    cif $ HOLogic.mk_eq (a,c) $ b $ (cif $ HOLogic.mk_eq (b,c) $ a $ c)))
        val def2 = Logic.mk_equals (cswap $ ab $ c, cswap_akname $ ab $ c)
      in
        thy' |>
        Primrec.add_primrec_global
          [(Binding.name swap_name, SOME swapT, NoSyn)]
          [(Attrib.empty_binding, def1)] ||>
        Sign.parent_path ||>>
        Global_Theory.add_defs_unchecked true
          [((Binding.name name, def2), [])] |>> (snd o fst)
      end) ak_names_types thy1;
    
    (* declares a permutation function for every atom-kind acting  *)
    (* on such atoms                                               *)
    (* const <ak>_prm_<ak> :: (<akT> * <akT>)list => akT => akT    *)
    (* <ak>_prm_<ak> []     a = a                                  *)
    (* <ak>_prm_<ak> (x#xs) a = swap_<ak> x (perm xs a)            *)
    val (prm_eqs, thy4) = fold_map (fn (ak_name, T) => fn thy =>
      let
        val thy' = Sign.add_path "rec" thy;
        val swapT = HOLogic.mk_prodT (T, T) --> T --> T;
        val swap_name = Sign.full_bname thy' ("swap_" ^ ak_name)
        val prmT = mk_permT T --> T --> T;
        val prm_name = ak_name ^ "_prm_" ^ ak_name;
        val prm = Free (prm_name, prmT);
        val x  = Free ("x", HOLogic.mk_prodT (T, T));
        val xs = Free ("xs", mk_permT T);
        val a  = Free ("a", T) ;

        val cnil  = Const ("List.list.Nil", mk_permT T);
        
        val def1 = HOLogic.mk_Trueprop (HOLogic.mk_eq (prm $ cnil $ a, a));

        val def2 = HOLogic.mk_Trueprop (HOLogic.mk_eq
                   (prm $ mk_Cons x xs $ a,
                    Const (swap_name, swapT) $ x $ (prm $ xs $ a)));
      in
        thy' |>
        Primrec.add_primrec_global
          [(Binding.name prm_name, SOME prmT, NoSyn)]
          [(Attrib.empty_binding, def1), (Attrib.empty_binding, def2)] ||>
        Sign.parent_path
      end) ak_names_types thy3;
    
    (* defines permutation functions for all combinations of atom-kinds; *)
    (* there are a trivial cases and non-trivial cases                   *)
    (* non-trivial case:                                                 *)
    (* <ak>_prm_<ak>_def:  perm pi a == <ak>_prm_<ak> pi a               *)
    (* trivial case with <ak> != <ak'>                                   *)
    (* <ak>_prm<ak'>_def[simp]:  perm pi a == a                          *)
    (*                                                                   *)
    (* the trivial cases are added to the simplifier, while the non-     *)
    (* have their own rules proved below                                 *)  
    val (perm_defs, thy5) = fold_map (fn (ak_name, T) => fn thy =>
      fold_map (fn (ak_name', T') => fn thy' =>
        let
          val perm_def_name = ak_name ^ "_prm_" ^ ak_name';
          val pi = Free ("pi", mk_permT T);
          val a  = Free ("a", T');
          val cperm = Const ("Nominal.perm", mk_permT T --> T' --> T');
          val thy'' = Sign.add_path "rec" thy'
          val cperm_def = Const (Sign.full_bname thy'' perm_def_name, mk_permT T --> T' --> T');
          val thy''' = Sign.parent_path thy'';

          val name = ak_name ^ "_prm_" ^ ak_name' ^ "_def";
          val def = Logic.mk_equals
                    (cperm $ pi $ a, if ak_name = ak_name' then cperm_def $ pi $ a else a)
        in
          Global_Theory.add_defs_unchecked true [((Binding.name name, def), [])] thy'''
        end) ak_names_types thy) ak_names_types thy4;
    
    (* proves that every atom-kind is an instance of at *)
    (* lemma at_<ak>_inst:                              *)
    (* at TYPE(<ak>)                                    *)
    val (prm_cons_thms,thy6) = 
      thy5 |> add_thms_string (map (fn (ak_name, T) =>
      let
        val ak_name_qu = Sign.full_bname thy5 (ak_name);
        val i_type = Type(ak_name_qu,[]);
        val cat = Const ("Nominal.at",(Term.itselfT i_type)  --> HOLogic.boolT);
        val at_type = Logic.mk_type i_type;
        val simp_s = HOL_ss addsimps maps (Global_Theory.get_thms thy5)
                                  ["at_def",
                                   ak_name ^ "_prm_" ^ ak_name ^ "_def",
                                   ak_name ^ "_prm_" ^ ak_name ^ ".simps",
                                   "swap_" ^ ak_name ^ "_def",
                                   "swap_" ^ ak_name ^ ".simps",
                                   ak_name ^ "_infinite"]
            
        val name = "at_"^ak_name^ "_inst";
        val statement = HOLogic.mk_Trueprop (cat $ at_type);

        val proof = fn _ => simp_tac simp_s 1

      in 
        ((name, Goal.prove_global thy5 [] [] statement proof), []) 
      end) ak_names_types);

    (* declares a perm-axclass for every atom-kind               *)
    (* axclass pt_<ak>                                           *)
    (* pt_<ak>1[simp]: perm [] x = x                             *)
    (* pt_<ak>2:       perm (pi1@pi2) x = perm pi1 (perm pi2 x)  *)
    (* pt_<ak>3:       pi1 ~ pi2 ==> perm pi1 x = perm pi2 x     *)
     val (pt_ax_classes,thy7) =  fold_map (fn (ak_name, T) => fn thy =>
      let 
          val cl_name = "pt_"^ak_name;
          val ty = TFree("'a",["HOL.type"]);
          val x   = Free ("x", ty);
          val pi1 = Free ("pi1", mk_permT T);
          val pi2 = Free ("pi2", mk_permT T);
          val cperm = Const ("Nominal.perm", mk_permT T --> ty --> ty);
          val cnil  = Const ("List.list.Nil", mk_permT T);
          val cappend = Const ("List.append",mk_permT T --> mk_permT T --> mk_permT T);
          val cprm_eq = Const ("Nominal.prm_eq",mk_permT T --> mk_permT T --> HOLogic.boolT);
          (* nil axiom *)
          val axiom1 = HOLogic.mk_Trueprop (HOLogic.mk_eq 
                       (cperm $ cnil $ x, x));
          (* append axiom *)
          val axiom2 = HOLogic.mk_Trueprop (HOLogic.mk_eq
                       (cperm $ (cappend $ pi1 $ pi2) $ x, cperm $ pi1 $ (cperm $ pi2 $ x)));
          (* perm-eq axiom *)
          val axiom3 = Logic.mk_implies
                       (HOLogic.mk_Trueprop (cprm_eq $ pi1 $ pi2),
                        HOLogic.mk_Trueprop (HOLogic.mk_eq (cperm $ pi1 $ x, cperm $ pi2 $ x)));
      in
          AxClass.define_class (Binding.name cl_name, ["HOL.type"]) []
                [((Binding.name (cl_name ^ "1"), [Simplifier.simp_add]), [axiom1]),
                 ((Binding.name (cl_name ^ "2"), []), [axiom2]),                           
                 ((Binding.name (cl_name ^ "3"), []), [axiom3])] thy
      end) ak_names_types thy6;

    (* proves that every pt_<ak>-type together with <ak>-type *)
    (* instance of pt                                         *)
    (* lemma pt_<ak>_inst:                                    *)
    (* pt TYPE('x::pt_<ak>) TYPE(<ak>)                        *)
    val (prm_inst_thms,thy8) = 
      thy7 |> add_thms_string (map (fn (ak_name, T) =>
      let
        val ak_name_qu = Sign.full_bname thy7 ak_name;
        val pt_name_qu = Sign.full_bname thy7 ("pt_"^ak_name);
        val i_type1 = TFree("'x",[pt_name_qu]);
        val i_type2 = Type(ak_name_qu,[]);
        val cpt = Const ("Nominal.pt",(Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
        val pt_type = Logic.mk_type i_type1;
        val at_type = Logic.mk_type i_type2;
        val simp_s = HOL_ss addsimps maps (Global_Theory.get_thms thy7)
                                  ["pt_def",
                                   "pt_" ^ ak_name ^ "1",
                                   "pt_" ^ ak_name ^ "2",
                                   "pt_" ^ ak_name ^ "3"];

        val name = "pt_"^ak_name^ "_inst";
        val statement = HOLogic.mk_Trueprop (cpt $ pt_type $ at_type);

        val proof = fn _ => simp_tac simp_s 1;
      in 
        ((name, Goal.prove_global thy7 [] [] statement proof), []) 
      end) ak_names_types);

     (* declares an fs-axclass for every atom-kind       *)
     (* axclass fs_<ak>                                  *)
     (* fs_<ak>1: finite ((supp x)::<ak> set)            *)
     val (fs_ax_classes,thy11) =  fold_map (fn (ak_name, T) => fn thy =>
       let 
          val cl_name = "fs_"^ak_name;
          val pt_name = Sign.full_bname thy ("pt_"^ak_name);
          val ty = TFree("'a",["HOL.type"]);
          val x   = Free ("x", ty);
          val csupp    = Const ("Nominal.supp", ty --> HOLogic.mk_setT T);
          val cfinite  = Const ("Finite_Set.finite", HOLogic.mk_setT T --> HOLogic.boolT)
          
          val axiom1   = HOLogic.mk_Trueprop (cfinite $ (csupp $ x));

       in  
        AxClass.define_class (Binding.name cl_name, [pt_name]) []
          [((Binding.name (cl_name ^ "1"), []), [axiom1])] thy
       end) ak_names_types thy8; 
         
     (* proves that every fs_<ak>-type together with <ak>-type   *)
     (* instance of fs-type                                      *)
     (* lemma abst_<ak>_inst:                                    *)
     (* fs TYPE('x::pt_<ak>) TYPE (<ak>)                         *)
     val (fs_inst_thms,thy12) = 
       thy11 |> add_thms_string (map (fn (ak_name, T) =>
       let
         val ak_name_qu = Sign.full_bname thy11 ak_name;
         val fs_name_qu = Sign.full_bname thy11 ("fs_"^ak_name);
         val i_type1 = TFree("'x",[fs_name_qu]);
         val i_type2 = Type(ak_name_qu,[]);
         val cfs = Const ("Nominal.fs", 
                                 (Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
         val fs_type = Logic.mk_type i_type1;
         val at_type = Logic.mk_type i_type2;
         val simp_s = HOL_ss addsimps maps (Global_Theory.get_thms thy11)
                                   ["fs_def",
                                    "fs_" ^ ak_name ^ "1"];
    
         val name = "fs_"^ak_name^ "_inst";
         val statement = HOLogic.mk_Trueprop (cfs $ fs_type $ at_type);

         val proof = fn _ => simp_tac simp_s 1;
       in 
         ((name, Goal.prove_global thy11 [] [] statement proof), []) 
       end) ak_names_types);

       (* declares for every atom-kind combination an axclass            *)
       (* cp_<ak1>_<ak2> giving a composition property                   *)
       (* cp_<ak1>_<ak2>1: pi1 o pi2 o x = (pi1 o pi2) o (pi1 o x)       *)
        val (cp_ax_classes,thy12b) = fold_map (fn (ak_name, T) => fn thy =>
         fold_map (fn (ak_name', T') => fn thy' =>
             let
               val cl_name = "cp_"^ak_name^"_"^ak_name';
               val ty = TFree("'a",["HOL.type"]);
               val x   = Free ("x", ty);
               val pi1 = Free ("pi1", mk_permT T);
               val pi2 = Free ("pi2", mk_permT T');                  
               val cperm1 = Const ("Nominal.perm", mk_permT T  --> ty --> ty);
               val cperm2 = Const ("Nominal.perm", mk_permT T' --> ty --> ty);
               val cperm3 = Const ("Nominal.perm", mk_permT T  --> mk_permT T' --> mk_permT T');

               val ax1   = HOLogic.mk_Trueprop 
                           (HOLogic.mk_eq (cperm1 $ pi1 $ (cperm2 $ pi2 $ x), 
                                           cperm2 $ (cperm3 $ pi1 $ pi2) $ (cperm1 $ pi1 $ x)));
               in  
                 AxClass.define_class (Binding.name cl_name, ["HOL.type"]) []
                   [((Binding.name (cl_name ^ "1"), []), [ax1])] thy'  
               end) ak_names_types thy) ak_names_types thy12;

        (* proves for every <ak>-combination a cp_<ak1>_<ak2>_inst theorem;     *)
        (* lemma cp_<ak1>_<ak2>_inst:                                           *)
        (* cp TYPE('a::cp_<ak1>_<ak2>) TYPE(<ak1>) TYPE(<ak2>)                  *)
        val (cp_thms,thy12c) = fold_map (fn (ak_name, T) => fn thy =>
         fold_map (fn (ak_name', T') => fn thy' =>
           let
             val ak_name_qu  = Sign.full_bname thy' (ak_name);
             val ak_name_qu' = Sign.full_bname thy' (ak_name');
             val cp_name_qu  = Sign.full_bname thy' ("cp_"^ak_name^"_"^ak_name');
             val i_type0 = TFree("'a",[cp_name_qu]);
             val i_type1 = Type(ak_name_qu,[]);
             val i_type2 = Type(ak_name_qu',[]);
             val ccp = Const ("Nominal.cp",
                             (Term.itselfT i_type0)-->(Term.itselfT i_type1)-->
                                                      (Term.itselfT i_type2)-->HOLogic.boolT);
             val at_type  = Logic.mk_type i_type1;
             val at_type' = Logic.mk_type i_type2;
             val cp_type  = Logic.mk_type i_type0;
             val simp_s   = HOL_basic_ss addsimps maps (Global_Theory.get_thms thy') ["cp_def"];
             val cp1      = Global_Theory.get_thm thy' ("cp_" ^ ak_name ^ "_" ^ ak_name' ^ "1");

             val name = "cp_"^ak_name^ "_"^ak_name'^"_inst";
             val statement = HOLogic.mk_Trueprop (ccp $ cp_type $ at_type $ at_type');

             val proof = fn _ => EVERY [simp_tac simp_s 1, 
                                        rtac allI 1, rtac allI 1, rtac allI 1,
                                        rtac cp1 1];
           in
             yield_singleton add_thms_string ((name,
               Goal.prove_global thy' [] [] statement proof), []) thy'
           end) 
           ak_names_types thy) ak_names_types thy12b;
       
        (* proves for every non-trivial <ak>-combination a disjointness   *)
        (* theorem; i.e. <ak1> != <ak2>                                   *)
        (* lemma ds_<ak1>_<ak2>:                                          *)
        (* dj TYPE(<ak1>) TYPE(<ak2>)                                     *)
        val (dj_thms, thy12d) = fold_map (fn (ak_name,T) => fn thy =>
          fold_map (fn (ak_name',T') => fn thy' =>
          (if not (ak_name = ak_name') 
           then 
               let
                 val ak_name_qu  = Sign.full_bname thy' ak_name;
                 val ak_name_qu' = Sign.full_bname thy' ak_name';
                 val i_type1 = Type(ak_name_qu,[]);
                 val i_type2 = Type(ak_name_qu',[]);
                 val cdj = Const ("Nominal.disjoint",
                           (Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
                 val at_type  = Logic.mk_type i_type1;
                 val at_type' = Logic.mk_type i_type2;
                 val simp_s = HOL_ss addsimps maps (Global_Theory.get_thms thy')
                                           ["disjoint_def",
                                            ak_name ^ "_prm_" ^ ak_name' ^ "_def",
                                            ak_name' ^ "_prm_" ^ ak_name ^ "_def"];

                 val name = "dj_"^ak_name^"_"^ak_name';
                 val statement = HOLogic.mk_Trueprop (cdj $ at_type $ at_type');

                 val proof = fn _ => simp_tac simp_s 1;
               in
                add_thms_string [((name, Goal.prove_global thy' [] [] statement proof), [])] thy'
               end
           else 
            ([],thy')))  (* do nothing branch, if ak_name = ak_name' *) 
            ak_names_types thy) ak_names_types thy12c;

     (********  pt_<ak> class instances  ********)
     (*=========================================*)
     (* some abbreviations for theorems *)
      val pt1           = @{thm "pt1"};
      val pt2           = @{thm "pt2"};
      val pt3           = @{thm "pt3"};
      val at_pt_inst    = @{thm "at_pt_inst"};
      val pt_unit_inst  = @{thm "pt_unit_inst"};
      val pt_prod_inst  = @{thm "pt_prod_inst"}; 
      val pt_nprod_inst = @{thm "pt_nprod_inst"}; 
      val pt_list_inst  = @{thm "pt_list_inst"};
      val pt_optn_inst  = @{thm "pt_option_inst"};
      val pt_noptn_inst = @{thm "pt_noption_inst"};
      val pt_fun_inst   = @{thm "pt_fun_inst"};

     (* for all atom-kind combinations <ak>/<ak'> show that        *)
     (* every <ak> is an instance of pt_<ak'>; the proof for       *)
     (* ak!=ak' is by definition; the case ak=ak' uses at_pt_inst. *)
     val thy13 = fold (fn ak_name => fn thy =>
        fold (fn ak_name' => fn thy' =>
         let
           val qu_name =  Sign.full_bname thy' ak_name';
           val cls_name = Sign.full_bname thy' ("pt_"^ak_name);
           val at_inst  = Global_Theory.get_thm thy' ("at_" ^ ak_name' ^ "_inst");

           val proof1 = EVERY [Class.intro_classes_tac [],
                                 rtac ((at_inst RS at_pt_inst) RS pt1) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt2) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt3) 1,
                                 atac 1];
           val simp_s = HOL_basic_ss addsimps 
                        maps (Global_Theory.get_thms thy') [ak_name ^ "_prm_" ^ ak_name' ^ "_def"];  
           val proof2 = EVERY [Class.intro_classes_tac [], REPEAT (asm_simp_tac simp_s 1)];

         in
           thy'
           |> AxClass.prove_arity (qu_name,[],[cls_name])
              (if ak_name = ak_name' then proof1 else proof2)
         end) ak_names thy) ak_names thy12d;

     (* show that                       *)
     (*      fun(pt_<ak>,pt_<ak>)       *)
     (*      noption(pt_<ak>)           *)
     (*      option(pt_<ak>)            *)
     (*      list(pt_<ak>)              *)
     (*      *(pt_<ak>,pt_<ak>)         *)
     (*      nprod(pt_<ak>,pt_<ak>)     *)
     (*      unit                       *)
     (*      set(pt_<ak>)               *)
     (* are instances of pt_<ak>        *)
     val thy18 = fold (fn ak_name => fn thy =>
       let
          val cls_name = Sign.full_bname thy ("pt_"^ak_name);
          val at_thm   = Global_Theory.get_thm thy ("at_"^ak_name^"_inst");
          val pt_inst  = Global_Theory.get_thm thy ("pt_"^ak_name^"_inst");

          fun pt_proof thm = 
              EVERY [Class.intro_classes_tac [],
                     rtac (thm RS pt1) 1, rtac (thm RS pt2) 1, rtac (thm RS pt3) 1, atac 1];

          val pt_thm_fun   = at_thm RS (pt_inst RS (pt_inst RS pt_fun_inst));
          val pt_thm_noptn = pt_inst RS pt_noptn_inst; 
          val pt_thm_optn  = pt_inst RS pt_optn_inst; 
          val pt_thm_list  = pt_inst RS pt_list_inst;
          val pt_thm_prod  = pt_inst RS (pt_inst RS pt_prod_inst);
          val pt_thm_nprod = pt_inst RS (pt_inst RS pt_nprod_inst);
          val pt_thm_unit  = pt_unit_inst;
       in
        thy
        |> AxClass.prove_arity ("fun",[[cls_name],[cls_name]],[cls_name]) (pt_proof pt_thm_fun)
        |> AxClass.prove_arity ("Nominal.noption",[[cls_name]],[cls_name]) (pt_proof pt_thm_noptn) 
        |> AxClass.prove_arity ("Option.option",[[cls_name]],[cls_name]) (pt_proof pt_thm_optn)
        |> AxClass.prove_arity ("List.list",[[cls_name]],[cls_name]) (pt_proof pt_thm_list)
        |> AxClass.prove_arity (@{type_name Product_Type.prod},[[cls_name],[cls_name]],[cls_name]) (pt_proof pt_thm_prod)
        |> AxClass.prove_arity ("Nominal.nprod",[[cls_name],[cls_name]],[cls_name]) 
                                    (pt_proof pt_thm_nprod)
        |> AxClass.prove_arity ("Product_Type.unit",[],[cls_name]) (pt_proof pt_thm_unit)
     end) ak_names thy13; 

       (********  fs_<ak> class instances  ********)
       (*=========================================*)
       (* abbreviations for some lemmas *)
       val fs1            = @{thm "fs1"};
       val fs_at_inst     = @{thm "fs_at_inst"};
       val fs_unit_inst   = @{thm "fs_unit_inst"};
       val fs_prod_inst   = @{thm "fs_prod_inst"};
       val fs_nprod_inst  = @{thm "fs_nprod_inst"};
       val fs_list_inst   = @{thm "fs_list_inst"};
       val fs_option_inst = @{thm "fs_option_inst"};
       val dj_supp        = @{thm "dj_supp"};

       (* shows that <ak> is an instance of fs_<ak>     *)
       (* uses the theorem at_<ak>_inst                 *)
       val thy20 = fold (fn ak_name => fn thy =>
        fold (fn ak_name' => fn thy' =>
        let
           val qu_name =  Sign.full_bname thy' ak_name';
           val qu_class = Sign.full_bname thy' ("fs_"^ak_name);
           val proof =
               (if ak_name = ak_name'
                then
                  let val at_thm = Global_Theory.get_thm thy' ("at_"^ak_name^"_inst");
                  in  EVERY [Class.intro_classes_tac [],
                             rtac ((at_thm RS fs_at_inst) RS fs1) 1] end
                else
                  let val dj_inst = Global_Theory.get_thm thy' ("dj_"^ak_name'^"_"^ak_name);
                      val simp_s = HOL_basic_ss addsimps [dj_inst RS dj_supp, finite_emptyI];
                  in EVERY [Class.intro_classes_tac [], asm_simp_tac simp_s 1] end)
        in
         AxClass.prove_arity (qu_name,[],[qu_class]) proof thy'
        end) ak_names thy) ak_names thy18;

       (* shows that                  *)
       (*    unit                     *)
       (*    *(fs_<ak>,fs_<ak>)       *)
       (*    nprod(fs_<ak>,fs_<ak>)   *)
       (*    list(fs_<ak>)            *)
       (*    option(fs_<ak>)          *) 
       (* are instances of fs_<ak>    *)

       val thy24 = fold (fn ak_name => fn thy => 
        let
          val cls_name = Sign.full_bname thy ("fs_"^ak_name);
          val fs_inst  = Global_Theory.get_thm thy ("fs_"^ak_name^"_inst");
          fun fs_proof thm = EVERY [Class.intro_classes_tac [], rtac (thm RS fs1) 1];

          val fs_thm_unit  = fs_unit_inst;
          val fs_thm_prod  = fs_inst RS (fs_inst RS fs_prod_inst);
          val fs_thm_nprod = fs_inst RS (fs_inst RS fs_nprod_inst);
          val fs_thm_list  = fs_inst RS fs_list_inst;
          val fs_thm_optn  = fs_inst RS fs_option_inst;
        in 
         thy
         |> AxClass.prove_arity ("Product_Type.unit",[],[cls_name]) (fs_proof fs_thm_unit) 
         |> AxClass.prove_arity (@{type_name Product_Type.prod},[[cls_name],[cls_name]],[cls_name]) (fs_proof fs_thm_prod) 
         |> AxClass.prove_arity ("Nominal.nprod",[[cls_name],[cls_name]],[cls_name]) 
                                     (fs_proof fs_thm_nprod) 
         |> AxClass.prove_arity ("List.list",[[cls_name]],[cls_name]) (fs_proof fs_thm_list)
         |> AxClass.prove_arity ("Option.option",[[cls_name]],[cls_name]) (fs_proof fs_thm_optn)
        end) ak_names thy20;

       (********  cp_<ak>_<ai> class instances  ********)
       (*==============================================*)
       (* abbreviations for some lemmas *)
       val cp1             = @{thm "cp1"};
       val cp_unit_inst    = @{thm "cp_unit_inst"};
       val cp_bool_inst    = @{thm "cp_bool_inst"};
       val cp_prod_inst    = @{thm "cp_prod_inst"};
       val cp_list_inst    = @{thm "cp_list_inst"};
       val cp_fun_inst     = @{thm "cp_fun_inst"};
       val cp_option_inst  = @{thm "cp_option_inst"};
       val cp_noption_inst = @{thm "cp_noption_inst"};
       val pt_perm_compose = @{thm "pt_perm_compose"};

       val dj_pp_forget    = @{thm "dj_perm_perm_forget"};

       (* shows that <aj> is an instance of cp_<ak>_<ai>  *)
       (* for every  <ak>/<ai>-combination                *)
       val thy25 = fold (fn ak_name => fn thy =>
         fold (fn ak_name' => fn thy' =>
          fold (fn ak_name'' => fn thy'' =>
            let
              val name =  Sign.full_bname thy'' ak_name;
              val cls_name = Sign.full_bname thy'' ("cp_"^ak_name'^"_"^ak_name'');
              val proof =
                (if (ak_name'=ak_name'') then 
                  (let
                    val pt_inst  = Global_Theory.get_thm thy'' ("pt_"^ak_name''^"_inst");
                    val at_inst  = Global_Theory.get_thm thy'' ("at_"^ak_name''^"_inst");
                  in
                   EVERY [Class.intro_classes_tac [],
                          rtac (at_inst RS (pt_inst RS pt_perm_compose)) 1]
                  end)
                else
                  (let
                     val dj_inst  = Global_Theory.get_thm thy'' ("dj_"^ak_name''^"_"^ak_name');
                     val simp_s = HOL_basic_ss addsimps
                                        ((dj_inst RS dj_pp_forget)::
                                         (maps (Global_Theory.get_thms thy'')
                                           [ak_name' ^"_prm_"^ak_name^"_def",
                                            ak_name''^"_prm_"^ak_name^"_def"]));
                  in
                    EVERY [Class.intro_classes_tac [], simp_tac simp_s 1]
                  end))
              in
                AxClass.prove_arity (name,[],[cls_name]) proof thy''
              end) ak_names thy') ak_names thy) ak_names thy24;

       (* shows that                                                    *) 
       (*      units                                                    *) 
       (*      products                                                 *)
       (*      lists                                                    *)
       (*      functions                                                *)
       (*      options                                                  *)
       (*      noptions                                                 *)
       (*      sets                                                     *)
       (* are instances of cp_<ak>_<ai> for every <ak>/<ai>-combination *)
       val thy26 = fold (fn ak_name => fn thy =>
        fold (fn ak_name' => fn thy' =>
        let
            val cls_name = Sign.full_bname thy' ("cp_"^ak_name^"_"^ak_name');
            val cp_inst  = Global_Theory.get_thm thy' ("cp_"^ak_name^"_"^ak_name'^"_inst");
            val pt_inst  = Global_Theory.get_thm thy' ("pt_"^ak_name^"_inst");
            val at_inst  = Global_Theory.get_thm thy' ("at_"^ak_name^"_inst");

            fun cp_proof thm  = EVERY [Class.intro_classes_tac [],rtac (thm RS cp1) 1];
          
            val cp_thm_unit = cp_unit_inst;
            val cp_thm_prod = cp_inst RS (cp_inst RS cp_prod_inst);
            val cp_thm_list = cp_inst RS cp_list_inst;
            val cp_thm_fun  = at_inst RS (pt_inst RS (cp_inst RS (cp_inst RS cp_fun_inst)));
            val cp_thm_optn = cp_inst RS cp_option_inst;
            val cp_thm_noptn = cp_inst RS cp_noption_inst;
        in
         thy'
         |> AxClass.prove_arity ("Product_Type.unit",[],[cls_name]) (cp_proof cp_thm_unit)
         |> AxClass.prove_arity (@{type_name Product_Type.prod}, [[cls_name],[cls_name]],[cls_name]) (cp_proof cp_thm_prod)
         |> AxClass.prove_arity ("List.list",[[cls_name]],[cls_name]) (cp_proof cp_thm_list)
         |> AxClass.prove_arity ("fun",[[cls_name],[cls_name]],[cls_name]) (cp_proof cp_thm_fun)
         |> AxClass.prove_arity ("Option.option",[[cls_name]],[cls_name]) (cp_proof cp_thm_optn)
         |> AxClass.prove_arity ("Nominal.noption",[[cls_name]],[cls_name]) (cp_proof cp_thm_noptn)
        end) ak_names thy) ak_names thy25;

     (* show that discrete nominal types are permutation types, finitely     *)
     (* supported and have the commutation property                          *)
     (* discrete types have a permutation operation defined as pi o x = x;   *)
     (* which renders the proofs to be simple "simp_all"-proofs.             *)
     val thy32 =
        let
          fun discrete_pt_inst discrete_ty defn =
             fold (fn ak_name => fn thy =>
             let
               val qu_class = Sign.full_bname thy ("pt_"^ak_name);
               val simp_s = HOL_basic_ss addsimps [Simpdata.mk_eq defn];
               val proof = EVERY [Class.intro_classes_tac [], REPEAT (asm_simp_tac simp_s 1)];
             in 
               AxClass.prove_arity (discrete_ty, [], [qu_class]) proof thy
             end) ak_names;

          fun discrete_fs_inst discrete_ty defn = 
             fold (fn ak_name => fn thy =>
             let
               val qu_class = Sign.full_bname thy ("fs_"^ak_name);
               val supp_def = Simpdata.mk_eq @{thm "Nominal.supp_def"};
               val simp_s = HOL_ss addsimps [supp_def, Collect_const, finite_emptyI, Simpdata.mk_eq defn];
               val proof = EVERY [Class.intro_classes_tac [], asm_simp_tac simp_s 1];
             in 
               AxClass.prove_arity (discrete_ty, [], [qu_class]) proof thy
             end) ak_names;

          fun discrete_cp_inst discrete_ty defn = 
             fold (fn ak_name' => (fold (fn ak_name => fn thy =>
             let
               val qu_class = Sign.full_bname thy ("cp_"^ak_name^"_"^ak_name');
               val supp_def = Simpdata.mk_eq @{thm "Nominal.supp_def"};
               val simp_s = HOL_ss addsimps [Simpdata.mk_eq defn];
               val proof = EVERY [Class.intro_classes_tac [], asm_simp_tac simp_s 1];
             in
               AxClass.prove_arity (discrete_ty, [], [qu_class]) proof thy
             end) ak_names)) ak_names;

        in
         thy26
         |> discrete_pt_inst @{type_name nat} @{thm perm_nat_def}
         |> discrete_fs_inst @{type_name nat} @{thm perm_nat_def}
         |> discrete_cp_inst @{type_name nat} @{thm perm_nat_def}
         |> discrete_pt_inst @{type_name bool} @{thm perm_bool_def}
         |> discrete_fs_inst @{type_name bool} @{thm perm_bool_def}
         |> discrete_cp_inst @{type_name bool} @{thm perm_bool_def}
         |> discrete_pt_inst @{type_name int} @{thm perm_int_def}
         |> discrete_fs_inst @{type_name int} @{thm perm_int_def}
         |> discrete_cp_inst @{type_name int} @{thm perm_int_def}
         |> discrete_pt_inst @{type_name char} @{thm perm_char_def}
         |> discrete_fs_inst @{type_name char} @{thm perm_char_def}
         |> discrete_cp_inst @{type_name char} @{thm perm_char_def}
        end;


       (* abbreviations for some lemmas *)
       (*===============================*)
       val abs_fun_pi          = @{thm "Nominal.abs_fun_pi"};
       val abs_fun_pi_ineq     = @{thm "Nominal.abs_fun_pi_ineq"};
       val abs_fun_eq          = @{thm "Nominal.abs_fun_eq"};
       val abs_fun_eq'         = @{thm "Nominal.abs_fun_eq'"};
       val abs_fun_fresh       = @{thm "Nominal.abs_fun_fresh"};
       val abs_fun_fresh'      = @{thm "Nominal.abs_fun_fresh'"};
       val dj_perm_forget      = @{thm "Nominal.dj_perm_forget"};
       val dj_pp_forget        = @{thm "Nominal.dj_perm_perm_forget"};
       val fresh_iff           = @{thm "Nominal.fresh_abs_fun_iff"};
       val fresh_iff_ineq      = @{thm "Nominal.fresh_abs_fun_iff_ineq"};
       val abs_fun_supp        = @{thm "Nominal.abs_fun_supp"};
       val abs_fun_supp_ineq   = @{thm "Nominal.abs_fun_supp_ineq"};
       val pt_swap_bij         = @{thm "Nominal.pt_swap_bij"};
       val pt_swap_bij'        = @{thm "Nominal.pt_swap_bij'"};
       val pt_fresh_fresh      = @{thm "Nominal.pt_fresh_fresh"};
       val pt_bij              = @{thm "Nominal.pt_bij"};
       val pt_perm_compose     = @{thm "Nominal.pt_perm_compose"};
       val pt_perm_compose'    = @{thm "Nominal.pt_perm_compose'"};
       val perm_app            = @{thm "Nominal.pt_fun_app_eq"};
       val at_fresh            = @{thm "Nominal.at_fresh"};
       val at_fresh_ineq       = @{thm "Nominal.at_fresh_ineq"};
       val at_calc             = @{thms "Nominal.at_calc"};
       val at_swap_simps       = @{thms "Nominal.at_swap_simps"};
       val at_supp             = @{thm "Nominal.at_supp"};
       val dj_supp             = @{thm "Nominal.dj_supp"};
       val fresh_left_ineq     = @{thm "Nominal.pt_fresh_left_ineq"};
       val fresh_left          = @{thm "Nominal.pt_fresh_left"};
       val fresh_right_ineq    = @{thm "Nominal.pt_fresh_right_ineq"};
       val fresh_right         = @{thm "Nominal.pt_fresh_right"};
       val fresh_bij_ineq      = @{thm "Nominal.pt_fresh_bij_ineq"};
       val fresh_bij           = @{thm "Nominal.pt_fresh_bij"};
       val fresh_star_bij_ineq = @{thms "Nominal.pt_fresh_star_bij_ineq"};
       val fresh_star_bij      = @{thms "Nominal.pt_fresh_star_bij"};
       val fresh_eqvt          = @{thm "Nominal.pt_fresh_eqvt"};
       val fresh_eqvt_ineq     = @{thm "Nominal.pt_fresh_eqvt_ineq"};
       val fresh_star_eqvt     = @{thms "Nominal.pt_fresh_star_eqvt"};
       val fresh_star_eqvt_ineq= @{thms "Nominal.pt_fresh_star_eqvt_ineq"};
       val set_diff_eqvt       = @{thm "Nominal.pt_set_diff_eqvt"};
       val in_eqvt             = @{thm "Nominal.pt_in_eqvt"};
       val eq_eqvt             = @{thm "Nominal.pt_eq_eqvt"};
       val all_eqvt            = @{thm "Nominal.pt_all_eqvt"};
       val ex_eqvt             = @{thm "Nominal.pt_ex_eqvt"};
       val ex1_eqvt            = @{thm "Nominal.pt_ex1_eqvt"};
       val the_eqvt            = @{thm "Nominal.pt_the_eqvt"};
       val pt_pi_rev           = @{thm "Nominal.pt_pi_rev"};
       val pt_rev_pi           = @{thm "Nominal.pt_rev_pi"};
       val at_exists_fresh     = @{thm "Nominal.at_exists_fresh"};
       val at_exists_fresh'    = @{thm "Nominal.at_exists_fresh'"};
       val fresh_perm_app_ineq = @{thm "Nominal.pt_fresh_perm_app_ineq"};
       val fresh_perm_app      = @{thm "Nominal.pt_fresh_perm_app"};    
       val fresh_aux           = @{thm "Nominal.pt_fresh_aux"};  
       val pt_perm_supp_ineq   = @{thm "Nominal.pt_perm_supp_ineq"};
       val pt_perm_supp        = @{thm "Nominal.pt_perm_supp"};
       val subseteq_eqvt       = @{thm "Nominal.pt_subseteq_eqvt"};
       val insert_eqvt         = @{thm "Nominal.pt_insert_eqvt"};
       val set_eqvt            = @{thm "Nominal.pt_set_eqvt"};
       val perm_set_eq         = @{thm "Nominal.perm_set_eq"};

       (* Now we collect and instantiate some lemmas w.r.t. all atom      *)
       (* types; this allows for example to use abs_perm (which is a      *)
       (* collection of theorems) instead of thm abs_fun_pi with explicit *)
       (* instantiations.                                                 *)
       val (_, thy33) =
         let

             (* takes a theorem thm and a list of theorems [t1,..,tn]            *)
             (* produces a list of theorems of the form [t1 RS thm,..,tn RS thm] *) 
             fun instR thm thms = map (fn ti => ti RS thm) thms;

             (* takes a theorem thm and a list of theorems [(t1,m1),..,(tn,mn)]  *)
             (* produces a list of theorems of the form [[t1,m1] MRS thm,..,[tn,mn] MRS thm] *) 
             fun instRR thm thms = map (fn (ti,mi) => [ti,mi] MRS thm) thms;

             (* takes two theorem lists (hopefully of the same length ;o)                *)
             (* produces a list of theorems of the form                                  *)
             (* [t1 RS m1,..,tn RS mn] where [t1,..,tn] is thms1 and [m1,..,mn] is thms2 *) 
             fun inst_zip thms1 thms2 = map (fn (t1,t2) => t1 RS t2) (thms1 ~~ thms2);

             (* takes a theorem list of the form [l1,...,ln]              *)
             (* and a list of theorem lists of the form                   *)
             (* [[h11,...,h1m],....,[hk1,....,hkm]                        *)
             (* produces the list of theorem lists                        *)
             (* [[l1 RS h11,...,l1 RS h1m],...,[ln RS hk1,...,ln RS hkm]] *)
             fun inst_mult thms thmss = map (fn (t,ts) => instR t ts) (thms ~~ thmss);

             (* FIXME: these lists do not need to be created dynamically again *)

             
             (* list of all at_inst-theorems *)
             val ats = map (fn ak => Global_Theory.get_thm thy32 ("at_"^ak^"_inst")) ak_names
             (* list of all pt_inst-theorems *)
             val pts = map (fn ak => Global_Theory.get_thm thy32 ("pt_"^ak^"_inst")) ak_names
             (* list of all cp_inst-theorems as a collection of lists*)
             val cps = 
                 let fun cps_fun ak1 ak2 =  Global_Theory.get_thm thy32 ("cp_"^ak1^"_"^ak2^"_inst")
                 in map (fn aki => (map (cps_fun aki) ak_names)) ak_names end; 
             (* list of all cp_inst-theorems that have different atom types *)
             val cps' = 
                let fun cps'_fun ak1 ak2 = 
                if ak1=ak2 then NONE else SOME (Global_Theory.get_thm thy32 ("cp_"^ak1^"_"^ak2^"_inst"))
                in map (fn aki => (map_filter I (map (cps'_fun aki) ak_names))) ak_names end;
             (* list of all dj_inst-theorems *)
             val djs = 
               let fun djs_fun ak1 ak2 = 
                     if ak1=ak2 then NONE else SOME(Global_Theory.get_thm thy32 ("dj_"^ak2^"_"^ak1))
               in map_filter I (map_product djs_fun ak_names ak_names) end;
             (* list of all fs_inst-theorems *)
             val fss = map (fn ak => Global_Theory.get_thm thy32 ("fs_"^ak^"_inst")) ak_names
             (* list of all at_inst-theorems *)
             val fs_axs = map (fn ak => Global_Theory.get_thm thy32 ("fs_"^ak^"1")) ak_names

             fun inst_pt thms = maps (fn ti => instR ti pts) thms;
             fun inst_at thms = maps (fn ti => instR ti ats) thms;
             fun inst_fs thms = maps (fn ti => instR ti fss) thms;
             fun inst_cp thms cps = flat (inst_mult thms cps);
             fun inst_pt_at thms = maps (fn ti => instRR ti (pts ~~ ats)) thms;
             fun inst_dj thms = maps (fn ti => instR ti djs) thms;
             fun inst_pt_pt_at_cp thms = inst_cp (inst_zip ats (inst_zip pts (inst_pt thms))) cps;
             fun inst_pt_at_fs thms = inst_zip (inst_fs [fs1]) (inst_zip ats (inst_pt thms));
             fun inst_pt_pt_at_cp thms =
                 let val i_pt_pt_at = inst_zip ats (inst_zip pts (inst_pt thms));
                     val i_pt_pt_at_cp = inst_cp i_pt_pt_at cps';
                 in i_pt_pt_at_cp end;
             fun inst_pt_pt_at_cp_dj thms = inst_zip djs (inst_pt_pt_at_cp thms);
           in
            thy32 
            |>   add_thmss_string [(("alpha", inst_pt_at [abs_fun_eq]),[])]
            ||>> add_thmss_string [(("alpha'", inst_pt_at [abs_fun_eq']),[])]
            ||>> add_thmss_string [(("alpha_fresh", inst_pt_at [abs_fun_fresh]),[])]
            ||>> add_thmss_string [(("alpha_fresh'", inst_pt_at [abs_fun_fresh']),[])]
            ||>> add_thmss_string [(("perm_swap", inst_pt_at [pt_swap_bij] @ inst_pt_at [pt_swap_bij']),[])]
            ||>> add_thmss_string 
              let val thms1 = inst_at at_swap_simps
                  and thms2 = inst_dj [dj_perm_forget]
              in [(("swap_simps", thms1 @ thms2),[])] end 
            ||>> add_thmss_string 
              let val thms1 = inst_pt_at [pt_pi_rev];
                  val thms2 = inst_pt_at [pt_rev_pi];
              in [(("perm_pi_simp",thms1 @ thms2),[])] end
            ||>> add_thmss_string [(("perm_fresh_fresh", inst_pt_at [pt_fresh_fresh]),[])]
            ||>> add_thmss_string [(("perm_bij", inst_pt_at [pt_bij]),[])]
            ||>> add_thmss_string 
              let val thms1 = inst_pt_at [pt_perm_compose];
                  val thms2 = instR cp1 (Library.flat cps');
              in [(("perm_compose",thms1 @ thms2),[])] end
            ||>> add_thmss_string [(("perm_compose'",inst_pt_at [pt_perm_compose']),[])] 
            ||>> add_thmss_string [(("perm_app", inst_pt_at [perm_app]),[])]
            ||>> add_thmss_string [(("supp_atm", (inst_at [at_supp]) @ (inst_dj [dj_supp])),[])]
            ||>> add_thmss_string [(("exists_fresh", inst_at [at_exists_fresh]),[])]
            ||>> add_thmss_string [(("exists_fresh'", inst_at [at_exists_fresh']),[])]
            ||>> add_thmss_string
              let
                val thms1 = inst_pt_at [all_eqvt];
                val thms2 = map (fold_rule [inductive_forall_def]) thms1
              in
                [(("all_eqvt", thms1 @ thms2), [NominalThmDecls.eqvt_force_add])]
              end
            ||>> add_thmss_string [(("ex_eqvt", inst_pt_at [ex_eqvt]),[NominalThmDecls.eqvt_force_add])]
            ||>> add_thmss_string [(("ex1_eqvt", inst_pt_at [ex1_eqvt]),[NominalThmDecls.eqvt_force_add])]
            ||>> add_thmss_string [(("the_eqvt", inst_pt_at [the_eqvt]),[NominalThmDecls.eqvt_force_add])]
            ||>> add_thmss_string 
              let val thms1 = inst_at [at_fresh]
                  val thms2 = inst_dj [at_fresh_ineq]
              in [(("fresh_atm", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_at at_calc
                  and thms2 = inst_dj [dj_perm_forget]
              in [(("calc_atm", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [abs_fun_pi]
                  and thms2 = inst_pt_pt_at_cp [abs_fun_pi_ineq]
              in [(("abs_perm", thms1 @ thms2),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_dj [dj_perm_forget]
                  and thms2 = inst_dj [dj_pp_forget]
              in [(("perm_dj", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at_fs [fresh_iff]
                  and thms2 = inst_pt_at [fresh_iff]
                  and thms3 = inst_pt_pt_at_cp_dj [fresh_iff_ineq]
            in [(("abs_fresh", thms1 @ thms2 @ thms3),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [abs_fun_supp]
                  and thms2 = inst_pt_at_fs [abs_fun_supp]
                  and thms3 = inst_pt_pt_at_cp_dj [abs_fun_supp_ineq]
              in [(("abs_supp", thms1 @ thms2 @ thms3),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_left]
                  and thms2 = inst_pt_pt_at_cp [fresh_left_ineq]
              in [(("fresh_left", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_right]
                  and thms2 = inst_pt_pt_at_cp [fresh_right_ineq]
              in [(("fresh_right", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_bij]
                  and thms2 = inst_pt_pt_at_cp [fresh_bij_ineq]
              in [(("fresh_bij", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at fresh_star_bij
                  and thms2 = maps (fn ti => inst_pt_pt_at_cp [ti]) fresh_star_bij_ineq
              in [(("fresh_star_bij", thms1 @ thms2),[])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_eqvt]
                  and thms2 = inst_pt_pt_at_cp_dj [fresh_eqvt_ineq]
              in [(("fresh_eqvt", thms1 @ thms2),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at fresh_star_eqvt
                  and thms2 = maps (fn ti => inst_pt_pt_at_cp_dj [ti]) fresh_star_eqvt_ineq
              in [(("fresh_star_eqvt", thms1 @ thms2),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [in_eqvt]
              in [(("in_eqvt", thms1),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [eq_eqvt]
              in [(("eq_eqvt", thms1),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [set_diff_eqvt]
              in [(("set_diff_eqvt", thms1),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [subseteq_eqvt]
              in [(("subseteq_eqvt", thms1),[NominalThmDecls.eqvt_add])] end
            ||>> add_thmss_string [(("insert_eqvt", inst_pt_at [insert_eqvt]), [NominalThmDecls.eqvt_add])]
            ||>> add_thmss_string [(("set_eqvt", inst_pt_at [set_eqvt]), [NominalThmDecls.eqvt_add])]
            ||>> add_thmss_string [(("perm_set_eq", inst_pt_at [perm_set_eq]), [])]
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_aux]
                  and thms2 = inst_pt_pt_at_cp_dj [fresh_perm_app_ineq] 
              in  [(("fresh_aux", thms1 @ thms2),[])] end  
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [fresh_perm_app]
                  and thms2 = inst_pt_pt_at_cp_dj [fresh_perm_app_ineq] 
              in  [(("fresh_perm_app", thms1 @ thms2),[])] end 
            ||>> add_thmss_string
              let val thms1 = inst_pt_at [pt_perm_supp]
                  and thms2 = inst_pt_pt_at_cp [pt_perm_supp_ineq] 
              in  [(("supp_eqvt", thms1 @ thms2),[NominalThmDecls.eqvt_add])] end  
            ||>> add_thmss_string [(("fin_supp",fs_axs),[])]
           end;

    in 
      NominalData.map (fold Symtab.update (full_ak_names ~~ map make_atom_info
        (pt_ax_classes ~~
         fs_ax_classes ~~
         map (fn cls => Symtab.make (full_ak_names ~~ cls)) cp_ax_classes ~~
         prm_cons_thms ~~ prm_inst_thms ~~
         map (fn ths => Symtab.make (full_ak_names ~~ ths)) cp_thms ~~
         map (fn thss => Symtab.make
           (map_filter (fn (s, [th]) => SOME (s, th) | _ => NONE)
              (full_ak_names ~~ thss))) dj_thms))) thy33
    end;


(* syntax und parsing *)

val _ =
  Outer_Syntax.command "atom_decl" "declare new kinds of atoms" Keyword.thy_decl
    (Scan.repeat1 Parse.name >> (Toplevel.theory o create_nom_typedecls));

end;
