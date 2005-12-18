(* $Id$ *)

signature NOMINAL_ATOMS =
sig
  val create_nom_typedecls : string list -> theory -> theory
  val atoms_of : theory -> string list
  val mk_permT : typ -> typ
  val setup : (theory -> theory) list
end

structure NominalAtoms : NOMINAL_ATOMS =
struct

(* data kind 'HOL/nominal' *)

structure NominalArgs =
struct
  val name = "HOL/nominal";
  type T = unit Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ x = Symtab.merge (K true) x;

  fun print sg tab = ();
end;

structure NominalData = TheoryDataFun(NominalArgs);

fun atoms_of thy = map fst (Symtab.dest (NominalData.get thy));

(* FIXME: add to hologic.ML ? *)
fun mk_listT T = Type ("List.list", [T]);
fun mk_permT T = mk_listT (HOLogic.mk_prodT (T, T));

fun mk_Cons x xs =
  let val T = fastype_of x
  in Const ("List.list.Cons", T --> mk_listT T --> mk_listT T) $ x $ xs end;


(* this function sets up all matters related to atom-  *)
(* kinds; the user specifies a list of atom-kind names *)
(* atom_decl <ak1> ... <akn>                           *)
fun create_nom_typedecls ak_names thy =
  let
    (* declares a type-decl for every atom-kind: *) 
    (* that is typedecl <ak>                     *)
    val thy1 = TypedefPackage.add_typedecls (map (fn x => (x,[],NoSyn)) ak_names) thy;
    
    (* produces a list consisting of pairs:         *)
    (*  fst component is the atom-kind name         *)
    (*  snd component is its type                   *)
    val full_ak_names = map (Sign.intern_type (sign_of thy1)) ak_names;
    val ak_names_types = ak_names ~~ map (Type o rpair []) full_ak_names;
     
    (* adds for every atom-kind an axiom             *)
    (* <ak>_infinite: infinite (UNIV::<ak_type> set) *)
    val (inf_axs,thy2) = PureThy.add_axioms_i (map (fn (ak_name, T) =>
      let 
	val name = ak_name ^ "_infinite"
        val axiom = HOLogic.mk_Trueprop (HOLogic.mk_not
                    (HOLogic.mk_mem (HOLogic.mk_UNIV T,
                     Const ("Finite_Set.Finites", HOLogic.mk_setT (HOLogic.mk_setT T)))))
      in
	((name, axiom), []) 
      end) ak_names_types) thy1;
    
    (* declares a swapping function for every atom-kind, it is         *)
    (* const swap_<ak> :: <akT> * <akT> => <akT> => <akT>              *)
    (* swap_<ak> (a,b) c = (if a=c then b (else if b=c then a else c)) *)
    (* overloades then the general swap-function                       *) 
    val (thy3, swap_eqs) = foldl_map (fn (thy, (ak_name, T)) =>
      let
        val swapT = HOLogic.mk_prodT (T, T) --> T --> T;
        val swap_name = Sign.full_name (sign_of thy) ("swap_" ^ ak_name);
        val a = Free ("a", T);
        val b = Free ("b", T);
        val c = Free ("c", T);
        val ab = Free ("ab", HOLogic.mk_prodT (T, T))
        val cif = Const ("HOL.If", HOLogic.boolT --> T --> T --> T);
        val cswap_akname = Const (swap_name, swapT);
        val cswap = Const ("nominal.swap", swapT)

        val name = "swap_"^ak_name^"_def";
        val def1 = HOLogic.mk_Trueprop (HOLogic.mk_eq
		   (cswap_akname $ HOLogic.mk_prod (a,b) $ c,
                    cif $ HOLogic.mk_eq (a,c) $ b $ (cif $ HOLogic.mk_eq (b,c) $ a $ c)))
        val def2 = Logic.mk_equals (cswap $ ab $ c, cswap_akname $ ab $ c)
      in
        thy |> Theory.add_consts_i [("swap_" ^ ak_name, swapT, NoSyn)] 
            |> (#2 o PureThy.add_defs_i true [((name, def2),[])])
            |> PrimrecPackage.add_primrec_i "" [(("", def1),[])]            
      end) (thy2, ak_names_types);
    
    (* declares a permutation function for every atom-kind acting  *)
    (* on such atoms                                               *)
    (* const <ak>_prm_<ak> :: (<akT> * <akT>)list => akT => akT    *)
    (* <ak>_prm_<ak> []     a = a                                  *)
    (* <ak>_prm_<ak> (x#xs) a = swap_<ak> x (perm xs a)            *)
    val (thy4, prm_eqs) = foldl_map (fn (thy, (ak_name, T)) =>
      let
        val swapT = HOLogic.mk_prodT (T, T) --> T --> T;
        val swap_name = Sign.full_name (sign_of thy) ("swap_" ^ ak_name)
        val prmT = mk_permT T --> T --> T;
        val prm_name = ak_name ^ "_prm_" ^ ak_name;
        val qu_prm_name = Sign.full_name (sign_of thy) prm_name;
        val x  = Free ("x", HOLogic.mk_prodT (T, T));
        val xs = Free ("xs", mk_permT T);
        val a  = Free ("a", T) ;

        val cnil  = Const ("List.list.Nil", mk_permT T);
        
        val def1 = HOLogic.mk_Trueprop (HOLogic.mk_eq (Const (qu_prm_name, prmT) $ cnil $ a, a));

        val def2 = HOLogic.mk_Trueprop (HOLogic.mk_eq
                   (Const (qu_prm_name, prmT) $ mk_Cons x xs $ a,
                    Const (swap_name, swapT) $ x $ (Const (qu_prm_name, prmT) $ xs $ a)));
      in
        thy |> Theory.add_consts_i [(prm_name, mk_permT T --> T --> T, NoSyn)] 
            |> PrimrecPackage.add_primrec_i "" [(("", def1), []),(("", def2), [])]
      end) (thy3, ak_names_types);
    
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
          val cperm = Const ("nominal.perm", mk_permT T --> T' --> T');
          val cperm_def = Const (Sign.full_name (sign_of thy') perm_def_name, mk_permT T --> T' --> T');

          val name = ak_name ^ "_prm_" ^ ak_name' ^ "_def";
          val def = Logic.mk_equals
                    (cperm $ pi $ a, if ak_name = ak_name' then cperm_def $ pi $ a else a)
        in
          PureThy.add_defs_i true [((name, def),[])] thy'
        end) ak_names_types thy) ak_names_types thy4;
    
    (* proves that every atom-kind is an instance of at *)
    (* lemma at_<ak>_inst:                              *)
    (* at TYPE(<ak>)                                    *)
    val (prm_cons_thms,thy6) = 
      thy5 |> PureThy.add_thms (map (fn (ak_name, T) =>
      let
        val ak_name_qu = Sign.full_name (sign_of thy5) (ak_name);
        val i_type = Type(ak_name_qu,[]);
	val cat = Const ("nominal.at",(Term.itselfT i_type)  --> HOLogic.boolT);
        val at_type = Logic.mk_type i_type;
        val simp_s = HOL_basic_ss addsimps PureThy.get_thmss thy5
                                  [Name "at_def",
                                   Name (ak_name ^ "_prm_" ^ ak_name ^ "_def"),
                                   Name (ak_name ^ "_prm_" ^ ak_name ^ ".simps"),
                                   Name ("swap_" ^ ak_name ^ "_def"),
                                   Name ("swap_" ^ ak_name ^ ".simps"),
                                   Name (ak_name ^ "_infinite")]
	    
	val name = "at_"^ak_name^ "_inst";
        val statement = HOLogic.mk_Trueprop (cat $ at_type);

        val proof = fn _ => auto_tac (claset(),simp_s);

      in 
        ((name, standard (Goal.prove thy5 [] [] statement proof)), []) 
      end) ak_names_types);

    (* declares a perm-axclass for every atom-kind               *)
    (* axclass pt_<ak>                                           *)
    (* pt_<ak>1[simp]: perm [] x = x                             *)
    (* pt_<ak>2:       perm (pi1@pi2) x = perm pi1 (perm pi2 x)  *)
    (* pt_<ak>3:       pi1 ~ pi2 ==> perm pi1 x = perm pi2 x     *)
     val (thy7, pt_ax_classes) =  foldl_map (fn (thy, (ak_name, T)) =>
      let 
	  val cl_name = "pt_"^ak_name;
          val ty = TFree("'a",["HOL.type"]);
          val x   = Free ("x", ty);
          val pi1 = Free ("pi1", mk_permT T);
          val pi2 = Free ("pi2", mk_permT T);
          val cperm = Const ("nominal.perm", mk_permT T --> ty --> ty);
          val cnil  = Const ("List.list.Nil", mk_permT T);
          val cappend = Const ("List.op @",mk_permT T --> mk_permT T --> mk_permT T);
          val cprm_eq = Const ("nominal.prm_eq",mk_permT T --> mk_permT T --> HOLogic.boolT);
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
        thy |> AxClass.add_axclass_i (cl_name, ["HOL.type"])
                [((cl_name^"1", axiom1),[Simplifier.simp_add_global]), 
                 ((cl_name^"2", axiom2),[]),                           
                 ((cl_name^"3", axiom3),[])]                          
      end) (thy6,ak_names_types);

    (* proves that every pt_<ak>-type together with <ak>-type *)
    (* instance of pt                                         *)
    (* lemma pt_<ak>_inst:                                    *)
    (* pt TYPE('x::pt_<ak>) TYPE(<ak>)                        *)
    val (prm_inst_thms,thy8) = 
      thy7 |> PureThy.add_thms (map (fn (ak_name, T) =>
      let
        val ak_name_qu = Sign.full_name (sign_of thy7) (ak_name);
        val pt_name_qu = Sign.full_name (sign_of thy7) ("pt_"^ak_name);
        val i_type1 = TFree("'x",[pt_name_qu]);
        val i_type2 = Type(ak_name_qu,[]);
	val cpt = Const ("nominal.pt",(Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
        val pt_type = Logic.mk_type i_type1;
        val at_type = Logic.mk_type i_type2;
        val simp_s = HOL_basic_ss addsimps PureThy.get_thmss thy7
                                  [Name "pt_def",
                                   Name ("pt_" ^ ak_name ^ "1"),
                                   Name ("pt_" ^ ak_name ^ "2"),
                                   Name ("pt_" ^ ak_name ^ "3")];

	val name = "pt_"^ak_name^ "_inst";
        val statement = HOLogic.mk_Trueprop (cpt $ pt_type $ at_type);

        val proof = fn _ => auto_tac (claset(),simp_s);
      in 
        ((name, standard (Goal.prove thy7 [] [] statement proof)), []) 
      end) ak_names_types);

     (* declares an fs-axclass for every atom-kind       *)
     (* axclass fs_<ak>                                  *)
     (* fs_<ak>1: finite ((supp x)::<ak> set)            *)
     val (thy11, fs_ax_classes) =  foldl_map (fn (thy, (ak_name, T)) =>
       let 
	  val cl_name = "fs_"^ak_name;
	  val pt_name = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val ty = TFree("'a",["HOL.type"]);
          val x   = Free ("x", ty);
          val csupp    = Const ("nominal.supp", ty --> HOLogic.mk_setT T);
          val cfinites = Const ("Finite_Set.Finites", HOLogic.mk_setT (HOLogic.mk_setT T))
          
          val axiom1   = HOLogic.mk_Trueprop (HOLogic.mk_mem (csupp $ x, cfinites));

       in  
        thy |> AxClass.add_axclass_i (cl_name, [pt_name]) [((cl_name^"1", axiom1),[])]            
       end) (thy8,ak_names_types); 

     (* proves that every fs_<ak>-type together with <ak>-type   *)
     (* instance of fs-type                                      *)
     (* lemma abst_<ak>_inst:                                    *)
     (* fs TYPE('x::pt_<ak>) TYPE (<ak>)                         *)
     val (fs_inst_thms,thy12) = 
       thy11 |> PureThy.add_thms (map (fn (ak_name, T) =>
       let
         val ak_name_qu = Sign.full_name (sign_of thy11) (ak_name);
         val fs_name_qu = Sign.full_name (sign_of thy11) ("fs_"^ak_name);
         val i_type1 = TFree("'x",[fs_name_qu]);
         val i_type2 = Type(ak_name_qu,[]);
 	 val cfs = Const ("nominal.fs", 
                                 (Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
         val fs_type = Logic.mk_type i_type1;
         val at_type = Logic.mk_type i_type2;
	 val simp_s = HOL_basic_ss addsimps PureThy.get_thmss thy11
                                   [Name "fs_def",
                                    Name ("fs_" ^ ak_name ^ "1")];
    
	 val name = "fs_"^ak_name^ "_inst";
         val statement = HOLogic.mk_Trueprop (cfs $ fs_type $ at_type);

         val proof = fn _ => auto_tac (claset(),simp_s);
       in 
         ((name, standard (Goal.prove thy11 [] [] statement proof)), []) 
       end) ak_names_types);

       (* declares for every atom-kind combination an axclass            *)
       (* cp_<ak1>_<ak2> giving a composition property                   *)
       (* cp_<ak1>_<ak2>1: pi1 o pi2 o x = (pi1 o pi2) o (pi1 o x)       *)
        val (thy12b,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
	     let
	       val cl_name = "cp_"^ak_name^"_"^ak_name';
	       val ty = TFree("'a",["HOL.type"]);
               val x   = Free ("x", ty);
               val pi1 = Free ("pi1", mk_permT T);
	       val pi2 = Free ("pi2", mk_permT T');                  
	       val cperm1 = Const ("nominal.perm", mk_permT T  --> ty --> ty);
               val cperm2 = Const ("nominal.perm", mk_permT T' --> ty --> ty);
               val cperm3 = Const ("nominal.perm", mk_permT T  --> mk_permT T' --> mk_permT T');

               val ax1   = HOLogic.mk_Trueprop 
			   (HOLogic.mk_eq (cperm1 $ pi1 $ (cperm2 $ pi2 $ x), 
                                           cperm2 $ (cperm3 $ pi1 $ pi2) $ (cperm1 $ pi1 $ x)));
	       in  
	       (fst (AxClass.add_axclass_i (cl_name, ["HOL.type"]) [((cl_name^"1", ax1),[])] thy'),())  
	       end) 
	   (thy, ak_names_types)) (thy12, ak_names_types)

        (* proves for every <ak>-combination a cp_<ak1>_<ak2>_inst theorem;     *)
        (* lemma cp_<ak1>_<ak2>_inst:                                           *)
        (* cp TYPE('a::cp_<ak1>_<ak2>) TYPE(<ak1>) TYPE(<ak2>)                  *)
        val (cp_thms,thy12c) = fold_map (fn (ak_name, T) => fn thy =>
	 fold_map (fn (ak_name', T') => fn thy' =>
           let
             val ak_name_qu  = Sign.full_name (sign_of thy') (ak_name);
	     val ak_name_qu' = Sign.full_name (sign_of thy') (ak_name');
             val cp_name_qu  = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
             val i_type0 = TFree("'a",[cp_name_qu]);
             val i_type1 = Type(ak_name_qu,[]);
             val i_type2 = Type(ak_name_qu',[]);
	     val ccp = Const ("nominal.cp",
                             (Term.itselfT i_type0)-->(Term.itselfT i_type1)-->
                                                      (Term.itselfT i_type2)-->HOLogic.boolT);
             val at_type  = Logic.mk_type i_type1;
             val at_type' = Logic.mk_type i_type2;
	     val cp_type  = Logic.mk_type i_type0;
             val simp_s   = HOL_basic_ss addsimps PureThy.get_thmss thy' [(Name "cp_def")];
	     val cp1      = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"1"));

	     val name = "cp_"^ak_name^ "_"^ak_name'^"_inst";
             val statement = HOLogic.mk_Trueprop (ccp $ cp_type $ at_type $ at_type');

             val proof = fn _ => EVERY [auto_tac (claset(),simp_s), rtac cp1 1];
	   in
	     PureThy.add_thms [((name, standard (Goal.prove thy' [] [] statement proof)), [])] thy'
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
		 val ak_name_qu  = Sign.full_name (sign_of thy') (ak_name);
	         val ak_name_qu' = Sign.full_name (sign_of thy') (ak_name');
                 val i_type1 = Type(ak_name_qu,[]);
                 val i_type2 = Type(ak_name_qu',[]);
	         val cdj = Const ("nominal.disjoint",
                           (Term.itselfT i_type1)-->(Term.itselfT i_type2)-->HOLogic.boolT);
                 val at_type  = Logic.mk_type i_type1;
                 val at_type' = Logic.mk_type i_type2;
                 val simp_s = HOL_basic_ss addsimps PureThy.get_thmss thy' 
					   [Name "disjoint_def",
                                            Name (ak_name^"_prm_"^ak_name'^"_def"),
                                            Name (ak_name'^"_prm_"^ak_name^"_def")];

	         val name = "dj_"^ak_name^"_"^ak_name';
                 val statement = HOLogic.mk_Trueprop (cdj $ at_type $ at_type');

                 val proof = fn _ => auto_tac (claset(),simp_s);
	       in
		PureThy.add_thms [((name, standard (Goal.prove thy' [] [] statement proof)), [])] thy'
	       end
           else 
            ([],thy')))  (* do nothing branch, if ak_name = ak_name' *) 
	    ak_names_types thy) ak_names_types thy12c;

     (*<<<<<<<  pt_<ak> class instances  >>>>>>>*)
     (*=========================================*)
     (* some abbreviations for theorems *)
      val pt1           = thm "pt1";
      val pt2           = thm "pt2";
      val pt3           = thm "pt3";
      val at_pt_inst    = thm "at_pt_inst";
      val pt_set_inst   = thm "pt_set_inst"; 
      val pt_unit_inst  = thm "pt_unit_inst";
      val pt_prod_inst  = thm "pt_prod_inst"; 
      val pt_list_inst  = thm "pt_list_inst";   
      val pt_optn_inst  = thm "pt_option_inst";   
      val pt_noptn_inst = thm "pt_noption_inst";   
      val pt_fun_inst   = thm "pt_fun_inst";     

     (* for all atom-kind combination show that         *)
     (* every <ak> is an instance of pt_<ai>            *)
     val thy13 = fold (fn ak_name => fn thy =>
	fold (fn ak_name' => fn thy' =>
         let
           val qu_name =  Sign.full_name (sign_of thy') ak_name';
           val cls_name = Sign.full_name (sign_of thy') ("pt_"^ak_name);
           val at_inst  = PureThy.get_thm thy' (Name ("at_"^ak_name'^"_inst")); 

           val proof1 = EVERY [AxClass.intro_classes_tac [],
                                 rtac ((at_inst RS at_pt_inst) RS pt1) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt2) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt3) 1,
                                 atac 1];
           val simp_s = HOL_basic_ss addsimps 
                        PureThy.get_thmss thy' [Name (ak_name^"_prm_"^ak_name'^"_def")];  
           val proof2 = EVERY [AxClass.intro_classes_tac [], REPEAT (asm_simp_tac simp_s 1)];

         in
           thy'
           |> AxClass.add_inst_arity_i (qu_name,[],[cls_name])
              (if ak_name = ak_name' then proof1 else proof2)
         end) ak_names thy) ak_names thy12c;

     (* show that                       *)
     (*      fun(pt_<ak>,pt_<ak>)       *)
     (*      nOption(pt_<ak>)           *)
     (*      option(pt_<ak>)            *)
     (*      list(pt_<ak>)              *)
     (*      *(pt_<ak>,pt_<ak>)         *)
     (*      unit                       *)
     (*      set(pt_<ak>)               *)
     (* are instances of pt_<ak>        *)
     val thy18 = fold (fn ak_name => fn thy =>
       let
          val cls_name = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val at_thm   = PureThy.get_thm thy (Name ("at_"^ak_name^"_inst"));
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));
          
          fun pt_proof thm = 
	      EVERY [AxClass.intro_classes_tac [],
                     rtac (thm RS pt1) 1, rtac (thm RS pt2) 1, rtac (thm RS pt3) 1, atac 1];

          val pt_thm_fun   = at_thm RS (pt_inst RS (pt_inst RS pt_fun_inst));
          val pt_thm_noptn = pt_inst RS pt_noptn_inst; 
          val pt_thm_optn  = pt_inst RS pt_optn_inst; 
          val pt_thm_list  = pt_inst RS pt_list_inst;
          val pt_thm_prod  = pt_inst RS (pt_inst RS pt_prod_inst);
          val pt_thm_unit  = pt_unit_inst;
          val pt_thm_set   = pt_inst RS pt_set_inst
       in 
	thy
	|> AxClass.add_inst_arity_i ("fun",[[cls_name],[cls_name]],[cls_name]) (pt_proof pt_thm_fun)
        |> AxClass.add_inst_arity_i ("nominal.nOption",[[cls_name]],[cls_name]) (pt_proof pt_thm_noptn) 
        |> AxClass.add_inst_arity_i ("Datatype.option",[[cls_name]],[cls_name]) (pt_proof pt_thm_optn)
        |> AxClass.add_inst_arity_i ("List.list",[[cls_name]],[cls_name]) (pt_proof pt_thm_list)
        |> AxClass.add_inst_arity_i ("*",[[cls_name],[cls_name]],[cls_name]) (pt_proof pt_thm_prod)
        |> AxClass.add_inst_arity_i ("Product_Type.unit",[],[cls_name]) (pt_proof pt_thm_unit)
        |> AxClass.add_inst_arity_i ("set",[[cls_name]],[cls_name]) (pt_proof pt_thm_set)
     end) ak_names thy13; 

     (* show that discrete types are permutation types, finitely supported and *)
     (* have the commutation property                                          *)
     (* discrete types have a permutation operation defined as pi o x = x;     *)
     (* which renders the proofs to be simple "simp_all"-proofs.               *)            
     val thy19 =
        let 
	  fun discrete_pt_inst discrete_ty defn = 
	     fold (fn ak_name => fn thy =>
	     let
	       val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
	       val simp_s = HOL_basic_ss addsimps [defn];
               val proof = EVERY [AxClass.intro_classes_tac [], REPEAT (asm_simp_tac simp_s 1)];      
             in  
	       AxClass.add_inst_arity_i (discrete_ty,[],[qu_class]) proof thy
             end) ak_names;

          fun discrete_fs_inst discrete_ty defn = 
	     fold (fn ak_name => fn thy =>
	     let
	       val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
	       val supp_def = thm "nominal.supp_def";
               val simp_s = HOL_ss addsimps [supp_def,if_False,Collect_const,Finites.emptyI,defn];
               val proof = EVERY [AxClass.intro_classes_tac [], asm_simp_tac simp_s 1];      
             in  
	       AxClass.add_inst_arity_i (discrete_ty,[],[qu_class]) proof thy
             end) ak_names;  

          fun discrete_cp_inst discrete_ty defn = 
	     fold (fn ak_name' => (fold (fn ak_name => fn thy =>
	     let
	       val qu_class = Sign.full_name (sign_of thy) ("cp_"^ak_name^"_"^ak_name');
	       val supp_def = thm "nominal.supp_def";
               val simp_s = HOL_ss addsimps [defn];
               val proof = EVERY [AxClass.intro_classes_tac [], asm_simp_tac simp_s 1];      
             in  
	       AxClass.add_inst_arity_i (discrete_ty,[],[qu_class]) proof thy
             end) ak_names)) ak_names;  
          
        in
         thy18
         |> discrete_pt_inst "nat"  (thm "perm_nat_def")
         |> discrete_fs_inst "nat"  (thm "perm_nat_def") 
         |> discrete_cp_inst "nat"  (thm "perm_nat_def") 
         |> discrete_pt_inst "bool" (thm "perm_bool")
         |> discrete_fs_inst "bool" (thm "perm_bool")
         |> discrete_cp_inst "bool" (thm "perm_bool")
         |> discrete_pt_inst "IntDef.int" (thm "perm_int_def")
         |> discrete_fs_inst "IntDef.int" (thm "perm_int_def") 
         |> discrete_cp_inst "IntDef.int" (thm "perm_int_def") 
         |> discrete_pt_inst "List.char" (thm "perm_char_def")
         |> discrete_fs_inst "List.char" (thm "perm_char_def")
         |> discrete_cp_inst "List.char" (thm "perm_char_def")
        end;


       (*<<<<<<<  fs_<ak> class instances  >>>>>>>*)
       (*=========================================*)
       (* abbreviations for some lemmas *)
       val fs1            = thm "fs1";
       val fs_at_inst     = thm "fs_at_inst";
       val fs_unit_inst   = thm "fs_unit_inst";
       val fs_prod_inst   = thm "fs_prod_inst";
       val fs_list_inst   = thm "fs_list_inst";
       val fs_option_inst = thm "fs_option_inst";

       (* shows that <ak> is an instance of fs_<ak>     *)
       (* uses the theorem at_<ak>_inst                 *)
       (* FIXME -- needs to be done for all ak-combinations *) 
       val thy20 = fold (fn ak_name => fn thy =>
       let
          val qu_name =  Sign.full_name (sign_of thy) ak_name;
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val at_thm = PureThy.get_thm thy (Name ("at_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((at_thm RS fs_at_inst) RS fs1) 1];      
       in 
	 AxClass.add_inst_arity_i (qu_name,[],[qu_class]) proof thy 
       end) ak_names thy19;

       (* shows that                  *)
       (*    unit                     *)
       (*    *(fs_<ak>,fs_<ak>)       *)
       (*    list(fs_<ak>)            *)
       (*    option(fs_<ak>)          *) 
       (* are instances of fs_<ak>    *)

       val thy24 = fold (fn ak_name => fn thy => 
        let
          val cls_name = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val fs_inst  = PureThy.get_thm thy (Name ("fs_"^ak_name^"_inst"));
          fun fs_proof thm = EVERY [AxClass.intro_classes_tac [], rtac (thm RS fs1) 1];      

          val fs_thm_unit = fs_unit_inst;
          val fs_thm_prod = fs_inst RS (fs_inst RS fs_prod_inst);
          val fs_thm_list = fs_inst RS fs_list_inst;
          val fs_thm_optn = fs_inst RS fs_option_inst;
        in 
         thy 
         |> AxClass.add_inst_arity_i ("Product_Type.unit",[],[cls_name]) (fs_proof fs_thm_unit) 
         |> AxClass.add_inst_arity_i ("*",[[cls_name],[cls_name]],[cls_name]) (fs_proof fs_thm_prod)    
         |> AxClass.add_inst_arity_i ("List.list",[[cls_name]],[cls_name]) (fs_proof fs_thm_list)
         |> AxClass.add_inst_arity_i ("Datatype.option",[[cls_name]],[cls_name]) (fs_proof fs_thm_optn)
        end) ak_names thy20; 

       (*<<<<<<<  cp_<ak>_<ai> class instances  >>>>>>>*)
       (*==============================================*)
       (* abbreviations for some lemmas *)
       val cp1             = thm "cp1";
       val cp_unit_inst    = thm "cp_unit_inst";
       val cp_bool_inst    = thm "cp_bool_inst";
       val cp_prod_inst    = thm "cp_prod_inst";
       val cp_list_inst    = thm "cp_list_inst";
       val cp_fun_inst     = thm "cp_fun_inst";
       val cp_option_inst  = thm "cp_option_inst";
       val cp_noption_inst = thm "cp_noption_inst";
       val pt_perm_compose = thm "pt_perm_compose";
       val dj_pp_forget    = thm "dj_perm_perm_forget";

       (* shows that <aj> is an instance of cp_<ak>_<ai>  *)
       (* that needs a three-nested loop *)
       val (thy25,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          foldl_map (fn (thy'', (ak_name'', T'')) =>
            let
              val qu_name =  Sign.full_name (sign_of thy'') ak_name;
              val qu_class = Sign.full_name (sign_of thy'') ("cp_"^ak_name'^"_"^ak_name'');
              val proof =
                (if (ak_name'=ak_name'') then 
		  (let
                    val pt_inst  = PureThy.get_thm thy'' (Name ("pt_"^ak_name''^"_inst"));
		    val at_inst  = PureThy.get_thm thy'' (Name ("at_"^ak_name''^"_inst"));
                  in 
		   EVERY [AxClass.intro_classes_tac [], 
                          rtac (at_inst RS (pt_inst RS pt_perm_compose)) 1]
                  end)
		else
		  (let 
                     val dj_inst  = PureThy.get_thm thy'' (Name ("dj_"^ak_name''^"_"^ak_name'));
		     val simp_s = HOL_basic_ss addsimps 
                                        ((dj_inst RS dj_pp_forget)::
                                         (PureThy.get_thmss thy'' 
					   [Name (ak_name' ^"_prm_"^ak_name^"_def"),
                                            Name (ak_name''^"_prm_"^ak_name^"_def")]));  
		  in 
                    EVERY [AxClass.intro_classes_tac [], simp_tac simp_s 1]
                  end))
	      in
                (AxClass.add_inst_arity_i (qu_name,[],[qu_class]) proof thy'',())
	      end)
	   (thy', ak_names_types)) (thy, ak_names_types)) (thy24, ak_names_types);
      
       (* shows that unit is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                         *)
       val (thy26,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          let
            val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
            val proof = EVERY [AxClass.intro_classes_tac [],rtac (cp_unit_inst RS cp1) 1];     
	  in
            (AxClass.add_inst_arity_i ("Product_Type.unit",[],[qu_class]) proof thy',())
	  end) 
	   (thy, ak_names_types)) (thy25, ak_names_types);
       
       (* shows that bool is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                         *)
       val (thy27,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
           let
	     val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
             val proof = EVERY [AxClass.intro_classes_tac [], rtac (cp_bool_inst RS cp1) 1];     
	   in
             (AxClass.add_inst_arity_i ("bool",[],[qu_class]) proof thy',())
	   end) 
	   (thy, ak_names_types)) (thy26, ak_names_types);

       (* shows that prod is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                         *)
       val (thy28,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          let
	    val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
            val cp_inst  = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
            val proof = EVERY [AxClass.intro_classes_tac [],
                               rtac ((cp_inst RS (cp_inst RS cp_prod_inst)) RS cp1) 1];     
	  in
            (AxClass.add_inst_arity_i ("*",[[qu_class],[qu_class]],[qu_class]) proof thy',())
	  end)  
	  (thy, ak_names_types)) (thy27, ak_names_types);

       (* shows that list is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                         *)
       val (thy29,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
           let
	     val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
             val cp_inst  = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
             val proof = EVERY [AxClass.intro_classes_tac [],
                                rtac ((cp_inst RS cp_list_inst) RS cp1) 1];     
	   in
            (AxClass.add_inst_arity_i ("List.list",[[qu_class]],[qu_class]) proof thy',())
	   end) 
	   (thy, ak_names_types)) (thy28, ak_names_types);

       (* shows that function is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                             *)
       val (thy30,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          let
	    val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
            val cp_inst  = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
            val pt_inst  = PureThy.get_thm thy' (Name ("pt_"^ak_name^"_inst"));
            val at_inst  = PureThy.get_thm thy' (Name ("at_"^ak_name^"_inst"));
            val proof = EVERY [AxClass.intro_classes_tac [],
                    rtac ((at_inst RS (pt_inst RS (cp_inst RS (cp_inst RS cp_fun_inst)))) RS cp1) 1];  
	  in
            (AxClass.add_inst_arity_i ("fun",[[qu_class],[qu_class]],[qu_class]) proof thy',())
	  end) 
	  (thy, ak_names_types)) (thy29, ak_names_types);

       (* shows that option is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                           *)
       val (thy31,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          let
	    val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
            val cp_inst  = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
            val proof = EVERY [AxClass.intro_classes_tac [],
                               rtac ((cp_inst RS cp_option_inst) RS cp1) 1];     
	  in
            (AxClass.add_inst_arity_i ("Datatype.option",[[qu_class]],[qu_class]) proof thy',())
	  end) 
	  (thy, ak_names_types)) (thy30, ak_names_types);

       (* shows that nOption is an instance of cp_<ak>_<ai>     *)
       (* for every <ak>-combination                            *)
       val (thy32,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          let
	    val qu_class = Sign.full_name (sign_of thy') ("cp_"^ak_name^"_"^ak_name');
            val cp_inst  = PureThy.get_thm thy' (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
            val proof = EVERY [AxClass.intro_classes_tac [],
                               rtac ((cp_inst RS cp_noption_inst) RS cp1) 1];     
	  in
           (AxClass.add_inst_arity_i ("nominal.nOption",[[qu_class]],[qu_class]) proof thy',())
	  end) 
	  (thy, ak_names_types)) (thy31, ak_names_types);

       (* abbreviations for some lemmas *)
       (*===============================*)
       val abs_fun_pi        = thm "nominal.abs_fun_pi";
       val abs_fun_pi_ineq   = thm "nominal.abs_fun_pi_ineq";
       val abs_fun_eq        = thm "nominal.abs_fun_eq";
       val dj_perm_forget    = thm "nominal.dj_perm_forget";
       val dj_pp_forget      = thm "nominal.dj_perm_perm_forget";
       val fresh_iff         = thm "nominal.fresh_abs_fun_iff";
       val fresh_iff_ineq    = thm "nominal.fresh_abs_fun_iff_ineq";
       val abs_fun_supp      = thm "nominal.abs_fun_supp";
       val abs_fun_supp_ineq = thm "nominal.abs_fun_supp_ineq";
       val pt_swap_bij       = thm "nominal.pt_swap_bij";
       val pt_fresh_fresh    = thm "nominal.pt_fresh_fresh";
       val pt_bij            = thm "nominal.pt_bij";
       val pt_perm_compose   = thm "nominal.pt_perm_compose";
       val perm_eq_app       = thm "nominal.perm_eq_app";
       val at_fresh          = thm "nominal.at_fresh";
       val at_calc           = thms "nominal.at_calc";
       val at_supp           = thm "nominal.at_supp";
       val dj_supp           = thm "nominal.dj_supp";
       val fresh_left_ineq   = thm "nominal.pt_fresh_left_ineq";
       val fresh_left        = thm "nominal.pt_fresh_left";
       val fresh_bij_ineq    = thm "nominal.pt_fresh_bij_ineq";
       val fresh_bij         = thm "nominal.pt_fresh_bij";

       (* Now we collect and instantiate some lemmas w.r.t. all atom      *)
       (* types; this allows for example to use abs_perm (which is a      *)
       (* collection of theorems) instead of thm abs_fun_pi with explicit *)
       (* instantiations.                                                 *)
       val (_,thy33) = 
	 let 
             (* takes a theorem thm and a list of theorems [t1,..,tn]            *)
             (* produces a list of theorems of the form [t1 RS thm,..,tn RS thm] *) 
             fun instR thm thms = map (fn ti => ti RS thm) thms;

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
             val ats = map (fn ak => PureThy.get_thm thy32 (Name ("at_"^ak^"_inst"))) ak_names
             (* list of all pt_inst-theorems *)
             val pts = map (fn ak => PureThy.get_thm thy32 (Name ("pt_"^ak^"_inst"))) ak_names
             (* list of all cp_inst-theorems as a collection of lists*)
             val cps = 
		 let fun cps_fun ak1 ak2 = PureThy.get_thm thy32 (Name ("cp_"^ak1^"_"^ak2^"_inst"))
		 in map (fn aki => (map (cps_fun aki) ak_names)) ak_names end; 
             (* list of all cp_inst-theorems that have different atom types *)
             val cps' = 
		let fun cps'_fun ak1 ak2 = 
		if ak1=ak2 then NONE else SOME(PureThy.get_thm thy32 (Name ("cp_"^ak1^"_"^ak2^"_inst")))
		in map (fn aki => (List.mapPartial I (map (cps'_fun aki) ak_names))) ak_names end;
             (* list of all dj_inst-theorems *)
             val djs = 
	       let fun djs_fun (ak1,ak2) = 
		     if ak1=ak2 then NONE else SOME(PureThy.get_thm thy32 (Name ("dj_"^ak2^"_"^ak1)))
	       in List.mapPartial I (map djs_fun (Library.product ak_names ak_names)) end;
             (* list of all fs_inst-theorems *)
             val fss = map (fn ak => PureThy.get_thm thy32 (Name ("fs_"^ak^"_inst"))) ak_names

             fun inst_pt thms = Library.flat (map (fn ti => instR ti pts) thms); 
             fun inst_at thms = Library.flat (map (fn ti => instR ti ats) thms);               
             fun inst_fs thms = Library.flat (map (fn ti => instR ti fss) thms);
	     fun inst_pt_at thms = inst_zip ats (inst_pt thms);			
             fun inst_dj thms = Library.flat (map (fn ti => instR ti djs) thms);  
	     fun inst_pt_pt_at_cp thms = 
		 Library.flat (inst_mult (inst_zip ats (inst_zip pts (inst_pt thms))) cps);
             fun inst_pt_at_fs thms = inst_zip (inst_fs [fs1]) (inst_zip ats (inst_pt thms));
	     fun inst_pt_pt_at_cp thms = 
		 let val i_pt_pt_at = inst_zip ats (inst_zip pts (inst_pt thms));
                     val i_pt_pt_at_cp = Library.flat (inst_mult i_pt_pt_at cps');
		 in i_pt_pt_at_cp end;
             fun inst_pt_pt_at_cp_dj thms = inst_zip djs (inst_pt_pt_at_cp thms);
           in
            thy32 
	    |>   PureThy.add_thmss [(("alpha", inst_pt_at [abs_fun_eq]),[])]
            ||>> PureThy.add_thmss [(("perm_swap", inst_pt_at [pt_swap_bij]),[])]
            ||>> PureThy.add_thmss [(("perm_fresh_fresh", inst_pt_at [pt_fresh_fresh]),[])]
            ||>> PureThy.add_thmss [(("perm_bij", inst_pt_at [pt_bij]),[])]
            ||>> PureThy.add_thmss [(("perm_compose", inst_pt_at [pt_perm_compose]),[])]
            ||>> PureThy.add_thmss [(("perm_app_eq", inst_pt_at [perm_eq_app]),[])]
            ||>> PureThy.add_thmss [(("supp_atm", (inst_at [at_supp]) @ (inst_dj [dj_supp])),[])]
            ||>> PureThy.add_thmss [(("fresh_atm", inst_at [at_fresh]),[])]
            ||>> PureThy.add_thmss [(("calc_atm", inst_at at_calc),[])]
            ||>> PureThy.add_thmss
	      let val thms1 = inst_pt_at [abs_fun_pi]
		  and thms2 = inst_pt_pt_at_cp [abs_fun_pi_ineq]
	      in [(("abs_perm", thms1 @ thms2),[])] end
            ||>> PureThy.add_thmss
	      let val thms1 = inst_dj [dj_perm_forget]
		  and thms2 = inst_dj [dj_pp_forget]
              in [(("perm_dj", thms1 @ thms2),[])] end
            ||>> PureThy.add_thmss
	      let val thms1 = inst_pt_at_fs [fresh_iff]
		  and thms2 = inst_pt_pt_at_cp_dj [fresh_iff_ineq]
	    in [(("abs_fresh", thms1 @ thms2),[])] end
	    ||>> PureThy.add_thmss
	      let val thms1 = inst_pt_at [abs_fun_supp]
		  and thms2 = inst_pt_at_fs [abs_fun_supp]
		  and thms3 = inst_pt_pt_at_cp_dj [abs_fun_supp_ineq]
	      in [(("abs_supp", thms1 @ thms2 @ thms3),[])] end
            ||>> PureThy.add_thmss
	      let val thms1 = inst_pt_at [fresh_left]
		  and thms2 = inst_pt_pt_at_cp [fresh_left_ineq]
	      in [(("fresh_left", thms1 @ thms2),[])] end
            ||>> PureThy.add_thmss
	      let val thms1 = inst_pt_at [fresh_bij]
		  and thms2 = inst_pt_pt_at_cp [fresh_bij_ineq]
	      in [(("fresh_eqvt", thms1 @ thms2),[])] end
	   end;

    in NominalData.put (fold Symtab.update (map (rpair ()) full_ak_names)
      (NominalData.get thy11)) thy33
    end;


(* syntax und parsing *)
structure P = OuterParse and K = OuterKeyword;

val atom_declP =
  OuterSyntax.command "atom_decl" "Declare new kinds of atoms" K.thy_decl
    (Scan.repeat1 P.name >> (Toplevel.theory o create_nom_typedecls));

val _ = OuterSyntax.add_parsers [atom_declP];

val setup = [NominalData.init];

end;
