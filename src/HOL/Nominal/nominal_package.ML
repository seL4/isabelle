(* $Id$ *)

signature NOMINAL_PACKAGE =
sig
  val create_nom_typedecls : string list -> theory -> theory
  val add_nominal_datatype : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory -> theory *
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list}
  val setup : (theory -> theory) list
end

structure NominalPackage (*: NOMINAL_PACKAGE *) =
struct

open DatatypeAux;

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
    val (thy2,inf_axs) = PureThy.add_axioms_i (map (fn (ak_name, T) =>
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
            |> (#1 o PureThy.add_defs_i true [((name, def2),[])])
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
    val (thy5, perm_defs) = foldl_map (fn (thy, (ak_name, T)) =>
      foldl_map (fn (thy', (ak_name', T')) =>
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
          thy' |> PureThy.add_defs_i true [((name, def),[])] 
        end) (thy, ak_names_types)) (thy4, ak_names_types);
    
    (* proves that every atom-kind is an instance of at *)
    (* lemma at_<ak>_inst:                              *)
    (* at TYPE(<ak>)                                    *)
    val (thy6, prm_cons_thms) = 
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

        val proof = fn _ => [auto_tac (claset(),simp_s)];

      in 
        ((name, prove_goalw_cterm [] (cterm_of (sign_of thy5) statement) proof), []) 
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
    val (thy8, prm_inst_thms) = 
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

        val proof = fn _ => [auto_tac (claset(),simp_s)];
      in 
        ((name, prove_goalw_cterm [] (cterm_of (sign_of thy7) statement) proof), []) 
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
     val (thy12, fs_inst_thms) = 
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

         val proof = fn _ => [auto_tac (claset(),simp_s)];
       in 
         ((name, prove_goalw_cterm [] (cterm_of (sign_of thy11) statement) proof), []) 
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
        val (thy12c, cp_thms) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
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

             val proof = fn _ => [auto_tac (claset(),simp_s), rtac cp1 1];
	   in
	     thy' |> PureThy.add_thms 
                    [((name, prove_goalw_cterm [] (cterm_of (sign_of thy') statement) proof), [])]
	   end) 
	   (thy, ak_names_types)) (thy12b, ak_names_types);
       
        (* proves for every non-trivial <ak>-combination a disjointness   *)
        (* theorem; i.e. <ak1> != <ak2>                                   *)
        (* lemma ds_<ak1>_<ak2>:                                          *)
        (* dj TYPE(<ak1>) TYPE(<ak2>)                                     *)
        val (thy12d, dj_thms) = foldl_map (fn (thy, (ak_name, T)) =>
	  foldl_map (fn (thy', (ak_name', T')) =>
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

                 val proof = fn _ => [auto_tac (claset(),simp_s)];
	       in
		   thy' |> PureThy.add_thms 
                        [((name, prove_goalw_cterm [] (cterm_of (sign_of thy') statement) proof), []) ]
	       end
           else 
            (thy',[])))  (* do nothing branch, if ak_name = ak_name' *) 
	   (thy, ak_names_types)) (thy12c, ak_names_types);

     (*<<<<<<<  pt_<ak> class instances  >>>>>>>*)
     (*=========================================*)
     
     (* some frequently used theorems *)
      val pt1 = PureThy.get_thm thy12c (Name "pt1");
      val pt2 = PureThy.get_thm thy12c (Name "pt2");
      val pt3 = PureThy.get_thm thy12c (Name "pt3");
      val at_pt_inst    = PureThy.get_thm thy12c (Name "at_pt_inst");
      val pt_bool_inst  = PureThy.get_thm thy12c (Name "pt_bool_inst");
      val pt_set_inst   = PureThy.get_thm thy12c (Name "pt_set_inst"); 
      val pt_unit_inst  = PureThy.get_thm thy12c (Name "pt_unit_inst");
      val pt_prod_inst  = PureThy.get_thm thy12c (Name "pt_prod_inst"); 
      val pt_list_inst  = PureThy.get_thm thy12c (Name "pt_list_inst");   
      val pt_optn_inst  = PureThy.get_thm thy12c (Name "pt_option_inst");   
      val pt_noptn_inst = PureThy.get_thm thy12c (Name "pt_noption_inst");   
      val pt_fun_inst   = PureThy.get_thm thy12c (Name "pt_fun_inst");     

     (* for all atom-kind combination shows that         *)
     (* every <ak> is an instance of pt_<ai>             *)
     val (thy13,_) = foldl_map (fn (thy, (ak_name, T)) =>
	 foldl_map (fn (thy', (ak_name', T')) =>
          (if ak_name = ak_name'
	   then
	     let
	      val qu_name =  Sign.full_name (sign_of thy') ak_name;
              val qu_class = Sign.full_name (sign_of thy') ("pt_"^ak_name);
              val at_inst  = PureThy.get_thm thy' (Name ("at_"^ak_name ^"_inst"));
              val proof = EVERY [AxClass.intro_classes_tac [],
                                 rtac ((at_inst RS at_pt_inst) RS pt1) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt2) 1,
                                 rtac ((at_inst RS at_pt_inst) RS pt3) 1,
                                 atac 1];
             in 
	      (AxClass.add_inst_arity_i (qu_name,[],[qu_class]) proof thy',()) 
             end
           else 
             let
	      val qu_name' = Sign.full_name (sign_of thy') ak_name';
              val qu_class = Sign.full_name (sign_of thy') ("pt_"^ak_name);
              val simp_s = HOL_basic_ss addsimps 
                           PureThy.get_thmss thy' [Name (ak_name^"_prm_"^ak_name'^"_def")];  
              val proof = EVERY [AxClass.intro_classes_tac [], auto_tac (claset(),simp_s)];
             in 
	      (AxClass.add_inst_arity_i (qu_name',[],[qu_class]) proof thy',()) 
             end)) 
	     (thy, ak_names_types)) (thy12c, ak_names_types);

     (* shows that bool is an instance of pt_<ak>     *)
     (* uses the theorem pt_bool_inst                 *)
     val (thy14,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac (pt_bool_inst RS pt1) 1,
                             rtac (pt_bool_inst RS pt2) 1,
                             rtac (pt_bool_inst RS pt3) 1,
                             atac 1];
       in 
	 (AxClass.add_inst_arity_i ("bool",[],[qu_class]) proof thy,()) 
       end) (thy13,ak_names_types); 

     (* shows that set(pt_<ak>) is an instance of pt_<ak>          *)
     (* unfolds the permutation definition and applies pt_<ak>i    *)
     val (thy15,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));  
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((pt_inst RS pt_set_inst) RS pt1) 1,
                             rtac ((pt_inst RS pt_set_inst) RS pt2) 1,
                             rtac ((pt_inst RS pt_set_inst) RS pt3) 1,
                             atac 1];
       in 
	 (AxClass.add_inst_arity_i ("set",[[qu_class]],[qu_class]) proof thy,()) 
       end) (thy14,ak_names_types); 

     (* shows that unit is an instance of pt_<ak>          *)
     val (thy16,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac (pt_unit_inst RS pt1) 1,
                             rtac (pt_unit_inst RS pt2) 1,
                             rtac (pt_unit_inst RS pt3) 1,
                             atac 1];
       in 
	 (AxClass.add_inst_arity_i ("Product_Type.unit",[],[qu_class]) proof thy,()) 
       end) (thy15,ak_names_types); 

     (* shows that *(pt_<ak>,pt_<ak>) is an instance of pt_<ak> *)
     (* uses the theorem pt_prod_inst and pt_<ak>_inst          *)
     val (thy17,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));  
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((pt_inst RS (pt_inst RS pt_prod_inst)) RS pt1) 1,
                             rtac ((pt_inst RS (pt_inst RS pt_prod_inst)) RS pt2) 1,
                             rtac ((pt_inst RS (pt_inst RS pt_prod_inst)) RS pt3) 1,
                             atac 1];
       in 
          (AxClass.add_inst_arity_i ("*",[[qu_class],[qu_class]],[qu_class]) proof thy,()) 
       end) (thy16,ak_names_types); 

     (* shows that list(pt_<ak>) is an instance of pt_<ak>     *)
     (* uses the theorem pt_list_inst and pt_<ak>_inst         *)
     val (thy18,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((pt_inst RS pt_list_inst) RS pt1) 1,
                             rtac ((pt_inst RS pt_list_inst) RS pt2) 1,
                             rtac ((pt_inst RS pt_list_inst) RS pt3) 1,
                             atac 1];      
       in 
	 (AxClass.add_inst_arity_i ("List.list",[[qu_class]],[qu_class]) proof thy,()) 
       end) (thy17,ak_names_types); 

     (* shows that option(pt_<ak>) is an instance of pt_<ak>   *)
     (* uses the theorem pt_option_inst and pt_<ak>_inst       *)
     val (thy18a,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((pt_inst RS pt_optn_inst) RS pt1) 1,
                             rtac ((pt_inst RS pt_optn_inst) RS pt2) 1,
                             rtac ((pt_inst RS pt_optn_inst) RS pt3) 1,
                             atac 1];      
       in 
	 (AxClass.add_inst_arity_i ("Datatype.option",[[qu_class]],[qu_class]) proof thy,()) 
       end) (thy18,ak_names_types); 

     (* shows that nOption(pt_<ak>) is an instance of pt_<ak>   *)
     (* uses the theorem pt_option_inst and pt_<ak>_inst       *)
     val (thy18b,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((pt_inst RS pt_noptn_inst) RS pt1) 1,
                             rtac ((pt_inst RS pt_noptn_inst) RS pt2) 1,
                             rtac ((pt_inst RS pt_noptn_inst) RS pt3) 1,
                             atac 1];      
       in 
	 (AxClass.add_inst_arity_i ("nominal.nOption",[[qu_class]],[qu_class]) proof thy,()) 
       end) (thy18a,ak_names_types); 


     (* shows that fun(pt_<ak>,pt_<ak>) is an instance of pt_<ak>     *)
     (* uses the theorem pt_list_inst and pt_<ak>_inst                *)
     val (thy19,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("pt_"^ak_name);
          val at_thm   = PureThy.get_thm thy (Name ("at_"^ak_name^"_inst"));
          val pt_inst  = PureThy.get_thm thy (Name ("pt_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((at_thm RS (pt_inst RS (pt_inst RS pt_fun_inst))) RS pt1) 1,
                             rtac ((at_thm RS (pt_inst RS (pt_inst RS pt_fun_inst))) RS pt2) 1,
                             rtac ((at_thm RS (pt_inst RS (pt_inst RS pt_fun_inst))) RS pt3) 1,
                             atac 1];      
       in 
	 (AxClass.add_inst_arity_i ("fun",[[qu_class],[qu_class]],[qu_class]) proof thy,()) 
       end) (thy18b,ak_names_types);

       (*<<<<<<<  fs_<ak> class instances  >>>>>>>*)
       (*=========================================*)
       val fs1          = PureThy.get_thm thy19 (Name "fs1");
       val fs_at_inst   = PureThy.get_thm thy19 (Name "fs_at_inst");
       val fs_unit_inst = PureThy.get_thm thy19 (Name "fs_unit_inst");
       val fs_bool_inst = PureThy.get_thm thy19 (Name "fs_bool_inst");
       val fs_prod_inst = PureThy.get_thm thy19 (Name "fs_prod_inst");
       val fs_list_inst = PureThy.get_thm thy19 (Name "fs_list_inst");

       (* shows that <ak> is an instance of fs_<ak>     *)
       (* uses the theorem at_<ak>_inst                 *)
       val (thy20,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_name =  Sign.full_name (sign_of thy) ak_name;
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val at_thm   = PureThy.get_thm thy (Name ("at_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((at_thm RS fs_at_inst) RS fs1) 1];      
       in 
	 (AxClass.add_inst_arity_i (qu_name,[],[qu_class]) proof thy,()) 
       end) (thy19,ak_names_types);  

       (* shows that unit is an instance of fs_<ak>     *)
       (* uses the theorem fs_unit_inst                 *)
       val (thy21,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac (fs_unit_inst RS fs1) 1];      
       in 
	 (AxClass.add_inst_arity_i ("Product_Type.unit",[],[qu_class]) proof thy,()) 
       end) (thy20,ak_names_types);  

       (* shows that bool is an instance of fs_<ak>     *)
       (* uses the theorem fs_bool_inst                 *)
       val (thy22,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac (fs_bool_inst RS fs1) 1];      
       in 
	 (AxClass.add_inst_arity_i ("bool",[],[qu_class]) proof thy,()) 
       end) (thy21,ak_names_types);  

       (* shows that *(fs_<ak>,fs_<ak>) is an instance of fs_<ak>     *)
       (* uses the theorem fs_prod_inst                               *)
       val (thy23,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val fs_inst  = PureThy.get_thm thy (Name ("fs_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                             rtac ((fs_inst RS (fs_inst RS fs_prod_inst)) RS fs1) 1];      
       in 
	 (AxClass.add_inst_arity_i ("*",[[qu_class],[qu_class]],[qu_class]) proof thy,()) 
       end) (thy22,ak_names_types);  

       (* shows that list(fs_<ak>) is an instance of fs_<ak>     *)
       (* uses the theorem fs_list_inst                          *)
       val (thy24,_) = foldl_map (fn (thy, (ak_name, T)) =>
       let
          val qu_class = Sign.full_name (sign_of thy) ("fs_"^ak_name);
          val fs_inst  = PureThy.get_thm thy (Name ("fs_"^ak_name^"_inst"));
          val proof = EVERY [AxClass.intro_classes_tac [],
                              rtac ((fs_inst RS fs_list_inst) RS fs1) 1];      
       in 
	 (AxClass.add_inst_arity_i ("List.list",[[qu_class]],[qu_class]) proof thy,()) 
       end) (thy23,ak_names_types);  
	   
       (*<<<<<<<  cp_<ak>_<ai> class instances  >>>>>>>*)
       (*==============================================*)
       val cp1             = PureThy.get_thm thy24 (Name "cp1");
       val cp_unit_inst    = PureThy.get_thm thy24 (Name "cp_unit_inst");
       val cp_bool_inst    = PureThy.get_thm thy24 (Name "cp_bool_inst");
       val cp_prod_inst    = PureThy.get_thm thy24 (Name "cp_prod_inst");
       val cp_list_inst    = PureThy.get_thm thy24 (Name "cp_list_inst");
       val cp_fun_inst     = PureThy.get_thm thy24 (Name "cp_fun_inst");
       val cp_option_inst  = PureThy.get_thm thy24 (Name "cp_option_inst");
       val cp_noption_inst = PureThy.get_thm thy24 (Name "cp_noption_inst");
       val pt_perm_compose = PureThy.get_thm thy24 (Name "pt_perm_compose");
       val dj_pp_forget    = PureThy.get_thm thy24 (Name "dj_perm_perm_forget");

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

       (* abbreviations for some collection of rules *)
       (*============================================*)
       val abs_fun_pi        = PureThy.get_thm thy32 (Name ("nominal.abs_fun_pi"));
       val abs_fun_pi_ineq   = PureThy.get_thm thy32 (Name ("nominal.abs_fun_pi_ineq"));
       val abs_fun_eq        = PureThy.get_thm thy32 (Name ("nominal.abs_fun_eq"));
       val dj_perm_forget    = PureThy.get_thm thy32 (Name ("nominal.dj_perm_forget"));
       val dj_pp_forget      = PureThy.get_thm thy32 (Name ("nominal.dj_perm_perm_forget"));
       val fresh_iff         = PureThy.get_thm thy32 (Name ("nominal.fresh_abs_fun_iff"));
       val fresh_iff_ineq    = PureThy.get_thm thy32 (Name ("nominal.fresh_abs_fun_iff_ineq"));
       val abs_fun_supp      = PureThy.get_thm thy32 (Name ("nominal.abs_fun_supp"));
       val abs_fun_supp_ineq = PureThy.get_thm thy32 (Name ("nominal.abs_fun_supp_ineq"));
       val pt_swap_bij       = PureThy.get_thm thy32 (Name ("nominal.pt_swap_bij"));
       val pt_fresh_fresh    = PureThy.get_thm thy32 (Name ("nominal.pt_fresh_fresh"));
       val pt_bij            = PureThy.get_thm thy32 (Name ("nominal.pt_bij"));
       val pt_perm_compose   = PureThy.get_thm thy32 (Name ("nominal.pt_perm_compose"));
       val perm_eq_app       = PureThy.get_thm thy32 (Name ("nominal.perm_eq_app"));

       (* abs_perm collects all lemmas for simplifying a permutation *)
       (* in front of an abs_fun                                     *)
       val (thy33,_) = 
	   let 
	     val name = "abs_perm"
             val thm_list = Library.flat (map (fn (ak_name, T) =>
	        let	
		  val at_inst = PureThy.get_thm thy32 (Name ("at_"^ak_name^"_inst"));
		  val pt_inst = PureThy.get_thm thy32 (Name ("pt_"^ak_name^"_inst"));	      
	          val thm = [pt_inst, at_inst] MRS abs_fun_pi
                  val thm_list = map (fn (ak_name', T') =>
                     let
                      val cp_inst = PureThy.get_thm thy32 (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
	             in
                     [pt_inst, pt_inst, at_inst, cp_inst] MRS abs_fun_pi_ineq
	             end) ak_names_types;
                 in thm::thm_list end) (ak_names_types))
           in
             (PureThy.add_thmss [((name, thm_list),[])] thy32)
           end;

        (* alpha collects all lemmas analysing an equation *)
        (* between abs_funs                                *)
        (*val (thy34,_) = 
	   let 
	     val name = "alpha"
             val thm_list = map (fn (ak_name, T) =>
	        let	
		  val at_inst = PureThy.get_thm thy33 (Name ("at_"^ak_name^"_inst"));
		  val pt_inst = PureThy.get_thm thy33 (Name ("pt_"^ak_name^"_inst"));	      
	        in
                  [pt_inst, at_inst] MRS abs_fun_eq
	        end) ak_names_types
           in
             (PureThy.add_thmss [((name, thm_list),[])] thy33)
           end;*)
 
          val (thy34,_) = 
	   let 
	     fun inst_pt_at thm ak_name =
		 let	
		   val at_inst = PureThy.get_thm thy33 (Name ("at_"^ak_name^"_inst"));
		   val pt_inst = PureThy.get_thm thy33 (Name ("pt_"^ak_name^"_inst"));	      
	         in
                     [pt_inst, at_inst] MRS thm
	         end	 

           in
            thy33 
	    |> PureThy.add_thmss   [(("alpha", map (inst_pt_at abs_fun_eq) ak_names),[])]
            |>>> PureThy.add_thmss [(("perm_swap", map (inst_pt_at pt_swap_bij) ak_names),[])]
            |>>> PureThy.add_thmss [(("perm_fresh_fresh", map (inst_pt_at pt_fresh_fresh) ak_names),[])]
            |>>> PureThy.add_thmss [(("perm_bij", map (inst_pt_at pt_bij) ak_names),[])]
            |>>> PureThy.add_thmss [(("perm_compose", map (inst_pt_at pt_perm_compose) ak_names),[])]
            |>>> PureThy.add_thmss [(("perm_app_eq", map (inst_pt_at perm_eq_app) ak_names),[])]
	   end;

         (* perm_dj collects all lemmas that forget an permutation *)
         (* when it acts on an atom of different type              *)
         val (thy35,_) = 
	   let 
	     val name = "perm_dj"
             val thm_list = Library.flat (map (fn (ak_name, T) =>
	        Library.flat (map (fn (ak_name', T') => 
                 if not (ak_name = ak_name') 
                 then 
		    let
                      val dj_inst = PureThy.get_thm thy34 (Name ("dj_"^ak_name^"_"^ak_name'));
                    in
                      [dj_inst RS dj_perm_forget, dj_inst RS dj_pp_forget]
                    end 
                 else []) ak_names_types)) ak_names_types)
           in
             (PureThy.add_thmss [((name, thm_list),[])] thy34)
           end;

         (* abs_fresh collects all lemmas for simplifying a freshness *)
         (* proposition involving an abs_fun                          *)

         val (thy36,_) = 
	   let 
	     val name = "abs_fresh"
             val thm_list = Library.flat (map (fn (ak_name, T) =>
	        let	
		  val at_inst = PureThy.get_thm thy35 (Name ("at_"^ak_name^"_inst"));
		  val pt_inst = PureThy.get_thm thy35 (Name ("pt_"^ak_name^"_inst"));
                  val fs_inst = PureThy.get_thm thy35 (Name ("fs_"^ak_name^"_inst"));	      
	          val thm = [pt_inst, at_inst, (fs_inst RS fs1)] MRS fresh_iff
                  val thm_list = Library.flat (map (fn (ak_name', T') =>
                     (if (not (ak_name = ak_name')) 
                     then
                       let
                        val cp_inst = PureThy.get_thm thy35 (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
	                val dj_inst = PureThy.get_thm thy35 (Name ("dj_"^ak_name'^"_"^ak_name));
                       in
                        [[pt_inst, pt_inst, at_inst, cp_inst, dj_inst] MRS fresh_iff_ineq]
	               end
                     else [])) ak_names_types);
                 in thm::thm_list end) (ak_names_types))
           in
             (PureThy.add_thmss [((name, thm_list),[])] thy35)
           end;

         (* abs_supp collects all lemmas for simplifying  *)
         (* support proposition involving an abs_fun      *)

         val (thy37,_) = 
	   let 
	     val name = "abs_supp"
             val thm_list = Library.flat (map (fn (ak_name, T) =>
	        let	
		  val at_inst = PureThy.get_thm thy36 (Name ("at_"^ak_name^"_inst"));
		  val pt_inst = PureThy.get_thm thy36 (Name ("pt_"^ak_name^"_inst"));
                  val fs_inst = PureThy.get_thm thy36 (Name ("fs_"^ak_name^"_inst"));	      
	          val thm1 = [pt_inst, at_inst, (fs_inst RS fs1)] MRS abs_fun_supp
                  val thm2 = [pt_inst, at_inst] MRS abs_fun_supp
                  val thm_list = Library.flat (map (fn (ak_name', T') =>
                     (if (not (ak_name = ak_name')) 
                     then
                       let
                        val cp_inst = PureThy.get_thm thy36 (Name ("cp_"^ak_name^"_"^ak_name'^"_inst"));
	                val dj_inst = PureThy.get_thm thy36 (Name ("dj_"^ak_name'^"_"^ak_name));
                       in
                        [[pt_inst, pt_inst, at_inst, cp_inst, dj_inst] MRS abs_fun_supp_ineq]
	               end
                     else [])) ak_names_types);
                 in thm1::thm2::thm_list end) (ak_names_types))
           in
             (PureThy.add_thmss [((name, thm_list),[])] thy36)
           end;

    in NominalData.put (fold Symtab.update (map (rpair ()) full_ak_names)
      (NominalData.get thy11)) thy37
    end;


(* syntax und parsing *)
structure P = OuterParse and K = OuterKeyword;

val atom_declP =
  OuterSyntax.command "atom_decl" "Declare new kinds of atoms" K.thy_decl
    (Scan.repeat1 P.name >> (Toplevel.theory o create_nom_typedecls));

val _ = OuterSyntax.add_parsers [atom_declP];

val setup = [NominalData.init];

(*=======================================================================*)

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (prems_of distinct_lemma);

fun read_typ sign ((Ts, sorts), str) =
  let
    val T = Type.no_tvars (Sign.read_typ (sign, (AList.lookup op =)
      (map (apfst (rpair ~1)) sorts)) str) handle TYPE (msg, _, _) => error msg
  in (Ts @ [T], add_typ_tfrees (T, sorts)) end;

(** taken from HOL/Tools/datatype_aux.ML **)

fun indtac indrule indnames i st =
  let
    val ts = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule));
    val ts' = HOLogic.dest_conj (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl (List.nth (prems_of st, i - 1))));
    val getP = if can HOLogic.dest_imp (hd ts) then
      (apfst SOME) o HOLogic.dest_imp else pair NONE;
    fun abstr (t1, t2) = (case t1 of
        NONE => (case filter (fn Free (s, _) => s mem indnames | _ => false)
              (term_frees t2) of
            [Free (s, T)] => absfree (s, T, t2)
          | _ => sys_error "indtac")
      | SOME (_ $ t' $ _) => Abs ("x", fastype_of t', abstract_over (t', t2)))
    val cert = cterm_of (Thm.sign_of_thm st);
    val Ps = map (cert o head_of o snd o getP) ts;
    val indrule' = cterm_instantiate (Ps ~~
      (map (cert o abstr o getP) ts')) indrule
  in
    rtac indrule' i st
  end;

fun gen_add_nominal_datatype prep_typ err flat_names new_type_names dts thy =
  let
    (* this theory is used just for parsing *)
  
    val tmp_thy = thy |>
      Theory.copy |>
      Theory.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val sign = Theory.sign_of tmp_thy;

    val atoms = atoms_of thy;
    val classes = map (NameSpace.map_base (fn s => "pt_" ^ s)) atoms;
    val cp_classes = List.concat (map (fn atom1 => map (fn atom2 =>
      Sign.intern_class thy ("cp_" ^ Sign.base_name atom1 ^ "_" ^
        Sign.base_name atom2)) atoms) atoms);
    fun augment_sort S = S union classes;
    val augment_sort_typ = map_type_tfree (fn (s, S) => TFree (s, augment_sort S));

    fun prep_constr ((constrs, sorts), (cname, cargs, mx)) =
      let val (cargs', sorts') = Library.foldl (prep_typ sign) (([], sorts), cargs)
      in (constrs @ [(cname, cargs', mx)], sorts') end

    fun prep_dt_spec ((dts, sorts), (tvs, tname, mx, constrs)) =
      let val (constrs', sorts') = Library.foldl prep_constr (([], sorts), constrs)
      in (dts @ [(tvs, tname, mx, constrs')], sorts') end

    val (dts', sorts) = Library.foldl prep_dt_spec (([], []), dts);
    val sorts' = map (apsnd augment_sort) sorts;
    val tyvars = map #1 dts';

    val types_syntax = map (fn (tvs, tname, mx, constrs) => (tname, mx)) dts';
    val constr_syntax = map (fn (tvs, tname, mx, constrs) =>
      map (fn (cname, cargs, mx) => (cname, mx)) constrs) dts';

    val ps = map (fn (_, n, _, _) =>
      (Sign.full_name sign n, Sign.full_name sign (n ^ "_Rep"))) dts;
    val rps = map Library.swap ps;

    fun replace_types (Type ("nominal.ABS", [T, U])) = 
          Type ("fun", [T, Type ("nominal.nOption", [replace_types U])])
      | replace_types (Type (s, Ts)) =
          Type (getOpt (AList.lookup op = ps s, s), map replace_types Ts)
      | replace_types T = T;

    fun replace_types' (Type (s, Ts)) =
          Type (getOpt (AList.lookup op = rps s, s), map replace_types' Ts)
      | replace_types' T = T;

    val dts'' = map (fn (tvs, tname, mx, constrs) => (tvs, tname ^ "_Rep", NoSyn,
      map (fn (cname, cargs, mx) => (cname,
        map (augment_sort_typ o replace_types) cargs, NoSyn)) constrs)) dts';

    val new_type_names' = map (fn n => n ^ "_Rep") new_type_names;
    val full_new_type_names' = map (Sign.full_name (sign_of thy)) new_type_names';

    val (thy1, {induction, ...}) =
      DatatypePackage.add_datatype_i err flat_names new_type_names' dts'' thy;

    val SOME {descr, ...} = Symtab.lookup
      (DatatypePackage.get_datatypes thy1) (hd full_new_type_names');
    val typ_of_dtyp = typ_of_dtyp descr sorts';
    fun nth_dtyp i = typ_of_dtyp (DtRec i);

    (**** define permutation functions ****)

    val permT = mk_permT (TFree ("'x", HOLogic.typeS));
    val pi = Free ("pi", permT);
    val perm_types = map (fn (i, _) =>
      let val T = nth_dtyp i
      in permT --> T --> T end) descr;
    val perm_names = replicate (length new_type_names) "nominal.perm" @
      DatatypeProp.indexify_names (map (fn i => Sign.full_name (sign_of thy1)
        ("perm_" ^ name_of_typ (nth_dtyp i)))
          (length new_type_names upto length descr - 1));
    val perm_names_types = perm_names ~~ perm_types;

    val perm_eqs = List.concat (map (fn (i, (_, _, constrs)) =>
      let val T = nth_dtyp i
      in map (fn (cname, dts) => 
        let
          val Ts = map typ_of_dtyp dts;
          val names = DatatypeProp.make_tnames Ts;
          val args = map Free (names ~~ Ts);
          val c = Const (cname, Ts ---> T);
          fun perm_arg (dt, x) =
            let val T = type_of x
            in if is_rec_type dt then
                let val (Us, _) = strip_type T
                in list_abs (map (pair "x") Us,
                  Const (List.nth (perm_names_types, body_index dt)) $ pi $
                    list_comb (x, map (fn (i, U) =>
                      Const ("nominal.perm", permT --> U --> U) $
                        (Const ("List.rev", permT --> permT) $ pi) $
                        Bound i) ((length Us - 1 downto 0) ~~ Us)))
                end
              else Const ("nominal.perm", permT --> T --> T) $ pi $ x
            end;  
        in
          (("", HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const (List.nth (perm_names_types, i)) $
               Free ("pi", mk_permT (TFree ("'x", HOLogic.typeS))) $
               list_comb (c, args),
             list_comb (c, map perm_arg (dts ~~ args))))), [])
        end) constrs
      end) descr);

    val (thy2, perm_simps) = thy1 |>
      Theory.add_consts_i (map (fn (s, T) => (Sign.base_name s, T, NoSyn))
        (List.drop (perm_names_types, length new_type_names))) |>
      PrimrecPackage.add_primrec_i "" perm_eqs;

    (**** prove that permutation functions introduced by unfolding are ****)
    (**** equivalent to already existing permutation functions         ****)

    val _ = warning ("length descr: " ^ string_of_int (length descr));
    val _ = warning ("length new_type_names: " ^ string_of_int (length new_type_names));

    val perm_indnames = DatatypeProp.make_tnames (map body_type perm_types);
    val perm_fun_def = PureThy.get_thm thy2 (Name "perm_fun_def");

    val unfolded_perm_eq_thms =
      if length descr = length new_type_names then []
      else map standard (List.drop (split_conj_thm
        (prove_goalw_cterm [] (cterm_of thy2 
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
            (map (fn (c as (s, T), x) =>
               let val [T1, T2] = binder_types T
               in HOLogic.mk_eq (Const c $ pi $ Free (x, T2),
                 Const ("nominal.perm", T) $ pi $ Free (x, T2))
               end)
             (perm_names_types ~~ perm_indnames)))))
          (fn _ => [indtac induction perm_indnames 1,
            ALLGOALS (asm_full_simp_tac
              (simpset_of thy2 addsimps [perm_fun_def]))])),
        length new_type_names));

    (**** prove [] \<bullet> t = t ****)

    val _ = warning "perm_empty_thms";

    val perm_empty_thms = List.concat (map (fn a =>
      let val permT = mk_permT (Type (a, []))
      in map standard (List.take (split_conj_thm
        (prove_goalw_cterm [] (cterm_of thy2
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
            (map (fn ((s, T), x) => HOLogic.mk_eq
                (Const (s, permT --> T --> T) $
                   Const ("List.list.Nil", permT) $ Free (x, T),
                 Free (x, T)))
             (perm_names ~~
              map body_type perm_types ~~ perm_indnames)))))
          (fn _ => [indtac induction perm_indnames 1,
            ALLGOALS (asm_full_simp_tac (simpset_of thy2))])),
        length new_type_names))
      end)
      atoms);

    (**** prove (pi1 @ pi2) \<bullet> t = pi1 \<bullet> (pi2 \<bullet> t) ****)

    val _ = warning "perm_append_thms";

    (*FIXME: these should be looked up statically*)
    val at_pt_inst = PureThy.get_thm thy2 (Name "at_pt_inst");
    val pt2 = PureThy.get_thm thy2 (Name "pt2");

    val perm_append_thms = List.concat (map (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        val pt_inst = PureThy.get_thm thy2 (Name ("pt_" ^ Sign.base_name a ^ "_inst"));
        val pt2' = pt_inst RS pt2;
        val pt2_ax = PureThy.get_thm thy2
          (Name (NameSpace.map_base (fn s => "pt_" ^ s ^ "2") a));
      in List.take (map standard (split_conj_thm
        (prove_goalw_cterm [] (cterm_of thy2
             (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ (Const ("List.op @", permT --> permT --> permT) $
                         pi1 $ pi2) $ Free (x, T),
                       perm $ pi1 $ (perm $ pi2 $ Free (x, T)))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames)))))
           (fn _ => [indtac induction perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (simpset_of thy2 addsimps [pt2', pt2_ax]))]))),
         length new_type_names)
      end) atoms);

    (**** prove pi1 ~ pi2 ==> pi1 \<bullet> t = pi2 \<bullet> t ****)

    val _ = warning "perm_eq_thms";

    val pt3 = PureThy.get_thm thy2 (Name "pt3");
    val pt3_rev = PureThy.get_thm thy2 (Name "pt3_rev");

    val perm_eq_thms = List.concat (map (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        (*FIXME: not robust - better access these theorems using NominalData?*)
        val at_inst = PureThy.get_thm thy2 (Name ("at_" ^ Sign.base_name a ^ "_inst"));
        val pt_inst = PureThy.get_thm thy2 (Name ("pt_" ^ Sign.base_name a ^ "_inst"));
        val pt3' = pt_inst RS pt3;
        val pt3_rev' = at_inst RS (pt_inst RS pt3_rev);
        val pt3_ax = PureThy.get_thm thy2
          (Name (NameSpace.map_base (fn s => "pt_" ^ s ^ "3") a));
      in List.take (map standard (split_conj_thm
        (prove_goalw_cterm [] (cterm_of thy2 (Logic.mk_implies
             (HOLogic.mk_Trueprop (Const ("nominal.prm_eq",
                permT --> permT --> HOLogic.boolT) $ pi1 $ pi2),
              HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ pi1 $ Free (x, T),
                       perm $ pi2 $ Free (x, T))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames))))))
           (fn hyps => [cut_facts_tac hyps 1, indtac induction perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (simpset_of thy2 addsimps [pt3', pt3_rev', pt3_ax]))]))),
         length new_type_names)
      end) atoms);

    (**** prove pi1 \<bullet> (pi2 \<bullet> t) = (pi1 \<bullet> pi2) \<bullet> (pi1 \<bullet> t) ****)

    val cp1 = PureThy.get_thm thy2 (Name "cp1");
    val dj_cp = PureThy.get_thm thy2 (Name "dj_cp");
    val pt_perm_compose = PureThy.get_thm thy2 (Name "pt_perm_compose");
    val pt_perm_compose_rev = PureThy.get_thm thy2 (Name "pt_perm_compose_rev");
    val dj_perm_perm_forget = PureThy.get_thm thy2 (Name "dj_perm_perm_forget");

    fun composition_instance name1 name2 thy =
      let
        val name1' = Sign.base_name name1;
        val name2' = Sign.base_name name2;
        val cp_class = Sign.intern_class thy ("cp_" ^ name1' ^ "_" ^ name2');
        val permT1 = mk_permT (Type (name1, []));
        val permT2 = mk_permT (Type (name2, []));
        val augment = map_type_tfree
          (fn (x, S) => TFree (x, cp_class :: S));
        val Ts = map (augment o body_type) perm_types;
        val cp_inst = PureThy.get_thm thy
          (Name ("cp_" ^ name1' ^ "_" ^ name2' ^ "_inst"));
        val simps = simpset_of thy addsimps (perm_fun_def ::
          (if name1 <> name2 then
             let val dj = PureThy.get_thm thy (Name ("dj_" ^ name2' ^ "_" ^ name1'))
             in [dj RS (cp_inst RS dj_cp), dj RS dj_perm_perm_forget] end
           else
             let
               val at_inst = PureThy.get_thm thy (Name ("at_" ^ name1' ^ "_inst"));
               val pt_inst = PureThy.get_thm thy (Name ("pt_" ^ name1' ^ "_inst"))
             in
               [cp_inst RS cp1 RS sym,
                at_inst RS (pt_inst RS pt_perm_compose) RS sym,
                at_inst RS (pt_inst RS pt_perm_compose_rev) RS sym]
            end))
        val thms = split_conj_thm (prove_goalw_cterm [] (cterm_of thy
            (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
              (map (fn ((s, T), x) =>
                  let
                    val pi1 = Free ("pi1", permT1);
                    val pi2 = Free ("pi2", permT2);
                    val perm1 = Const (s, permT1 --> T --> T);
                    val perm2 = Const (s, permT2 --> T --> T);
                    val perm3 = Const ("nominal.perm", permT1 --> permT2 --> permT2)
                  in HOLogic.mk_eq
                    (perm1 $ pi1 $ (perm2 $ pi2 $ Free (x, T)),
                     perm2 $ (perm3 $ pi1 $ pi2) $ (perm1 $ pi1 $ Free (x, T)))
                  end)
                (perm_names ~~ Ts ~~ perm_indnames)))))
          (fn _ => [indtac induction perm_indnames 1,
             ALLGOALS (asm_full_simp_tac simps)]))
      in
        foldl (fn ((s, tvs), thy) => AxClass.add_inst_arity_i
            (s, replicate (length tvs) (cp_class :: classes), [cp_class])
            (AxClass.intro_classes_tac [] THEN ALLGOALS (resolve_tac thms)) thy)
          thy (full_new_type_names' ~~ tyvars)
      end;

    val (thy3, perm_thmss) = thy2 |>
      fold (fn name1 => fold (composition_instance name1) atoms) atoms |>
      curry (Library.foldr (fn ((i, (tyname, args, _)), thy) =>
        AxClass.add_inst_arity_i (tyname, replicate (length args) classes, classes)
        (AxClass.intro_classes_tac [] THEN REPEAT (EVERY
           [resolve_tac perm_empty_thms 1,
            resolve_tac perm_append_thms 1,
            resolve_tac perm_eq_thms 1, assume_tac 1])) thy))
        (List.take (descr, length new_type_names)) |>
      PureThy.add_thmss
        [((space_implode "_" new_type_names ^ "_unfolded_perm_eq",
          unfolded_perm_eq_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_empty",
          perm_empty_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_append",
          perm_append_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_eq",
          perm_eq_thms), [Simplifier.simp_add_global])];
  
    (**** Define representing sets ****)

    val _ = warning "representing sets";

    val rep_set_names = map (Sign.full_name thy3) (DatatypeProp.indexify_names
      (map (fn (i, _) => name_of_typ (nth_dtyp i) ^ "_set") descr));
    val big_rep_name =
      space_implode "_" (DatatypeProp.indexify_names (List.mapPartial
        (fn (i, ("nominal.nOption", _, _)) => NONE
          | (i, _) => SOME (name_of_typ (nth_dtyp i))) descr)) ^ "_set";
    val _ = warning ("big_rep_name: " ^ big_rep_name);

    fun strip_option (dtf as DtType ("fun", [dt, DtRec i])) =
          (case AList.lookup op = descr i of
             SOME ("nominal.nOption", _, [(_, [dt']), _]) =>
               apfst (cons dt) (strip_option dt')
           | _ => ([], dtf))
      | strip_option dt = ([], dt);

    fun make_intr s T (cname, cargs) =
      let
        fun mk_prem (dt, (j, j', prems, ts)) = 
          let
            val (dts, dt') = strip_option dt;
            val (dts', dt'') = strip_dtyp dt';
            val Ts = map typ_of_dtyp dts;
            val Us = map typ_of_dtyp dts';
            val T = typ_of_dtyp dt'';
            val free = mk_Free "x" (Us ---> T) j;
            val free' = app_bnds free (length Us);
            fun mk_abs_fun (T, (i, t)) =
              let val U = fastype_of t
              in (i + 1, Const ("nominal.abs_fun", [T, U, T] --->
                Type ("nominal.nOption", [U])) $ mk_Free "y" T i $ t)
              end
          in (j + 1, j' + length Ts,
            case dt'' of
                DtRec k => list_all (map (pair "x") Us,
                  HOLogic.mk_Trueprop (HOLogic.mk_mem (free',
                    Const (List.nth (rep_set_names, k),
                      HOLogic.mk_setT T)))) :: prems
              | _ => prems,
            snd (foldr mk_abs_fun (j', free) Ts) :: ts)
          end;

        val (_, _, prems, ts) = foldr mk_prem (1, 1, [], []) cargs;
        val concl = HOLogic.mk_Trueprop (HOLogic.mk_mem
          (list_comb (Const (cname, map fastype_of ts ---> T), ts),
           Const (s, HOLogic.mk_setT T)))
      in Logic.list_implies (prems, concl)
      end;

    val (intr_ts, ind_consts) =
      apfst List.concat (ListPair.unzip (List.mapPartial
        (fn ((_, ("nominal.nOption", _, _)), _) => NONE
          | ((i, (_, _, constrs)), rep_set_name) =>
              let val T = nth_dtyp i
              in SOME (map (make_intr rep_set_name T) constrs,
                Const (rep_set_name, HOLogic.mk_setT T))
              end)
                (descr ~~ rep_set_names)));

    val (thy4, {raw_induct = rep_induct, intrs = rep_intrs, ...}) =
      setmp InductivePackage.quiet_mode false
        (InductivePackage.add_inductive_i false true big_rep_name false true false
           ind_consts (map (fn x => (("", x), [])) intr_ts) []) thy3;

    (**** Prove that representing set is closed under permutation ****)

    val _ = warning "proving closure under permutation...";

    val perm_indnames' = List.mapPartial
      (fn (x, (_, ("nominal.nOption", _, _))) => NONE | (x, _) => SOME x)
      (perm_indnames ~~ descr);

    fun mk_perm_closed name = map (fn th => standard (th RS mp))
      (List.take (split_conj_thm (prove_goalw_cterm [] (cterm_of thy4 
        (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map
           (fn (S, x) =>
              let
                val S = map_term_types (map_type_tfree
                  (fn (s, cs) => TFree (s, cs union cp_classes))) S;
                val T = HOLogic.dest_setT (fastype_of S);
                val permT = mk_permT (Type (name, []))
              in HOLogic.mk_imp (HOLogic.mk_mem (Free (x, T), S),
                HOLogic.mk_mem (Const ("nominal.perm", permT --> T --> T) $
                  Free ("pi", permT) $ Free (x, T), S))
              end) (ind_consts ~~ perm_indnames')))))
        (fn _ =>  (* CU: added perm_fun_def in the final tactic in order to deal with funs *)
           [indtac rep_induct [] 1,
            ALLGOALS (simp_tac (simpset_of thy4 addsimps
              (symmetric perm_fun_def :: PureThy.get_thms thy4 (Name ("abs_perm"))))),
            ALLGOALS (resolve_tac rep_intrs 
               THEN_ALL_NEW (asm_full_simp_tac (simpset_of thy4 addsimps [perm_fun_def])))])),
        length new_type_names));

    (* FIXME: theorems are stored in database for testing only *)
    val perm_closed_thmss = map mk_perm_closed atoms;
    val (thy5, _) = PureThy.add_thmss [(("perm_closed",
      List.concat perm_closed_thmss), [])] thy4;

    (**** typedef ****)

    val _ = warning "defining type...";

    val (thy6, typedefs) =
      foldl_map (fn (thy, ((((name, mx), tvs), c), name')) =>
        setmp TypedefPackage.quiet_mode true
          (TypedefPackage.add_typedef_i false (SOME name') (name, tvs, mx) c NONE
            (rtac exI 1 THEN
              QUIET_BREADTH_FIRST (has_fewer_prems 1)
              (resolve_tac rep_intrs 1))) thy |> (fn (thy, r) =>
        let
          val permT = mk_permT (TFree (variant tvs "'a", HOLogic.typeS));
          val pi = Free ("pi", permT);
          val tvs' = map (fn s => TFree (s, the (AList.lookup op = sorts' s))) tvs;
          val T = Type (Sign.intern_type thy name, tvs');
          val Const (_, Type (_, [U])) = c
        in apsnd (pair r o hd)
          (PureThy.add_defs_i true [(("prm_" ^ name ^ "_def", Logic.mk_equals
            (Const ("nominal.perm", permT --> T --> T) $ pi $ Free ("x", T),
             Const (Sign.intern_const thy ("Abs_" ^ name), U --> T) $
               (Const ("nominal.perm", permT --> U --> U) $ pi $
                 (Const (Sign.intern_const thy ("Rep_" ^ name), T --> U) $
                   Free ("x", T))))), [])] thy)
        end))
          (thy5, types_syntax ~~ tyvars ~~
            (List.take (ind_consts, length new_type_names)) ~~ new_type_names);

    val perm_defs = map snd typedefs;
    val Abs_inverse_thms = map (#Abs_inverse o fst) typedefs;
    val Rep_thms = map (#Rep o fst) typedefs;

    (** prove that new types are in class pt_<name> **)

    val _ = warning "prove that new types are in class pt_<name> ...";

    fun pt_instance ((class, atom), perm_closed_thms) =
      fold (fn (((({Abs_inverse, Rep_inverse, Rep, ...},
        perm_def), name), tvs), perm_closed) => fn thy =>
          AxClass.add_inst_arity_i
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [AxClass.intro_classes_tac [],
              rewrite_goals_tac [perm_def],
              asm_full_simp_tac (simpset_of thy addsimps [Rep_inverse]) 1,
              asm_full_simp_tac (simpset_of thy addsimps
                [Rep RS perm_closed RS Abs_inverse]) 1,
              asm_full_simp_tac (HOL_basic_ss addsimps [PureThy.get_thm thy
                (Name ("pt_" ^ Sign.base_name atom ^ "3"))]) 1]) thy)
        (typedefs ~~ new_type_names ~~ tyvars ~~ perm_closed_thms);


    (** prove that new types are in class cp_<name1>_<name2> **)

    val _ = warning "prove that new types are in class cp_<name1>_<name2> ...";

    fun cp_instance (atom1, perm_closed_thms1) (atom2, perm_closed_thms2) thy =
      let
        val name = "cp_" ^ Sign.base_name atom1 ^ "_" ^ Sign.base_name atom2;
        val class = Sign.intern_class thy name;
        val cp1' = PureThy.get_thm thy (Name (name ^ "_inst")) RS cp1
      in fold (fn ((((({Abs_inverse, Rep_inverse, Rep, ...},
        perm_def), name), tvs), perm_closed1), perm_closed2) => fn thy =>
          AxClass.add_inst_arity_i
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [AxClass.intro_classes_tac [],
              rewrite_goals_tac [perm_def],
              asm_full_simp_tac (simpset_of thy addsimps
                ((Rep RS perm_closed1 RS Abs_inverse) ::
                 (if atom1 = atom2 then []
                  else [Rep RS perm_closed2 RS Abs_inverse]))) 1,
              DatatypeAux.cong_tac 1,
              rtac refl 1,
              rtac cp1' 1]) thy)
        (typedefs ~~ new_type_names ~~ tyvars ~~ perm_closed_thms1 ~~
          perm_closed_thms2) thy
      end;

    val thy7 = fold (fn x => fn thy => thy |>
      pt_instance x |>
      fold (cp_instance (apfst snd x)) (atoms ~~ perm_closed_thmss))
        (classes ~~ atoms ~~ perm_closed_thmss) thy6;

    (**** constructors ****)

    fun mk_abs_fun (x, t) =
      let
        val T = fastype_of x;
        val U = fastype_of t
      in
        Const ("nominal.abs_fun", T --> U --> T -->
          Type ("nominal.nOption", [U])) $ x $ t
      end;

    val typ_of_dtyp' = replace_types' o typ_of_dtyp;

    val rep_names = map (fn s =>
      Sign.intern_const thy7 ("Rep_" ^ s)) new_type_names;
    val abs_names = map (fn s =>
      Sign.intern_const thy7 ("Abs_" ^ s)) new_type_names;

    val recTs = get_rec_types descr sorts;
    val newTs' = Library.take (length new_type_names, recTs);
    val newTs = map replace_types' newTs';

    val full_new_type_names = map (Sign.full_name (sign_of thy)) new_type_names;

    fun make_constr_def tname T T' ((thy, defs, eqns), ((cname, cargs), (cname', mx))) =
      let
        fun constr_arg (dt, (j, l_args, r_args)) =
          let
            val x' = mk_Free "x" (typ_of_dtyp' dt) j;
            val (dts, dt') = strip_option dt;
            val xs = map (fn (dt, i) => mk_Free "x" (typ_of_dtyp' dt) i)
              (dts ~~ (j upto j + length dts - 1))
            val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts)
            val (dts', dt'') = strip_dtyp dt'
          in case dt'' of
              DtRec k => if k < length new_type_names then
                  (j + length dts + 1,
                   xs @ x :: l_args,
                   foldr mk_abs_fun
                     (list_abs (map (pair "z" o typ_of_dtyp') dts',
                       Const (List.nth (rep_names, k), typ_of_dtyp' dt'' -->
                         typ_of_dtyp dt'') $ app_bnds x (length dts')))
                     xs :: r_args)
                else error "nested recursion not (yet) supported"
            | _ => (j + 1, x' :: l_args, x' :: r_args)
          end

        val (_, l_args, r_args) = foldr constr_arg (1, [], []) cargs;
        val abs_name = Sign.intern_const (Theory.sign_of thy) ("Abs_" ^ tname);
        val rep_name = Sign.intern_const (Theory.sign_of thy) ("Rep_" ^ tname);
        val constrT = map fastype_of l_args ---> T;
        val lhs = list_comb (Const (Sign.full_name thy (Sign.base_name cname),
          constrT), l_args);
        val rhs = list_comb (Const (cname, map fastype_of r_args ---> T'), r_args);
        val def = Logic.mk_equals (lhs, Const (abs_name, T' --> T) $ rhs);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> T') $ lhs, rhs));
        val def_name = (Sign.base_name cname) ^ "_def";
        val (thy', [def_thm]) = thy |>
          Theory.add_consts_i [(cname', constrT, mx)] |>
          (PureThy.add_defs_i false o map Thm.no_attributes) [(def_name, def)]
      in (thy', defs @ [def_thm], eqns @ [eqn]) end;

    fun dt_constr_defs ((thy, defs, eqns, dist_lemmas),
        (((((_, (_, _, constrs)), tname), T), T'), constr_syntax)) =
      let
        val rep_const = cterm_of thy
          (Const (Sign.intern_const thy ("Rep_" ^ tname), T --> T'));
        val dist = standard (cterm_instantiate [(cterm_of thy distinct_f, rep_const)] distinct_lemma);
        val (thy', defs', eqns') = Library.foldl (make_constr_def tname T T')
          ((Theory.add_path tname thy, defs, []), constrs ~~ constr_syntax)
      in
        (parent_path flat_names thy', defs', eqns @ [eqns'], dist_lemmas @ [dist])
      end;

    val (thy8, constr_defs, constr_rep_eqns, dist_lemmas) = Library.foldl dt_constr_defs
      ((thy7, [], [], []), List.take (descr, length new_type_names) ~~
        new_type_names ~~ newTs ~~ newTs' ~~ constr_syntax);

    val abs_inject_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Abs_" ^ tname ^ "_inject"))) new_type_names;

    val rep_inject_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname ^ "_inject"))) new_type_names;

    val rep_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname))) new_type_names;

    val rep_inverse_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname ^ "_inverse"))) new_type_names;

    (* prove theorem  Rep_i (Constr_j ...) = Constr'_j ...  *)
    
    fun prove_constr_rep_thm eqn =
      let
        val inj_thms = map (fn r => r RS iffD1) abs_inject_thms;
        val rewrites = constr_defs @ map mk_meta_eq rep_inverse_thms
      in prove_goalw_cterm [] (cterm_of thy8 eqn) (fn _ =>
        [resolve_tac inj_thms 1,
         rewrite_goals_tac rewrites,
         rtac refl 3,
         resolve_tac rep_intrs 2,
         REPEAT (resolve_tac rep_thms 1)])
      end;

    val constr_rep_thmss = map (map prove_constr_rep_thm) constr_rep_eqns;

    (* prove theorem  pi \<bullet> Rep_i x = Rep_i (pi \<bullet> x) *)

    fun prove_perm_rep_perm (atom, perm_closed_thms) = map (fn th =>
      let
        val _ $ (_ $ (Rep $ x) $ _) = Logic.unvarify (prop_of th);
        val Type ("fun", [T, U]) = fastype_of Rep;
        val permT = mk_permT (Type (atom, []));
        val pi = Free ("pi", permT);
      in
        prove_goalw_cterm [] (cterm_of thy8 (HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const ("nominal.perm", permT --> U --> U) $ pi $ (Rep $ x),
             Rep $ (Const ("nominal.perm", permT --> T --> T) $ pi $ x)))))
          (fn _ => [simp_tac (HOL_basic_ss addsimps (perm_defs @ Abs_inverse_thms @
            perm_closed_thms @ Rep_thms)) 1])
      end) Rep_thms;

    val perm_rep_perm_thms = List.concat (map prove_perm_rep_perm
      (atoms ~~ perm_closed_thmss));

    (* prove distinctness theorems *)

    fun make_distincts_1 _ [] = []
      | make_distincts_1 tname ((cname, cargs)::constrs) =
          let
            val cname = Sign.intern_const thy8
              (NameSpace.append tname (Sign.base_name cname));
            val (Ts, T) = strip_type (the (Sign.const_type thy8 cname));
            val frees = map Free ((DatatypeProp.make_tnames Ts) ~~ Ts);
            val t = list_comb (Const (cname, Ts ---> T), frees);

            fun make_distincts' [] = []
              | make_distincts' ((cname', cargs')::constrs') =
                  let
                    val cname' = Sign.intern_const thy8
                      (NameSpace.append tname (Sign.base_name cname'));
                    val Ts' = binder_types (the (Sign.const_type thy8 cname'));
                    val frees' = map Free ((map ((op ^) o (rpair "'"))
                      (DatatypeProp.make_tnames Ts')) ~~ Ts');
                    val t' = list_comb (Const (cname', Ts' ---> T), frees')
                  in
                    (HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.mk_eq (t, t')))::
                      (make_distincts' constrs')
                  end

          in (make_distincts' constrs) @ (make_distincts_1 tname constrs)
          end;

    val distinct_props = map (fn ((_, (_, _, constrs)), tname) =>
        make_distincts_1 tname constrs)
      (List.take (descr, length new_type_names) ~~ new_type_names);

    val dist_rewrites = map (fn (rep_thms, dist_lemma) =>
      dist_lemma::(rep_thms @ [In0_eq, In1_eq, In0_not_In1, In1_not_In0]))
        (constr_rep_thmss ~~ dist_lemmas);

    fun prove_distinct_thms (_, []) = []
      | prove_distinct_thms (p as (rep_thms, dist_lemma), t::ts) =
          let
            val dist_thm = prove_goalw_cterm [] (cterm_of thy8 t) (fn _ =>
              [simp_tac (simpset_of thy8 addsimps (dist_lemma :: rep_thms)) 1])
          in dist_thm::(standard (dist_thm RS not_sym))::
            (prove_distinct_thms (p, ts))
          end;

    val distinct_thms = map prove_distinct_thms
      (constr_rep_thmss ~~ dist_lemmas ~~ distinct_props);

    (** prove equations for permutation functions **)

    val abs_perm = PureThy.get_thms thy8 (Name "abs_perm"); (* FIXME *)

    val perm_simps' = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = replace_types' (nth_dtyp i)
      in List.concat (map (fn (atom, perm_closed_thms) =>
          map (fn ((cname, dts), constr_rep_thm) => 
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val permT = mk_permT (Type (atom, []));
          val pi = Free ("pi", permT);

          fun perm t =
            let val T = fastype_of t
            in Const ("nominal.perm", permT --> T --> T) $ pi $ t end;

          fun constr_arg (dt, (j, l_args, r_args)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts = map typ_of_dtyp' dts;
              val xs = map (fn (T, i) => mk_Free "x" T i)
                (Ts ~~ (j upto j + length dts - 1))
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
            in case dt'' of
                DtRec k => if k < length new_type_names then
                    (j + length dts + 1,
                     xs @ x :: l_args,
                     map perm (xs @ [x]) @ r_args)
                  else error "nested recursion not (yet) supported"
              | _ => (j + 1, x' :: l_args, perm x' :: r_args)
            end

          val (_, l_args, r_args) = foldr constr_arg (1, [], []) dts;
          val c = Const (cname, map fastype_of l_args ---> T)
        in
          prove_goalw_cterm [] (cterm_of thy8
            (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (perm (list_comb (c, l_args)), list_comb (c, r_args)))))
            (fn _ =>
              [simp_tac (simpset_of thy8 addsimps (constr_rep_thm :: perm_defs)) 1,
               simp_tac (HOL_basic_ss addsimps (Rep_thms @ Abs_inverse_thms @
                 constr_defs @ perm_closed_thms)) 1,
               TRY (simp_tac (HOL_basic_ss addsimps
                 (symmetric perm_fun_def :: abs_perm)) 1),
               TRY (simp_tac (HOL_basic_ss addsimps
                 (perm_fun_def :: perm_defs @ Rep_thms @ Abs_inverse_thms @
                    perm_closed_thms)) 1)])
        end) (constrs ~~ constr_rep_thms)) (atoms ~~ perm_closed_thmss))
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** prove injectivity of constructors **)

    val rep_inject_thms' = map (fn th => th RS sym) rep_inject_thms;
    val alpha = PureThy.get_thms thy8 (Name "alpha");
    val abs_fresh = PureThy.get_thms thy8 (Name "abs_fresh");
    val fresh_def = PureThy.get_thm thy8 (Name "fresh_def");
    val supp_def = PureThy.get_thm thy8 (Name "supp_def");

    val inject_thms = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = replace_types' (nth_dtyp i)
      in List.mapPartial (fn ((cname, dts), constr_rep_thm) =>
        if null dts then NONE else SOME
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));

          fun make_inj (dt, (j, args1, args2, eqs)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val y' = mk_Free "y" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts_idx = map typ_of_dtyp' dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val ys = map (fn (T, i) => mk_Free "y" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val y = mk_Free "y" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
            in case dt'' of
                DtRec k => if k < length new_type_names then
                    (j + length dts + 1,
                     xs @ (x :: args1), ys @ (y :: args2),
                     HOLogic.mk_eq
                       (foldr mk_abs_fun x xs, foldr mk_abs_fun y ys) :: eqs)
                  else error "nested recursion not (yet) supported"
              | _ => (j + 1, x' :: args1, y' :: args2, HOLogic.mk_eq (x', y') :: eqs)
            end;

          val (_, args1, args2, eqs) = foldr make_inj (1, [], [], []) dts;
          val Ts = map fastype_of args1;
          val c = Const (cname, Ts ---> T)
        in
          prove_goalw_cterm [] (cterm_of thy8 (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (HOLogic.mk_eq (list_comb (c, args1), list_comb (c, args2)),
               foldr1 HOLogic.mk_conj eqs))))
            (fn _ =>
               [asm_full_simp_tac (simpset_of thy8 addsimps (constr_rep_thm ::
                  rep_inject_thms')) 1,
                TRY (asm_full_simp_tac (HOL_basic_ss addsimps (fresh_def :: supp_def ::
                  alpha @ abs_perm @ abs_fresh @ rep_inject_thms @
                  perm_rep_perm_thms)) 1)])
        end) (constrs ~~ constr_rep_thms)
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** equations for support and freshness **)

    val Un_assoc = PureThy.get_thm thy8 (Name "Un_assoc");
    val de_Morgan_conj = PureThy.get_thm thy8 (Name "de_Morgan_conj");
    val Collect_disj_eq = PureThy.get_thm thy8 (Name "Collect_disj_eq");
    val finite_Un = PureThy.get_thm thy8 (Name "finite_Un");

    val (supp_thms, fresh_thms) = ListPair.unzip (map ListPair.unzip
      (map (fn ((((i, (_, _, constrs)), tname), inject_thms'), perm_thms') =>
      let val T = replace_types' (nth_dtyp i)
      in List.concat (map (fn (cname, dts) => map (fn atom =>
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val atomT = Type (atom, []);

          fun process_constr (dt, (j, args1, args2)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts_idx = map typ_of_dtyp' dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
            in case dt'' of
                DtRec k => if k < length new_type_names then
                    (j + length dts + 1,
                     xs @ (x :: args1), foldr mk_abs_fun x xs :: args2)
                  else error "nested recursion not (yet) supported"
              | _ => (j + 1, x' :: args1, x' :: args2)
            end;

          val (_, args1, args2) = foldr process_constr (1, [], []) dts;
          val Ts = map fastype_of args1;
          val c = list_comb (Const (cname, Ts ---> T), args1);
          fun supp t =
            Const ("nominal.supp", fastype_of t --> HOLogic.mk_setT atomT) $ t;
          fun fresh t =
            Const ("nominal.fresh", atomT --> fastype_of t --> HOLogic.boolT) $
              Free ("a", atomT) $ t;
          val supp_thm = prove_goalw_cterm [] (cterm_of thy8
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (supp c,
                 if null dts then Const ("{}", HOLogic.mk_setT atomT)
                 else foldr1 (HOLogic.mk_binop "op Un") (map supp args2)))))
            (fn _ =>
              [simp_tac (HOL_basic_ss addsimps (supp_def ::
                 Un_assoc :: de_Morgan_conj :: Collect_disj_eq :: finite_Un ::
                 abs_perm @ abs_fresh @ inject_thms' @ perm_thms')) 1])
        in
          (supp_thm,
           prove_goalw_cterm [] (cterm_of thy8 (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (fresh c,
               if null dts then HOLogic.true_const
               else foldr1 HOLogic.mk_conj (map fresh args2)))))
             (fn _ =>
               [simp_tac (simpset_of thy8 addsimps [fresh_def, supp_thm]) 1]))
        end) atoms) constrs)
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ inject_thms ~~ perm_simps')));

    val (thy9, _) = thy8 |>
      DatatypeAux.store_thmss "distinct" new_type_names distinct_thms |>>>
      DatatypeAux.store_thmss "constr_rep" new_type_names constr_rep_thmss |>>>
      DatatypeAux.store_thmss "perm" new_type_names perm_simps' |>>>
      DatatypeAux.store_thmss "inject" new_type_names inject_thms |>>>
      DatatypeAux.store_thmss "supp" new_type_names supp_thms |>>>
      DatatypeAux.store_thmss "fresh" new_type_names fresh_thms;

  in
    (thy9, perm_eq_thms)
  end;

val add_nominal_datatype = gen_add_nominal_datatype read_typ true;


(* FIXME: The following stuff should be exported by DatatypePackage *)

local structure P = OuterParse and K = OuterKeyword in

val datatype_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.type_args -- P.name -- P.opt_infix --
    (P.$$$ "=" |-- P.enum1 "|" (P.name -- Scan.repeat P.typ -- P.opt_mixfix));

fun mk_datatype args =
  let
    val names = map (fn ((((NONE, _), t), _), _) => t | ((((SOME t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) =>
      (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in #1 o add_nominal_datatype false names specs end;

val nominal_datatypeP =
  OuterSyntax.command "nominal_datatype" "define inductive datatypes" K.thy_decl
    (P.and_list1 datatype_decl >> (Toplevel.theory o mk_datatype));

val _ = OuterSyntax.add_parsers [nominal_datatypeP];

end;

end