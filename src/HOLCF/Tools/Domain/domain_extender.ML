(*  Title:      HOLCF/Tools/Domain/domain_extender.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Theory extender for domain command, including theory syntax.
*)

signature DOMAIN_EXTENDER =
sig
  val add_domain_cmd:
      binding ->
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * string) list * mixfix) list) list
      -> theory -> theory

  val add_domain:
      binding ->
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * typ) list * mixfix) list) list
      -> theory -> theory

  val add_new_domain_cmd:
      binding ->
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * string) list * mixfix) list) list
      -> theory -> theory

  val add_new_domain:
      binding ->
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * typ) list * mixfix) list) list
      -> theory -> theory
end;

structure Domain_Extender :> DOMAIN_EXTENDER =
struct

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------- *)
fun check_and_sort_domain
    (arg_sort : bool -> sort)
    (dtnvs : (string * typ list) list)
    (cons'' : (binding * (bool * binding option * typ) list * mixfix) list list)
    (thy : theory)
    : ((string * typ list) *
       (binding * (bool * binding option * typ) list * mixfix) list) list =
  let
    val defaultS = Sign.defaultS thy;

    val test_dupl_typs =
      case duplicates (op =) (map fst dtnvs) of 
        [] => false | dups => error ("Duplicate types: " ^ commas_quote dups);

    val all_cons = map (Binding.name_of o first) (flat cons'');
    val test_dupl_cons =
      case duplicates (op =) all_cons of 
        [] => false | dups => error ("Duplicate constructors: " 
                                      ^ commas_quote dups);
    val all_sels =
      (map Binding.name_of o map_filter second o maps second) (flat cons'');
    val test_dupl_sels =
      case duplicates (op =) all_sels of
        [] => false | dups => error("Duplicate selectors: "^commas_quote dups);

    fun test_dupl_tvars s =
      case duplicates (op =) (map(fst o dest_TFree)s) of
        [] => false | dups => error("Duplicate type arguments: " 
                                    ^commas_quote dups);
    val test_dupl_tvars' = exists test_dupl_tvars (map snd dtnvs);

    (* test for free type variables, illegal sort constraints on rhs,
       non-pcpo-types and invalid use of recursive type;
       replace sorts in type variables on rhs *)
    fun analyse_equation ((dname,typevars),cons') = 
      let
        val tvars = map dest_TFree typevars;
        val distinct_typevars = map TFree tvars;
        fun rm_sorts (TFree(s,_)) = TFree(s,[])
          | rm_sorts (Type(s,ts)) = Type(s,remove_sorts ts)
          | rm_sorts (TVar(s,_))  = TVar(s,[])
        and remove_sorts l = map rm_sorts l;
        fun analyse indirect (TFree(v,s))  =
            (case AList.lookup (op =) tvars v of 
               NONE => error ("Free type variable " ^ quote v ^ " on rhs.")
             | SOME sort => if eq_set (op =) (s, defaultS) orelse
                               eq_set (op =) (s, sort)
                            then TFree(v,sort)
                            else error ("Inconsistent sort constraint" ^
                                        " for type variable " ^ quote v))
          | analyse indirect (t as Type(s,typl)) =
            (case AList.lookup (op =) dtnvs s of
               NONE => Type (s, map (analyse false) typl)
             | SOME typevars =>
                 if indirect 
                 then error ("Indirect recursion of type " ^ 
                             quote (string_of_typ thy t))
                 else if dname <> s orelse
                         (** BUG OR FEATURE?:
                             mutual recursion may use different arguments **)
                         remove_sorts typevars = remove_sorts typl 
                 then Type(s,map (analyse true) typl)
                 else error ("Direct recursion of type " ^ 
                             quote (string_of_typ thy t) ^ 
                             " with different arguments"))
          | analyse indirect (TVar _) = Imposs "extender:analyse";
        fun check_pcpo lazy T =
            let val sort = arg_sort lazy in
              if Sign.of_sort thy (T, sort) then T
              else error ("Constructor argument type is not of sort " ^
                          Syntax.string_of_sort_global thy sort ^ ": " ^
                          string_of_typ thy T)
            end;
        fun analyse_arg (lazy, sel, T) =
            (lazy, sel, check_pcpo lazy (analyse false T));
        fun analyse_con (b, args, mx) = (b, map analyse_arg args, mx);
      in ((dname,distinct_typevars), map analyse_con cons') end; 
  in ListPair.map analyse_equation (dtnvs,cons'')
  end; (* let *)

(* ----- calls for building new thy and thms -------------------------------- *)

type info =
     Domain_Take_Proofs.iso_info list * Domain_Take_Proofs.take_induct_info;

fun gen_add_domain
    (prep_typ : theory -> 'a -> typ)
    (add_isos : (binding * mixfix * (typ * typ)) list -> theory -> info * theory)
    (arg_sort : bool -> sort)
    (comp_dbind : binding)
    (eqs''' : ((string * string option) list * binding * mixfix *
               (binding * (bool * binding option * 'a) list * mixfix) list) list)
    (thy : theory) =
  let
    val dtnvs : (binding * typ list * mixfix) list =
      let
        fun readS (SOME s) = Syntax.read_sort_global thy s
          | readS NONE = Sign.defaultS thy;
        fun readTFree (a, s) = TFree (a, readS s);
      in
        map (fn (vs,dname:binding,mx,_) =>
                (dname, map readTFree vs, mx)) eqs'''
      end;

    fun thy_type  (dname,tvars,mx) = (dname, length tvars, mx);
    fun thy_arity (dname,tvars,mx) =
      (Sign.full_name thy dname, map (snd o dest_TFree) tvars, arg_sort false);

    (* this theory is used just for parsing and error checking *)
    val tmp_thy = thy
      |> Theory.copy
      |> Sign.add_types (map thy_type dtnvs)
      |> fold (AxClass.axiomatize_arity o thy_arity) dtnvs;

    val dbinds : binding list =
        map (fn (_,dbind,_,_) => dbind) eqs''';
    val cons''' :
        (binding * (bool * binding option * 'a) list * mixfix) list list =
        map (fn (_,_,_,cons) => cons) eqs''';
    val cons'' :
        (binding * (bool * binding option * typ) list * mixfix) list list =
        map (map (upd_second (map (upd_third (prep_typ tmp_thy))))) cons''';
    val dtnvs' : (string * typ list) list =
        map (fn (dname,vs,mx) => (Sign.full_name thy dname,vs)) dtnvs;
    val eqs' : ((string * typ list) *
        (binding * (bool * binding option * typ) list * mixfix) list) list =
        check_and_sort_domain arg_sort dtnvs' cons'' tmp_thy;
    val dts : typ list = map (Type o fst) eqs';

    fun mk_arg_typ (lazy, dest_opt, T) = if lazy then mk_uT T else T;
    fun mk_con_typ (bind, args, mx) =
        if null args then oneT else foldr1 mk_sprodT (map mk_arg_typ args);
    fun mk_eq_typ (_, cons) = foldr1 mk_ssumT (map mk_con_typ cons);
    val repTs : typ list = map mk_eq_typ eqs';

    val iso_spec : (binding * mixfix * (typ * typ)) list =
        map (fn ((dbind, _, mx), eq) => (dbind, mx, eq))
          (dtnvs ~~ (dts ~~ repTs));

    val ((iso_infos, take_info), thy) = add_isos iso_spec thy;

    val new_dts : (string * string list) list =
        map (fn ((s,Ts),_) => (s, map (fst o dest_TFree) Ts)) eqs';
    fun one_con (con,args,mx) : cons =
        (Binding.name_of con,  (* FIXME preverse binding (!?) *)
         ListPair.map (fn ((lazy,sel,tp),vn) =>
           mk_arg ((lazy, Datatype_Aux.dtyp_of_typ new_dts tp), vn))
                      (args, Datatype_Prop.make_tnames (map third args)));
    val eqs : eq list =
        map (fn (dtnvs,cons') => (dtnvs, map one_con cons')) eqs';

    val ((rewss, take_rews), theorems_thy) =
        thy
          |> fold_map (fn (((dbind, eq), (_,cs)), info) =>
                Domain_Theorems.theorems (eq, eqs) dbind cs info take_info)
             (dbinds ~~ eqs ~~ eqs' ~~ iso_infos)
          ||>> Domain_Theorems.comp_theorems (comp_dbind, eqs) take_info;
  in
    theorems_thy
      |> Global_Theory.add_thmss
           [((Binding.qualified true "rews" comp_dbind,
              flat rewss @ take_rews), [])]
      |> snd
  end;

fun define_isos (spec : (binding * mixfix * (typ * typ)) list) =
  let
    fun prep (dbind, mx, (lhsT, rhsT)) =
      let val (dname, vs) = dest_Type lhsT;
      in (map (fst o dest_TFree) vs, dbind, mx, rhsT, NONE) end;
  in
    Domain_Isomorphism.domain_isomorphism (map prep spec)
  end;

fun pcpo_arg lazy = if lazy then @{sort cpo} else @{sort pcpo};
fun rep_arg lazy = @{sort sfp};

val add_domain =
    gen_add_domain Sign.certify_typ Domain_Axioms.add_axioms pcpo_arg;

val add_new_domain =
    gen_add_domain Sign.certify_typ define_isos rep_arg;

val add_domain_cmd =
    gen_add_domain Syntax.read_typ_global Domain_Axioms.add_axioms pcpo_arg;

val add_new_domain_cmd =
    gen_add_domain Syntax.read_typ_global define_isos rep_arg;


(** outer syntax **)

val _ = Keyword.keyword "lazy";

val dest_decl : (bool * binding option * string) parser =
  Parse.$$$ "(" |-- Scan.optional (Parse.$$$ "lazy" >> K true) false --
    (Parse.binding >> SOME) -- (Parse.$$$ "::" |-- Parse.typ)  --| Parse.$$$ ")" >> Parse.triple1
    || Parse.$$$ "(" |-- Parse.$$$ "lazy" |-- Parse.typ --| Parse.$$$ ")"
    >> (fn t => (true,NONE,t))
    || Parse.typ >> (fn t => (false,NONE,t));

val cons_decl =
  Parse.binding -- Scan.repeat dest_decl -- Parse.opt_mixfix;

val domain_decl =
  (Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix) --
    (Parse.$$$ "=" |-- Parse.enum1 "|" cons_decl);

val domains_decl =
  Scan.option (Parse.$$$ "(" |-- Parse.binding --| Parse.$$$ ")") --
    Parse.and_list1 domain_decl;

fun mk_domain
    (definitional : bool)
    (opt_name : binding option,
     doms : ((((string * string option) list * binding) * mixfix) *
             ((binding * (bool * binding option * string) list) * mixfix) list) list ) =
  let
    val names = map (fn (((_, t), _), _) => Binding.name_of t) doms;
    val specs : ((string * string option) list * binding * mixfix *
                 (binding * (bool * binding option * string) list * mixfix) list) list =
        map (fn (((vs, t), mx), cons) =>
                (vs, t, mx, map (fn ((c, ds), mx) => (c, ds, mx)) cons)) doms;
    val comp_dbind =
        case opt_name of NONE => Binding.name (space_implode "_" names)
                       | SOME s => s;
  in
    if definitional 
    then add_new_domain_cmd comp_dbind specs
    else add_domain_cmd comp_dbind specs
  end;

val _ =
  Outer_Syntax.command "domain" "define recursive domains (HOLCF)"
    Keyword.thy_decl (domains_decl >> (Toplevel.theory o mk_domain false));

val _ =
  Outer_Syntax.command "new_domain" "define recursive domains (HOLCF)"
    Keyword.thy_decl (domains_decl >> (Toplevel.theory o mk_domain true));

end;
