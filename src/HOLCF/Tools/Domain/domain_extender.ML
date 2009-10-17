(*  Title:      HOLCF/Tools/Domain/domain_extender.ML
    Author:     David von Oheimb

Theory extender for domain command, including theory syntax.
*)

signature DOMAIN_EXTENDER =
sig
  val add_domain_cmd: string ->
                      ((string * string option) list * binding * mixfix *
                       (binding * (bool * binding option * string) list * mixfix) list) list
                      -> theory -> theory
  val add_domain: string ->
                  ((string * string option) list * binding * mixfix *
                   (binding * (bool * binding option * typ) list * mixfix) list) list
                  -> theory -> theory
end;

structure Domain_Extender :> DOMAIN_EXTENDER =
struct

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------- *)
fun check_and_sort_domain
      (dtnvs : (string * typ list) list)
      (cons'' : (binding * (bool * binding option * typ) list * mixfix) list list)
      (sg : theory)
    : ((string * typ list) *
       (binding * (bool * binding option * typ) list * mixfix) list) list =
    let
      val defaultS = Sign.defaultS sg;
      val test_dupl_typs = (case duplicates (op =) (map fst dtnvs) of 
                              [] => false | dups => error ("Duplicate types: " ^ commas_quote dups));
      val test_dupl_cons =
          (case duplicates (op =) (map (Binding.name_of o first) (flat cons'')) of 
             [] => false | dups => error ("Duplicate constructors: " 
                                          ^ commas_quote dups));
      val test_dupl_sels =
          (case duplicates (op =) (map Binding.name_of (map_filter second
                                                                        (maps second (flat cons'')))) of
             [] => false | dups => error("Duplicate selectors: "^commas_quote dups));
      val test_dupl_tvars =
          exists(fn s=>case duplicates (op =) (map(fst o dest_TFree)s)of
                         [] => false | dups => error("Duplicate type arguments: " 
                                                     ^commas_quote dups)) (map snd dtnvs);
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
            val indirect_ok = ["*","Cfun.->","Ssum.++","Sprod.**","Up.u"]
            fun analyse indirect (TFree(v,s))  =
                (case AList.lookup (op =) tvars v of 
                   NONE => error ("Free type variable " ^ quote v ^ " on rhs.")
                 | SOME sort => if eq_set_string (s,defaultS) orelse
                                   eq_set_string (s,sort    )
                                then TFree(v,sort)
                                else error ("Inconsistent sort constraint" ^
                                            " for type variable " ^ quote v))
              | analyse indirect (t as Type(s,typl)) =
                (case AList.lookup (op =) dtnvs s of
                   NONE          => if s mem indirect_ok
                                    then Type(s,map (analyse false) typl)
                                    else Type(s,map (analyse true) typl)
                 | SOME typevars => if indirect 
                                    then error ("Indirect recursion of type " ^ 
                                                quote (string_of_typ sg t))
                                    else if dname <> s orelse
                                            (** BUG OR FEATURE?:
                                                mutual recursion may use different arguments **)
                                            remove_sorts typevars = remove_sorts typl 
                                    then Type(s,map (analyse true) typl)
                                    else error ("Direct recursion of type " ^ 
                                                quote (string_of_typ sg t) ^ 
                                                " with different arguments"))
              | analyse indirect (TVar _) = Imposs "extender:analyse";
            fun check_pcpo lazy T =
                let val ok = if lazy then cpo_type else pcpo_type
                in if ok sg T then T else error
                                            ("Constructor argument type is not of sort pcpo: " ^
                                             string_of_typ sg T)
                end;
            fun analyse_arg (lazy, sel, T) =
                (lazy, sel, check_pcpo lazy (analyse false T));
            fun analyse_con (b, args, mx) = (b, map analyse_arg args, mx);
          in ((dname,distinct_typevars), map analyse_con cons') end; 
    in ListPair.map analyse_equation (dtnvs,cons'')
    end; (* let *)

(* ----- calls for building new thy and thms -------------------------------- *)

fun gen_add_domain
      (prep_typ : theory -> 'a -> typ)
      (comp_dnam : string)
      (eqs''' : ((string * string option) list * binding * mixfix *
                 (binding * (bool * binding option * 'a) list * mixfix) list) list)
      (thy''' : theory) =
    let
      fun readS (SOME s) = Syntax.read_sort_global thy''' s
        | readS NONE = Sign.defaultS thy''';
      fun readTFree (a, s) = TFree (a, readS s);

      val dtnvs = map (fn (vs,dname:binding,mx,_) => 
                          (dname, map readTFree vs, mx)) eqs''';
      val cons''' = map (fn (_,_,_,cons) => cons) eqs''';
      fun thy_type  (dname,tvars,mx) = (dname, length tvars, mx);
      fun thy_arity (dname,tvars,mx) = (Sign.full_name thy''' dname, map (snd o dest_TFree) tvars, pcpoS);
      val thy'' = thy''' |> Sign.add_types (map thy_type dtnvs)
                         |> fold (AxClass.axiomatize_arity o thy_arity) dtnvs;
      val cons'' = map (map (upd_second (map (upd_third (prep_typ thy''))))) cons''';
      val dtnvs' = map (fn (dname,vs,mx) => (Sign.full_name thy''' dname,vs)) dtnvs;
      val eqs' : ((string * typ list) * (binding * (bool * binding option * typ) list * mixfix) list) list =
          check_and_sort_domain dtnvs' cons'' thy'';
      val thy' = thy'' |> Domain_Syntax.add_syntax comp_dnam eqs';
      val dts  = map (Type o fst) eqs';
      val new_dts = map (fn ((s,Ts),_) => (s, map (fst o dest_TFree) Ts)) eqs';
      fun strip ss = Library.drop (find_index (fn s => s = "'") ss + 1, ss);
      fun typid (Type  (id,_)) =
          let val c = hd (Symbol.explode (Long_Name.base_name id))
          in if Symbol.is_letter c then c else "t" end
        | typid (TFree (id,_)   ) = hd (strip (tl (Symbol.explode id)))
        | typid (TVar ((id,_),_)) = hd (tl (Symbol.explode id));
      fun one_con (con,args,mx) =
          ((Syntax.const_name mx (Binding.name_of con)),
           ListPair.map (fn ((lazy,sel,tp),vn) => mk_arg ((lazy,
                                                           DatatypeAux.dtyp_of_typ new_dts tp),
                                                          Option.map Binding.name_of sel,vn))
                        (args,(mk_var_names(map (typid o third) args)))
          ) : cons;
      val eqs = map (fn (dtnvs,cons') => (dtnvs, map one_con cons')) eqs' : eq list;
      val thy = thy' |> Domain_Axioms.add_axioms comp_dnam eqs;
      val ((rewss, take_rews), theorems_thy) =
          thy |> fold_map (fn eq => Domain_Theorems.theorems (eq, eqs)) eqs
              ||>> Domain_Theorems.comp_theorems (comp_dnam, eqs);
    in
      theorems_thy
        |> Sign.add_path (Long_Name.base_name comp_dnam)
        |> (snd o (PureThy.add_thmss [((Binding.name "rews", flat rewss @ take_rews), [])]))
        |> Sign.parent_path
    end;

val add_domain = gen_add_domain Sign.certify_typ;
val add_domain_cmd = gen_add_domain Syntax.read_typ_global;


(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val _ = OuterKeyword.keyword "lazy";

val dest_decl : (bool * binding option * string) parser =
    P.$$$ "(" |-- Scan.optional (P.$$$ "lazy" >> K true) false --
      (P.binding >> SOME) -- (P.$$$ "::" |-- P.typ)  --| P.$$$ ")" >> P.triple1
      || P.$$$ "(" |-- P.$$$ "lazy" |-- P.typ --| P.$$$ ")"
      >> (fn t => (true,NONE,t))
      || P.typ >> (fn t => (false,NONE,t));

val cons_decl =
    P.binding -- Scan.repeat dest_decl -- P.opt_mixfix;

val type_var' : (string * string option) parser =
    (P.type_ident -- Scan.option (P.$$$ "::" |-- P.!!! P.sort));

val type_args' : (string * string option) list parser =
    type_var' >> single ||
              P.$$$ "(" |-- P.!!! (P.list1 type_var' --| P.$$$ ")") ||
              Scan.succeed [];

val domain_decl =
    (type_args' -- P.binding -- P.opt_infix) --
                                             (P.$$$ "=" |-- P.enum1 "|" cons_decl);

val domains_decl =
    Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") --
                P.and_list1 domain_decl;

fun mk_domain (opt_name : string option,
               doms : ((((string * string option) list * binding) * mixfix) *
                       ((binding * (bool * binding option * string) list) * mixfix) list) list ) =
    let
      val names = map (fn (((_, t), _), _) => Binding.name_of t) doms;
      val specs : ((string * string option) list * binding * mixfix *
                   (binding * (bool * binding option * string) list * mixfix) list) list =
          map (fn (((vs, t), mx), cons) =>
                  (vs, t, mx, map (fn ((c, ds), mx) => (c, ds, mx)) cons)) doms;
      val comp_dnam =
          case opt_name of NONE => space_implode "_" names | SOME s => s;
    in add_domain_cmd comp_dnam specs end;

val _ =
    OuterSyntax.command "domain" "define recursive domains (HOLCF)" K.thy_decl
                        (domains_decl >> (Toplevel.theory o mk_domain));

end;

end;
