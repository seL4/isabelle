(*  Title:      HOL/Statespace/state_space.ML
    Author:     Norbert Schirmer, TU Muenchen
*)

signature STATE_SPACE =
sig
  val distinct_compsN : string
  val getN : string
  val putN : string
  val injectN : string
  val namespaceN : string
  val projectN : string
  val valuetypesN : string

  val namespace_definition :
     bstring ->
     typ ->
     (xstring, string) Expression.expr * (binding * string option * mixfix) list ->
     string list -> string list -> theory -> theory

  val define_statespace :
     string list ->
     string ->
     ((string * bool) * (string list * bstring * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_statespace_i :
     string option ->
     string list ->
     string ->
     ((string * bool) * (typ list * bstring * (string * string) list)) list ->
     (string * typ) list -> theory -> theory

  val statespace_decl :
     ((string list * bstring) *
       (((string * bool) * (string list * xstring * (bstring * bstring) list)) list *
        (bstring * string) list)) parser


  val neq_x_y : Proof.context -> term -> term -> thm option
  val distinctNameSolver : Simplifier.solver
  val distinctTree_tac : Proof.context -> int -> tactic
  val distinct_simproc : Simplifier.simproc


  val get_comp : Context.generic -> string -> (typ * string) option
  val get_silent : Context.generic -> bool
  val set_silent : bool -> Context.generic -> Context.generic

  val gen_lookup_tr : Proof.context -> term -> string -> term
  val lookup_swap_tr : Proof.context -> term list -> term
  val lookup_tr : Proof.context -> term list -> term
  val lookup_tr' : Proof.context -> term list -> term

  val gen_update_tr :
     bool -> Proof.context -> string -> term -> term -> term
  val update_tr : Proof.context -> term list -> term
  val update_tr' : Proof.context -> term list -> term
end;

structure StateSpace : STATE_SPACE =
struct

(* Names *)

val distinct_compsN = "distinct_names"
val namespaceN = "_namespace"
val valuetypesN = "_valuetypes"
val projectN = "project"
val injectN = "inject"
val getN = "get"
val putN = "put"
val project_injectL = "StateSpaceLocale.project_inject";


(* Library *)

fun fold1 f xs = fold f (tl xs) (hd xs)
fun fold1' f [] x = x
  | fold1' f xs _ = fold1 f xs

fun sublist_idx eq xs ys =
  let
    fun sublist n xs ys =
         if is_prefix eq xs ys then SOME n
         else (case ys of [] => NONE
               | (y::ys') => sublist (n+1) xs ys')
  in sublist 0 xs ys end;

fun is_sublist eq xs ys = is_some (sublist_idx eq xs ys);

fun sorted_subset eq [] ys = true
  | sorted_subset eq (x::xs) [] = false
  | sorted_subset eq (x::xs) (y::ys) = if eq (x,y) then sorted_subset eq xs ys
                                       else sorted_subset eq (x::xs) ys;



type namespace_info =
 {declinfo: (typ*string) Termtab.table, (* type, name of statespace *)
  distinctthm: thm Symtab.table,
  silent: bool
 };

structure NameSpaceData = Generic_Data
(
  type T = namespace_info;
  val empty = {declinfo = Termtab.empty, distinctthm = Symtab.empty, silent = false};
  val extend = I;
  fun merge
    ({declinfo=declinfo1, distinctthm=distinctthm1, silent=silent1},
      {declinfo=declinfo2, distinctthm=distinctthm2, silent=silent2}) : T =
    {declinfo = Termtab.merge (K true) (declinfo1, declinfo2),
     distinctthm = Symtab.merge (K true) (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
);

fun make_namespace_data declinfo distinctthm silent =
     {declinfo=declinfo,distinctthm=distinctthm,silent=silent};


fun delete_declinfo n ctxt =
  let val {declinfo,distinctthm,silent} = NameSpaceData.get ctxt;
  in NameSpaceData.put
       (make_namespace_data (Termtab.delete_safe n declinfo) distinctthm silent) ctxt
  end;


fun update_declinfo (n,v) ctxt =
  let val {declinfo,distinctthm,silent} = NameSpaceData.get ctxt;
  in NameSpaceData.put
      (make_namespace_data (Termtab.update (n,v) declinfo) distinctthm silent) ctxt
  end;

fun set_silent silent ctxt =
  let val {declinfo,distinctthm,...} = NameSpaceData.get ctxt;
  in NameSpaceData.put
      (make_namespace_data declinfo distinctthm silent) ctxt
  end;

val get_silent = #silent o NameSpaceData.get;

fun expression_no_pos (expr, fixes) : Expression.expression =
  (map (fn (name, inst) => ((name, Position.none), inst)) expr, fixes);

fun prove_interpretation_in ctxt_tac (name, expr) thy =
   thy
   |> Expression.sublocale_cmd I (name, Position.none) (expression_no_pos expr) []
   |> Proof.global_terminal_proof
         ((Method.Basic (fn ctxt => SIMPLE_METHOD (ctxt_tac ctxt)), Position.no_range), NONE)
   |> Proof_Context.theory_of

fun add_locale name expr elems thy =
  thy
  |> Expression.add_locale I (Binding.name name) (Binding.name name) expr elems
  |> snd
  |> Local_Theory.exit;

fun add_locale_cmd name expr elems thy =
  thy
  |> Expression.add_locale_cmd I (Binding.name name) Binding.empty (expression_no_pos expr) elems
  |> snd
  |> Local_Theory.exit;

type statespace_info =
 {args: (string * sort) list, (* type arguments *)
  parents: (typ list * string * string option list) list,
             (* type instantiation, state-space name, component renamings *)
  components: (string * typ) list,
  types: typ list (* range types of state space *)
 };

structure StateSpaceData = Generic_Data
(
  type T = statespace_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun add_statespace name args parents components types ctxt =
     StateSpaceData.put
      (Symtab.update_new (name, {args=args,parents=parents,
                                components=components,types=types}) (StateSpaceData.get ctxt))
      ctxt;

fun get_statespace ctxt name =
      Symtab.lookup (StateSpaceData.get ctxt) name;


fun mk_free ctxt name =
  if Variable.is_fixed ctxt name orelse Variable.is_declared ctxt name
  then
    let val n' = Variable.intern_fixed ctxt name
    in SOME (Free (n', Proof_Context.infer_type ctxt (n', dummyT))) end
  else NONE


fun get_dist_thm ctxt name = Symtab.lookup (#distinctthm (NameSpaceData.get ctxt)) name;
fun get_comp ctxt name =
     Option.mapPartial
       (Termtab.lookup (#declinfo (NameSpaceData.get ctxt)))
       (mk_free (Context.proof_of ctxt) name);


(*** Tactics ***)

fun neq_x_y ctxt x y =
  (let
    val dist_thm = the (get_dist_thm (Context.Proof ctxt) (#1 (dest_Free x)));
    val ctree = cprop_of dist_thm |> Thm.dest_comb |> #2 |> Thm.dest_comb |> #2;
    val tree = term_of ctree;
    val x_path = the (DistinctTreeProver.find_tree x tree);
    val y_path = the (DistinctTreeProver.find_tree y tree);
    val thm = DistinctTreeProver.distinctTreeProver dist_thm x_path y_path;
  in SOME thm
  end handle Option.Option => NONE)

fun distinctTree_tac ctxt = SUBGOAL (fn (goal, i) =>
  (case goal of
    Const (@{const_name Trueprop}, _) $
      (Const (@{const_name Not}, _) $
        (Const (@{const_name HOL.eq}, _) $ (x as Free _) $ (y as Free _))) =>
      (case neq_x_y ctxt x y of
        SOME neq => rtac neq i
      | NONE => no_tac)
  | _ => no_tac));

val distinctNameSolver =
  mk_solver "distinctNameSolver" (distinctTree_tac o Simplifier.the_context);

val distinct_simproc =
  Simplifier.simproc_global @{theory HOL} "StateSpace.distinct_simproc" ["x = y"]
    (fn thy => fn ss => (fn (Const (@{const_name HOL.eq},_)$(x as Free _)$(y as Free _)) =>
        (case try Simplifier.the_context ss of
          SOME ctxt =>
            Option.map (fn neq => DistinctTreeProver.neq_to_eq_False OF [neq])
              (neq_x_y ctxt x y)
        | NONE => NONE)
      | _ => NONE));

local
  val ss = HOL_basic_ss
in
fun interprete_parent name dist_thm_name parent_expr thy =
  let
    fun solve_tac ctxt = CSUBGOAL (fn (goal, i) =>
      let
        val distinct_thm = Proof_Context.get_thm ctxt dist_thm_name;
        val rule = DistinctTreeProver.distinct_implProver distinct_thm goal;
      in rtac rule i end);

    fun tac ctxt =
      Locale.intro_locales_tac true ctxt [] THEN ALLGOALS (solve_tac ctxt);

  in
    thy |> prove_interpretation_in tac (name, parent_expr)
  end;

end;

fun namespace_definition name nameT parent_expr parent_comps new_comps thy =
  let
    val all_comps = parent_comps @ new_comps;
    val vars = (map (fn n => (Binding.name n, NONE, NoSyn)) all_comps);
    val full_name = Sign.full_bname thy name;
    val dist_thm_name = distinct_compsN;

    val dist_thm_full_name = dist_thm_name;
    fun comps_of_thm thm = prop_of thm
             |> (fn (_$(_$t)) => DistinctTreeProver.dest_tree t) |> map (fst o dest_Free);

    fun type_attr phi = Thm.declaration_attribute (fn thm => fn context =>
      (case context of
        Context.Theory _ => context
      | Context.Proof ctxt =>
        let
          val {declinfo,distinctthm=tt,silent} = NameSpaceData.get context;
          val all_names = comps_of_thm thm;
          fun upd name tt =
               (case Symtab.lookup tt name of
                 SOME dthm => if sorted_subset (op =) (comps_of_thm dthm) all_names
                              then Symtab.update (name,thm) tt else tt
               | NONE => Symtab.update (name,thm) tt)

          val tt' = tt |> fold upd all_names;
          val activate_simproc =
            Simplifier.map_ss
              (Simplifier.with_context (Context_Position.set_visible false ctxt)
                (fn ss => ss addsimprocs [distinct_simproc]));
          val context' =
              context
              |> NameSpaceData.put {declinfo=declinfo,distinctthm=tt',silent=silent}
              |> activate_simproc;
        in context' end));

    val attr = Attrib.internal type_attr;

    val assume =
      ((Binding.name dist_thm_name, [attr]),
        [(HOLogic.Trueprop $
          (Const (@{const_name all_distinct}, Type (@{type_name tree}, [nameT]) --> HOLogic.boolT) $
            DistinctTreeProver.mk_tree (fn n => Free (n, nameT)) nameT
              (sort fast_string_ord all_comps)), [])]);
  in
    thy
    |> add_locale name ([], vars) [Element.Assumes [assume]]
    |> Proof_Context.theory_of
    |> interprete_parent name dist_thm_full_name parent_expr
  end;

fun encode_dot x = if x= #"." then #"_" else x;

fun encode_type (TFree (s, _)) = s
  | encode_type (TVar ((s,i),_)) = "?" ^ s ^ string_of_int i
  | encode_type (Type (n,Ts)) =
      let
        val Ts' = fold1' (fn x => fn y => x ^ "_" ^ y) (map encode_type Ts) "";
        val n' = String.map encode_dot n;
      in if Ts'="" then n' else Ts' ^ "_" ^ n' end;

fun project_name T = projectN ^"_"^encode_type T;
fun inject_name T = injectN ^"_"^encode_type T;

fun project_free T pT V = Free (project_name T, V --> pT);
fun inject_free T pT V = Free (inject_name T, pT --> V);

fun get_name n = getN ^ "_" ^ n;
fun put_name n = putN ^ "_" ^ n;
fun get_const n T nT V = Free (get_name n, (nT --> V) --> T);
fun put_const n T nT V = Free (put_name n, T --> (nT --> V) --> (nT --> V));

fun lookup_const T nT V =
  Const (@{const_name StateFun.lookup}, (V --> T) --> nT --> (nT --> V) --> T);

fun update_const T nT V =
  Const (@{const_name StateFun.update},
    (V --> T) --> (T --> V) --> nT --> (T --> T) --> (nT --> V) --> (nT --> V));

fun K_const T = Const (@{const_name K_statefun}, T --> T --> T);


fun add_declaration name decl thy =
  thy
  |> Named_Target.init I name
  |> (fn lthy => Local_Theory.declaration {syntax = false, pervasive = false} (decl lthy) lthy)
  |> Local_Theory.exit_global;

fun parent_components thy (Ts, pname, renaming) =
  let
    val ctxt = Context.Theory thy;
    fun rename [] xs = xs
      | rename (NONE::rs)  (x::xs) = x::rename rs xs
      | rename (SOME r::rs) ((x,T)::xs) = (r,T)::rename rs xs;
    val {args, parents, components, ...} = the (Symtab.lookup (StateSpaceData.get ctxt) pname);
    val inst = map fst args ~~ Ts;
    val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
    val parent_comps =
      maps (fn (Ts',n,rs) => parent_components thy (map subst Ts', n, rs)) parents;
    val all_comps = rename renaming (parent_comps @ map (apsnd subst) components);
  in all_comps end;

fun take_upto i xs = List.take(xs,i) handle General.Subscript => xs;

fun statespace_definition state_type args name parents parent_comps components thy =
  let
    val full_name = Sign.full_bname thy name;
    val all_comps = parent_comps @ components;

    val components' = map (fn (n,T) => (n,(T,full_name))) components;
    val all_comps' = map (fn (n,T) => (n,(T,full_name))) all_comps;

    fun parent_expr (prefix, (_, n, rs)) =
      (suffix namespaceN n, (prefix, Expression.Positional rs));
    val parents_expr = map parent_expr parents;
    fun distinct_types Ts =
      let val tab = fold (fn T => fn tab => Typtab.update (T,()) tab) Ts Typtab.empty;
      in map fst (Typtab.dest tab) end;

    val Ts = distinct_types (map snd all_comps);
    val arg_names = map fst args;
    val valueN = singleton (Name.variant_list arg_names) "'value";
    val nameN = singleton (Name.variant_list (valueN :: arg_names)) "'name";
    val valueT = TFree (valueN, Sign.defaultS thy);
    val nameT = TFree (nameN, Sign.defaultS thy);
    val stateT = nameT --> valueT;
    fun projectT T = valueT --> T;
    fun injectT T = T --> valueT;
    val locinsts = map (fn T => (project_injectL,
                    ((encode_type T,false),Expression.Positional
                             [SOME (Free (project_name T,projectT T)),
                              SOME (Free ((inject_name T,injectT T)))]))) Ts;
    val locs = maps (fn T => [(Binding.name (project_name T),NONE,NoSyn),
                                     (Binding.name (inject_name T),NONE,NoSyn)]) Ts;
    val constrains = maps (fn T => [(project_name T,projectT T),(inject_name T,injectT T)]) Ts;

    fun interprete_parent_valuetypes (prefix, (Ts, pname, _)) thy =
      let
        val {args,types,...} =
             the (Symtab.lookup (StateSpaceData.get (Context.Theory thy)) pname);
        val inst = map fst args ~~ Ts;
        val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
        val pars = maps ((fn T => [project_name T,inject_name T]) o subst) types;

        val expr = ([(suffix valuetypesN name,
                     (prefix, Expression.Positional (map SOME pars)))],[]);
      in
        prove_interpretation_in (ALLGOALS o solve_tac o Assumption.all_prems_of)
          (suffix valuetypesN name, expr) thy
      end;

    fun interprete_parent (prefix, (_, pname, rs)) =
      let
        val expr = ([(pname, (prefix, Expression.Positional rs))],[])
      in prove_interpretation_in
           (fn ctxt => Locale.intro_locales_tac false ctxt [])
           (full_name, expr) end;

    fun declare_declinfo updates lthy phi ctxt =
      let
        fun upd_prf ctxt =
          let
            fun upd (n,v) =
              let
                val nT = Proof_Context.infer_type (Local_Theory.target_of lthy) (n, dummyT)
              in Context.proof_map
                  (update_declinfo (Morphism.term phi (Free (n,nT)),v))
              end;
          in ctxt |> fold upd updates end;

      in Context.mapping I upd_prf ctxt end;

   fun string_of_typ T =
      Print_Mode.setmp []
        (Syntax.string_of_typ (Config.put show_sorts true (Syntax.init_pretty_global thy))) T;
   val fixestate = (case state_type of
         NONE => []
       | SOME s =>
          let
            val fx = Element.Fixes [(Binding.name s,SOME (string_of_typ stateT),NoSyn)];
            val cs = Element.Constrains
                       (map (fn (n,T) =>  (n,string_of_typ T))
                         ((map (fn (n,_) => (n,nameT)) all_comps) @
                          constrains))
          in [fx,cs] end
       )


  in thy
     |> namespace_definition
           (suffix namespaceN name) nameT (parents_expr,[])
           (map fst parent_comps) (map fst components)
     |> Context.theory_map (add_statespace full_name args (map snd parents) components [])
     |> add_locale (suffix valuetypesN name) (locinsts,locs) []
     |> Proof_Context.theory_of
     |> fold interprete_parent_valuetypes parents
     |> add_locale_cmd name
              ([(suffix namespaceN full_name ,(("",false),Expression.Named [])),
                (suffix valuetypesN full_name,(("",false),Expression.Named  []))],[]) fixestate
     |> Proof_Context.theory_of
     |> fold interprete_parent parents
     |> add_declaration full_name (declare_declinfo components')
  end;


(* prepare arguments *)

fun read_raw_parent ctxt raw_T =
  (case Proof_Context.read_typ_abbrev ctxt raw_T of
    Type (name, Ts) => (Ts, name)
  | T => error ("Bad parent statespace specification: " ^ Syntax.string_of_typ ctxt T));

fun read_typ ctxt raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val T = Syntax.read_typ ctxt' raw_T;
    val env' = Term.add_tfreesT T env;
  in (T, env') end;

fun cert_typ ctxt raw_T env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val T = Type.no_tvars (Sign.certify_typ thy raw_T)
      handle TYPE (msg, _, _) => error msg;
    val env' = Term.add_tfreesT T env;
  in (T, env') end;

fun gen_define_statespace prep_typ state_space args name parents comps thy =
  let (* - args distinct
         - only args may occur in comps and parent-instantiations
         - number of insts must match parent args
         - no duplicate renamings
         - renaming should occur in namespace
      *)
    val _ = writeln ("Defining statespace " ^ quote name ^ " ...");

    val ctxt = Proof_Context.init_global thy;

    fun add_parent (prefix, (Ts, pname, rs)) env =
      let
        val prefix' =
          (case prefix of
            ("", mandatory) => (pname, mandatory)
          | _ => prefix);

        val full_pname = Sign.full_bname thy pname;
        val {args,components,...} =
              (case get_statespace (Context.Theory thy) full_pname of
                SOME r => r
               | NONE => error ("Undefined statespace " ^ quote pname));


        val (Ts',env') = fold_map (prep_typ ctxt) Ts env
            handle ERROR msg => cat_error msg
                    ("The error(s) above occurred in parent statespace specification "
                    ^ quote pname);
        val err_insts = if length args <> length Ts' then
            ["number of type instantiation(s) does not match arguments of parent statespace "
              ^ quote pname]
            else [];

        val rnames = map fst rs
        val err_dup_renamings = (case duplicates (op =) rnames of
             [] => []
            | dups => ["Duplicate renaming(s) for " ^ commas dups])

        val cnames = map fst components;
        val err_rename_unknowns = (case subtract (op =) cnames rnames of
              [] => []
             | rs => ["Unknown components " ^ commas rs]);


        val rs' = map (AList.lookup (op =) rs o fst) components;
        val errs =err_insts @ err_dup_renamings @ err_rename_unknowns
      in
        if null errs then ((prefix', (Ts', full_pname, rs')), env')
        else error (cat_lines (errs @ ["in parent statespace " ^ quote pname]))
      end;

    val (parents',env) = fold_map add_parent parents [];

    val err_dup_args =
         (case duplicates (op =) args of
            [] => []
          | dups => ["Duplicate type argument(s) " ^ commas dups]);


    val err_dup_components =
         (case duplicates (op =) (map fst comps) of
           [] => []
          | dups => ["Duplicate state-space components " ^ commas dups]);

    fun prep_comp (n,T) env =
      let val (T', env') = prep_typ ctxt T env handle ERROR msg =>
       cat_error msg ("The error(s) above occurred in component " ^ quote n)
      in ((n,T'), env') end;

    val (comps',env') = fold_map prep_comp comps env;

    val err_extra_frees =
      (case subtract (op =) args (map fst env') of
        [] => []
      | extras => ["Extra free type variable(s) " ^ commas extras]);

    val defaultS = Sign.defaultS thy;
    val args' = map (fn x => (x, AList.lookup (op =) env x |> the_default defaultS)) args;


    fun fst_eq ((x:string,_),(y,_)) = x = y;
    fun snd_eq ((_,t:typ),(_,u)) = t = u;

    val raw_parent_comps = maps (parent_components thy o snd) parents';
    fun check_type (n,T) =
          (case distinct (snd_eq) (filter (curry fst_eq (n,T)) raw_parent_comps) of
             []  => []
           | [_] => []
           | rs  => ["Different types for component " ^ quote n ^ ": " ^
                commas (map (Syntax.string_of_typ ctxt o snd) rs)])

    val err_dup_types = maps check_type (duplicates fst_eq raw_parent_comps)

    val parent_comps = distinct (fst_eq) raw_parent_comps;
    val all_comps = parent_comps @ comps';
    val err_comp_in_parent = (case duplicates (op =) (map fst all_comps) of
               [] => []
             | xs => ["Components already defined in parents: " ^ commas_quote xs]);
    val errs = err_dup_args @ err_dup_components @ err_extra_frees @
               err_dup_types @ err_comp_in_parent;
  in if null errs
     then thy |> statespace_definition state_space args' name parents' parent_comps comps'
     else error (cat_lines errs)
  end
  handle ERROR msg => cat_error msg ("Failed to define statespace " ^ quote name);

val define_statespace = gen_define_statespace read_typ NONE;
val define_statespace_i = gen_define_statespace cert_typ;



(*** parse/print - translations ***)

local
fun map_get_comp f ctxt (Free (name,_)) =
      (case (get_comp ctxt name) of
        SOME (T,_) => f T T dummyT
      | NONE => (Syntax.free "arbitrary"(*; error "context not ready"*)))
  | map_get_comp _ _ _ = Syntax.free "arbitrary";

val get_comp_projection = map_get_comp project_free;
val get_comp_injection  = map_get_comp inject_free;

fun name_of (Free (n,_)) = n;
in

fun gen_lookup_tr ctxt s n =
  (case get_comp (Context.Proof ctxt) n of
    SOME (T, _) =>
      Syntax.const @{const_name StateFun.lookup} $
        Syntax.free (project_name T) $ Syntax.free n $ s
  | NONE =>
      if get_silent (Context.Proof ctxt)
      then Syntax.const @{const_name StateFun.lookup} $
        Syntax.const @{const_syntax undefined} $ Syntax.free n $ s
      else raise TERM ("StateSpace.gen_lookup_tr: component " ^ quote n ^ " not defined", []));

fun lookup_tr ctxt [s, x] =
  (case Term_Position.strip_positions x of
    Free (n,_) => gen_lookup_tr ctxt s n
  | _ => raise Match);

fun lookup_swap_tr ctxt [Free (n,_),s] = gen_lookup_tr ctxt s n;

fun lookup_tr' ctxt [_ $ Free (prj, _), n as (_ $ Free (name, _)), s] =
      (case get_comp (Context.Proof ctxt) name of
        SOME (T, _) =>
          if prj = project_name T
          then Syntax.const "_statespace_lookup" $ s $ n
          else raise Match
      | NONE => raise Match)
  | lookup_tr' _ ts = raise Match;

fun gen_update_tr id ctxt n v s =
  let
    fun pname T = if id then @{const_name Fun.id} else project_name T;
    fun iname T = if id then @{const_name Fun.id} else inject_name T;
  in
    (case get_comp (Context.Proof ctxt) n of
      SOME (T, _) =>
        Syntax.const @{const_name StateFun.update} $
          Syntax.free (pname T) $ Syntax.free (iname T) $
          Syntax.free n $ (Syntax.const @{const_name K_statefun} $ v) $ s
    | NONE =>
        if get_silent (Context.Proof ctxt) then
          Syntax.const @{const_name StateFun.update} $
            Syntax.const @{const_syntax undefined} $ Syntax.const @{const_syntax undefined} $
            Syntax.free n $ (Syntax.const @{const_name K_statefun} $ v) $ s
       else raise TERM ("StateSpace.gen_update_tr: component " ^ n ^ " not defined", []))
   end;

fun update_tr ctxt [s, x, v] =
  (case Term_Position.strip_positions x of
    Free (n, _) => gen_update_tr false ctxt n v s
  | _ => raise Match);

fun update_tr' ctxt
        [_ $ Free (prj, _), _ $ Free (inj, _), n as (_ $ Free (name, _)), (Const (k, _) $ v), s] =
      if Long_Name.base_name k = Long_Name.base_name @{const_name K_statefun} then
        (case get_comp (Context.Proof ctxt) name of
          SOME (T, _) =>
            if inj = inject_name T andalso prj = project_name T then
              Syntax.const "_statespace_update" $ s $ n $ v
            else raise Match
        | NONE => raise Match)
     else raise Match
  | update_tr' _ _ = raise Match;

end;


(*** outer syntax *)

local

val type_insts =
  Parse.typ >> single ||
  @{keyword "("} |-- Parse.!!! (Parse.list1 Parse.typ --| @{keyword ")"})

val comp = Parse.name -- (@{keyword "::"} |-- Parse.!!! Parse.typ);
fun plus1_unless test scan =
  scan ::: Scan.repeat (@{keyword "+"} |-- Scan.unless test (Parse.!!! scan));

val mapsto = @{keyword "="};
val rename = Parse.name -- (mapsto |-- Parse.name);
val renames = Scan.optional (@{keyword "["} |-- Parse.!!! (Parse.list1 rename --| @{keyword "]"})) [];

val parent =
  Parse_Spec.locale_prefix false --
  ((type_insts -- Parse.xname) || (Parse.xname >> pair [])) -- renames
    >> (fn ((prefix, (insts, name)), renames) => (prefix, (insts, name, renames)));

in

val statespace_decl =
  Parse.type_args -- Parse.name --
    (@{keyword "="} |--
      ((Scan.repeat1 comp >> pair []) ||
        (plus1_unless comp parent --
          Scan.optional (@{keyword "+"} |-- Parse.!!! (Scan.repeat1 comp)) [])));
val _ =
  Outer_Syntax.command @{command_spec "statespace"} "define state space"
    (statespace_decl >> (fn ((args, name), (parents, comps)) =>
      Toplevel.theory (define_statespace args name parents comps)));

end;

end;
