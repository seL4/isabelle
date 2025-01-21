(*  Title:      HOL/Import/import_rule.ML
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH
    Author:     Makarius

Importer proof rules and processing of lines and files.

Based on earlier code by Steven Obua and Sebastian Skalberg.
*)

signature IMPORT_RULE =
sig
  val trace : bool Config.T
  type name = {hol: string, isabelle: string}
  val beta : cterm -> thm
  val eq_mp : thm -> thm -> thm
  val comb : thm -> thm -> thm
  val trans : thm -> thm -> thm
  val deduct : thm -> thm -> thm
  val conj1 : thm -> thm
  val conj2 : thm -> thm
  val refl : cterm -> thm
  val abs : cterm -> thm -> thm
  val mdef : theory -> string -> thm
  val def : name -> cterm -> theory -> thm * theory
  val mtydef : theory -> string -> thm
  val tydef : name -> string -> string -> cterm -> cterm -> thm -> theory -> thm * theory
  val inst_type : (ctyp * ctyp) list -> thm -> thm
  val inst : (cterm * cterm) list -> thm -> thm
  val import_file : Path.T -> theory -> theory
end

structure Import_Rule: IMPORT_RULE =
struct

(* tracing *)

val trace = Attrib.setup_config_bool \<^binding>\<open>import_trace\<close> (K false)

type name = {hol: string, isabelle: string}

fun print_name {hol, isabelle} =
  if hol = isabelle then quote hol
  else quote hol ^ " = " ^ quote isabelle

fun print_item kind name =
  Markup.markup Markup.keyword1 kind ^ " " ^ print_name name

fun tracing_item thy kind name =
  if Config.get_global thy trace then tracing (print_item kind name) else ()



(** primitive rules of HOL Light **)

(* basic logic *)

fun to_obj_eq th =
  let
    val (t, u) = Thm.dest_equals (Thm.cprop_of th)
    val A = Thm.ctyp_of_cterm t
    val rl = Thm.instantiate' [SOME A] [SOME t, SOME u] @{thm meta_eq_to_obj_eq}
  in
    Thm.implies_elim rl th
  end

fun to_meta_eq th =
  let
    val (t, u) = Thm.dest_binop (HOLogic.dest_judgment (Thm.cprop_of th))
    val A = Thm.ctyp_of_cterm t
    val rl = Thm.instantiate' [SOME A] [SOME t, SOME u] @{thm eq_reflection}
  in
    Thm.implies_elim rl th
  end

fun beta t = Thm.beta_conversion false t |> to_obj_eq

fun eq_mp th1 th2 =
  let
    val (Q, P) = Thm.dest_binop (HOLogic.dest_judgment (Thm.cprop_of th1))
    val rl = Thm.instantiate' [] [SOME Q, SOME P] @{thm iffD1}
  in
    Thm.implies_elim (Thm.implies_elim rl th1) th2
  end

fun comb th1 th2 =
  Thm.combination (to_meta_eq th1) (to_meta_eq th2) |> to_obj_eq

fun trans th1 th2 =
  Thm.transitive (to_meta_eq th1) (to_meta_eq th2) |> to_obj_eq

fun deduct th1 th2 =
  let
    val Q = Thm.cprop_of th1
    val P = Thm.cprop_of th2
    val th1' = Thm.implies_intr P th1
    val th2' = Thm.implies_intr Q th2
    val rl =
      Thm.instantiate' [] [SOME (HOLogic.dest_judgment Q), SOME (HOLogic.dest_judgment P)]
        @{thm iffI}
  in
    Thm.implies_elim (Thm.implies_elim rl th2') th1'
  end

fun conj1 th =
  let
    val (P, Q) = Thm.dest_binop (HOLogic.dest_judgment (Thm.cprop_of th))
    val rl = Thm.instantiate' [] [SOME P, SOME Q] @{thm conjunct1}
  in
    Thm.implies_elim rl th
  end

fun conj2 th =
  let
    val (P, Q) = Thm.dest_binop (HOLogic.dest_judgment (Thm.cprop_of th))
    val rl = Thm.instantiate' [] [SOME P, SOME Q] @{thm conjunct2}
  in
    Thm.implies_elim rl th
  end

fun refl t =
  let val A = Thm.ctyp_of_cterm t
  in Thm.instantiate' [SOME A] [SOME t] @{thm refl} end

fun abs x th =
  to_meta_eq th |> Thm.abstract_rule (Term.term_name (Thm.term_of x)) x |> to_obj_eq



(* instantiation *)

fun freezeT thy th =
  let
    fun add (v as ((a, _), S)) tvars =
      if TVars.defined tvars v then tvars
      else TVars.add (v, Thm.global_ctyp_of thy (TFree (a, S))) tvars
    val tyinst =
      TVars.build (Thm.prop_of th |> (fold_types o fold_atyps) (fn TVar v => add v | _ => I))
  in
    Thm.instantiate (tyinst, Vars.empty) th
  end

fun freeze' th =
  let
    val vars = Vars.build (th |> Thm.add_vars)
    val inst = vars |> Vars.map (fn _ => fn v =>
      let
        val Var ((x, _), _) = Thm.term_of v
        val ty = Thm.ctyp_of_cterm v
      in Thm.free (x, ty) end)
  in
    Thm.instantiate (TVars.empty, inst) th
  end

fun freeze thy = freezeT thy #> freeze';

fun inst_type theta =
  let
    val tyinst =
      TFrees.build (theta |> fold (fn (a, b) =>
        TFrees.add (Term.dest_TFree (Thm.typ_of a), b)))
  in
    Thm.instantiate_frees (tyinst, Frees.empty)
  end

fun inst theta th =
  let
    val inst =
      Frees.build (theta |> fold (fn (a, b) =>
        Frees.add (Term.dest_Free (Thm.term_of a), b)))
  in
    Thm.instantiate_frees (TFrees.empty, inst) th
    |> freeze'
  end


(* constant definitions *)

fun def' (name as {isabelle = c, ...}) rhs thy =
  let
    val _ = tracing_item thy "const" name;
    val b = Binding.name c
    val ty = type_of rhs
    val thy1 = Sign.add_consts [(b, ty, NoSyn)] thy
    val eq = Logic.mk_equals (Const (Sign.full_name thy1 b, ty), rhs)
    val (th, thy2) = Global_Theory.add_def (Binding.suffix_name "_hldef" b, eq) thy1
    val def_thm = freezeT thy1 th |> to_obj_eq
  in
    (def_thm, thy2)
  end

fun mdef thy name =
  (case Import_Data.get_const_def thy name of
    SOME th => th
  | NONE => error ("Constant mapped, but no definition: " ^ quote name))

fun def (name as {isabelle = c, ...}) rhs thy =
  if is_some (Import_Data.get_const_def thy c) then
    (warning ("Const mapped, but def provided: " ^ quote c); (freeze thy (mdef thy c), thy))
  else def' name (Thm.term_of rhs) thy


(* type definitions *)

fun typedef_hol2hollight A B rep abs pred a r =
  Thm.instantiate' [SOME A, SOME B] [SOME rep, SOME abs, SOME pred, SOME a, SOME r]
    @{lemma "type_definition Rep Abs (Collect P) \<Longrightarrow> Abs (Rep a) = a \<and> P r = (Rep (Abs r) = r)"
        by (metis type_definition.Rep_inverse type_definition.Abs_inverse
              type_definition.Rep mem_Collect_eq)}

fun typedef_hollight th =
  let
    val ((rep, abs), P) =
      Thm.dest_comb (HOLogic.dest_judgment (Thm.cprop_of th))
      |>> (Thm.dest_comb #>> Thm.dest_arg)
      ||> Thm.dest_arg
    val [A, B] = Thm.dest_ctyp (Thm.ctyp_of_cterm rep)
  in
    typedef_hol2hollight A B rep abs P (Thm.free ("a", A)) (Thm.free ("r", B))
  end

fun tydef' (name as {isabelle = tycname, ...}) abs_name rep_name P t witness thy =
  let
    val _ = tracing_item thy "type" name;

    val T = Thm.ctyp_of_cterm t
    val nonempty =
      Thm.instantiate' [SOME T] [SOME P, SOME t]
        @{lemma "P t \<Longrightarrow> \<exists>x. x \<in> Collect P" by auto}
      |> Thm.elim_implies witness
    val \<^Const_>\<open>Trueprop for \<^Const_>\<open>Ex _ for \<open>Abs (_, _, \<^Const_>\<open>Set.member _ for _ set\<close>)\<close>\<close>\<close> =
      Thm.concl_of nonempty

    val tfrees = Term.add_tfrees set []
    val tnames = sort_strings (map fst tfrees)
    val typedef_bindings =
     {Rep_name = Binding.name rep_name,
      Abs_name = Binding.name abs_name,
      type_definition_name = Binding.name ("type_definition_" ^ tycname)}
    val ((_, typedef_info), thy') =
     Typedef.add_typedef_global {overloaded = false}
       (Binding.name tycname, map (rpair dummyS) tnames, NoSyn) set
       (SOME typedef_bindings) (fn ctxt => resolve_tac ctxt [nonempty] 1) thy
    val aty = Thm.global_ctyp_of thy' (#abs_type (#1 typedef_info))
    val th = freezeT thy' (#type_definition (#2 typedef_info))
    val (rep, abs) = Thm.dest_binop (Thm.dest_fun (HOLogic.dest_judgment (Thm.cprop_of th)))
    val [A, B] = Thm.dest_ctyp (Thm.ctyp_of_cterm rep)
    val typedef_th = typedef_hol2hollight A B rep abs P (Thm.free ("a", aty)) (Thm.free ("r", T))
  in
    (typedef_th OF [#type_definition (#2 typedef_info)], thy')
  end

fun mtydef thy name =
  (case Import_Data.get_typ_def thy name of
    SOME th => Thm.implies_elim (typedef_hollight th) th
  | NONE => error ("Type mapped, but no tydef thm registered: " ^ quote name))

fun tydef (name as {hol = tycname, ...}) abs_name rep_name P t td_th thy =
  if is_some (Import_Data.get_typ_def thy tycname) then
    (warning ("Type mapped but proofs provided: " ^ quote tycname); (mtydef thy tycname, thy))
  else tydef' name abs_name rep_name P t td_th thy



(** importer **)

(* basic entities *)

fun make_name hol =
  {hol = hol, isabelle = String.translate (fn #"." => "dot" | c => Char.toString c) hol}

fun make_bound a =
  (case try (unprefix "_") a of
    SOME b => if forall_string Symbol.is_ascii_digit b then "u" else b
  | NONE => a);

fun make_free x ty = Thm.free (#isabelle (make_name x), ty);

fun make_tfree thy a =
  let val b = "'" ^ String.translate (fn #"?" => "t" | c => Char.toString c) a
  in Thm.global_ctyp_of thy (TFree (b, \<^sort>\<open>type\<close>)) end

fun make_type thy c args =
  let
    val d =
      (case Import_Data.get_typ_map thy c of
        SOME d => d
      | NONE => Sign.full_bname thy (#isabelle (make_name c)))
    val T = Thm.global_ctyp_of thy (Type (d, replicate (length args) dummyT))
  in Thm.make_ctyp T args end

fun make_const thy c ty =
  let
    val d =
      (case Import_Data.get_const_map thy c of
        SOME d => d
      | NONE => Sign.full_bname thy (#isabelle (make_name c)))
  in Thm.global_cterm_of thy (Const (d, Thm.typ_of ty)) end

val make_thm = Skip_Proof.make_thm_cterm o HOLogic.mk_judgment
val assume_thm = Thm.assume_cterm o HOLogic.mk_judgment


(* import file *)

local

datatype state =
  State of theory * (ctyp Inttab.table * int) * (cterm Inttab.table * int) * (thm Inttab.table * int)

fun init_state thy = State (thy, (Inttab.empty, 0), (Inttab.empty, 0), (Inttab.empty, 0))

fun get (tab, reg) s =
  (case Int.fromString s of
    NONE => raise Fail "get: not a number"
  | SOME i =>
      (case Inttab.lookup tab (Int.abs i) of
        NONE => raise Fail "get: lookup failed"
      | SOME res => (res, (if i < 0 then Inttab.delete (Int.abs i) tab else tab, reg))))

fun get_theory (State (thy, _, _, _)) = thy;
val theory = `get_theory;
fun theory_op f (State (thy, a, b, c)) = let val (y, thy') = f thy in (y, State (thy', a, b, c)) end;

fun typ i (State (thy, a, b, c)) = let val (i, a') = get a i in (i, State (thy, a', b, c)) end
fun term i (State (thy, a, b, c)) = let val (i, b') = get b i in (i, State (thy, a, b', c)) end
fun thm i (State (thy, a, b, c)) = let val (i, c') = get c i in (i, State (thy, a, b, c')) end

val typs = fold_map typ
val terms = fold_map term

fun set (tab, reg) res = (Inttab.update_new (reg + 1, res) tab, reg + 1)
fun set_typ ty (State (thy, a, b, c)) = State (thy, set a ty, b, c)
fun set_term tm (State (thy, a, b, c)) = State (thy, a, set b tm, c)
fun set_thm th (State (thy, a, b, c)) = State (thy, a, b, set c th)

fun stored_thm name (State (thy, a, b, c)) =
  let val th = freeze thy (Global_Theory.get_thm thy name)
  in State (thy, a, b, set c th) end

fun store_thm name (State (thy, a, b, c as (tab, reg))) =
  let
    val _ = tracing_item thy "thm" name;

    val th =
      (case Inttab.lookup tab reg of
        NONE => raise Fail "store_thm: lookup failed"
      | SOME th0 => Drule.export_without_context_open th0)

    val tvars = TVars.build (Thm.fold_terms {hyps = false} TVars.add_tvars th);
    val names = Name.invent_global_types (TVars.size tvars)
    val tyinst =
      TVars.build (fold2
        (fn v as ((_, i), S) => fn b => TVars.add (v, Thm.global_ctyp_of thy (TVar ((b, i), S))))
        (TVars.list_set tvars) names)

    val th' = Thm.instantiate (tyinst, Vars.empty) th
    val thy' = #2 (Global_Theory.add_thm ((Binding.name (#isabelle name), th'), []) thy)
  in State (thy', a, b, c) end

fun pair_list (x :: y :: zs) = ((x, y) :: pair_list zs)
  | pair_list [] = []
  | pair_list _ = raise Fail "pair_list: odd list length"

fun parse_line s =
  (case String.tokens (fn x => x = #"\n" orelse x = #" ") s of
    [] => raise Fail "parse_line: empty"
  | cmd :: args =>
      (case String.explode cmd of
        [] => raise Fail "parse_line: empty command"
      | c :: cs => (c, String.implode cs :: args)))

fun command (#"R", [t]) = term t #>> refl #-> set_thm
  | command (#"B", [t]) = term t #>> beta #-> set_thm
  | command (#"1", [th]) = thm th #>> conj1 #-> set_thm
  | command (#"2", [th]) = thm th #>> conj2 #-> set_thm
  | command (#"H", [t]) = term t #>> assume_thm #-> set_thm
  | command (#"A", [_, t]) = term t #>> make_thm #-> set_thm
  | command (#"C", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry comb #-> set_thm
  | command (#"T", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry trans #-> set_thm
  | command (#"E", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry eq_mp #-> set_thm
  | command (#"D", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry deduct #-> set_thm
  | command (#"L", [t, th]) = term t ##>> thm th #>> uncurry abs #-> set_thm
  | command (#"M", [name]) = stored_thm name
  | command (#"Q", args) =
      split_last args |> (fn (tys, th) => thm th #-> (fn th => typs tys #-> (fn tys =>
        set_thm (inst_type (pair_list tys) th))))
  | command (#"S", args) =
      split_last args |> (fn (ts, th) => thm th #-> (fn th => terms ts #-> (fn ts =>
        set_thm (inst (pair_list ts) th))))
  | command (#"F", [name, t]) =
      term t #-> (fn t => theory_op (def (make_name name) t) #-> set_thm)
  | command (#"F", [name]) = theory #-> (fn thy => set_thm (mdef thy name))
  | command (#"Y", [name, abs, rep, t1, t2, th]) =
      thm th #-> (fn th => term t1 #-> (fn t1 => term t2 #-> (fn t2 =>
        theory_op (tydef (make_name name) abs rep t1 t2 th) #-> set_thm)))
  | command (#"Y", [name, _, _]) = theory #-> (fn thy => set_thm (mtydef thy name))
  | command (#"t", [a]) = theory #-> (fn thy => set_typ (make_tfree thy a))
  | command (#"a", c :: tys) = theory #-> (fn thy => typs tys #>> make_type thy c #-> set_typ)
  | command (#"v", [x, ty]) = typ ty #>> make_free x #-> set_term
  | command (#"c", [c, ty]) = theory #-> (fn thy => typ ty #>> make_const thy c #-> set_term)
  | command (#"f", [t, u]) = term t #-> (fn t => term u #-> (fn u => set_term (Thm.apply t u)))
  | command (#"l", [x, t]) =
      term x #-> (fn x => term t #-> (fn t =>
        set_term (Thm.lambda_name (make_bound (#1 (dest_Free (Thm.term_of x))), x) t)))
  | command (#"+", [name]) = store_thm (make_name name)
  | command (c, _) = raise Fail ("process: unknown command: " ^ String.str c)

in

fun import_file path0 thy =
  let
    val path = File.absolute_path (Resources.master_directory thy + path0)
    val lines =
      if Path.is_zst path then Bytes.read path |> Zstd.uncompress |> Bytes.trim_split_lines
      else File.read_lines path
  in init_state thy |> fold (parse_line #> command) lines |> get_theory end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>import_file\<close> "import recorded proofs from HOL Light"
    (Parse.path >> (fn name => Toplevel.theory (fn thy => import_file (Path.explode name) thy)))

end

end
