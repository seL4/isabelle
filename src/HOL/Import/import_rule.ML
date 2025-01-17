(*  Title:      HOL/Import/import_rule.ML
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Importer proof rules and processing of lines and files.

Based on earlier code by Steven Obua and Sebastian Skalberg.
*)

signature IMPORT_RULE =
sig
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
  val def : string -> cterm -> theory -> thm * theory
  val mtydef : theory -> string -> thm
  val tydef :
    string -> string -> string -> cterm -> cterm -> thm -> theory -> thm * theory
  val inst_type : (ctyp * ctyp) list -> thm -> thm
  val inst : (cterm * cterm) list -> thm -> thm
  val import_file : Path.T -> theory -> theory
end

structure Import_Rule: IMPORT_RULE =
struct

fun implies_elim_all th = implies_elim_list th (map Thm.assume (cprems_of th))

fun meta_mp th1 th2 =
  let
    val th1a = implies_elim_all th1
    val th1b = Thm.implies_intr (strip_imp_concl (Thm.cprop_of th2)) th1a
    val th2a = implies_elim_all th2
    val th3 = Thm.implies_elim th1b th2a
  in
    implies_intr_hyps th3
  end

fun meta_eq_to_obj_eq th =
  let
    val (tml, tmr) = Thm.dest_binop (strip_imp_concl (Thm.cprop_of th))
    val cty = Thm.ctyp_of_cterm tml
    val i = Thm.instantiate' [SOME cty] [SOME tml, SOME tmr]
      @{thm meta_eq_to_obj_eq}
  in
    Thm.implies_elim i th
  end

fun beta ct = meta_eq_to_obj_eq (Thm.beta_conversion false ct)

fun eq_mp th1 th2 =
  let
    val (tm1l, tm1r) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (Thm.cprop_of th1)))
    val i1 = Thm.instantiate' [] [SOME tm1l, SOME tm1r] @{thm iffD1}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun comb th1 th2 =
  let
    val t1c = Thm.dest_arg (strip_imp_concl (Thm.cprop_of th1))
    val t2c = Thm.dest_arg (strip_imp_concl (Thm.cprop_of th2))
    val (cf, cg) = Thm.dest_binop t1c
    val (cx, cy) = Thm.dest_binop t2c
    val [fd, fr] = Thm.dest_ctyp (Thm.ctyp_of_cterm cf)
    val i1 = Thm.instantiate' [SOME fd, SOME fr]
      [SOME cf, SOME cg, SOME cx, SOME cy] @{thm cong}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun trans th1 th2 =
  let
    val t1c = Thm.dest_arg (strip_imp_concl (Thm.cprop_of th1))
    val t2c = Thm.dest_arg (strip_imp_concl (Thm.cprop_of th2))
    val (r, s) = Thm.dest_binop t1c
    val (_, t) = Thm.dest_binop t2c
    val ty = Thm.ctyp_of_cterm r
    val i1 = Thm.instantiate' [SOME ty] [SOME r, SOME s, SOME t] @{thm trans}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun deduct th1 th2 =
  let
    val th1c = strip_imp_concl (Thm.cprop_of th1)
    val th2c = strip_imp_concl (Thm.cprop_of th2)
    val th1a = implies_elim_all th1
    val th2a = implies_elim_all th2
    val th1b = Thm.implies_intr th2c th1a
    val th2b = Thm.implies_intr th1c th2a
    val i = Thm.instantiate' []
      [SOME (Thm.dest_arg th1c), SOME (Thm.dest_arg th2c)] @{thm iffI}
    val i1 = Thm.implies_elim i (Thm.assume (Thm.cprop_of th2b))
    val i2 = Thm.implies_elim i1 th1b
    val i3 = Thm.implies_intr (Thm.cprop_of th2b) i2
    val i4 = Thm.implies_elim i3 th2b
  in
    implies_intr_hyps i4
  end

fun conj1 th =
  let
    val (tml, tmr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (Thm.cprop_of th)))
    val i = Thm.instantiate' [] [SOME tml, SOME tmr] @{thm conjunct1}
  in
    meta_mp i th
  end

fun conj2 th =
  let
    val (tml, tmr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (Thm.cprop_of th)))
    val i = Thm.instantiate' [] [SOME tml, SOME tmr] @{thm conjunct2}
  in
    meta_mp i th
  end

fun refl ctm =
  let
    val cty = Thm.ctyp_of_cterm ctm
  in
    Thm.instantiate' [SOME cty] [SOME ctm] @{thm refl}
  end

fun abs cv th =
  let
    val th1 = implies_elim_all th
    val (tl, tr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (Thm.cprop_of th1)))
    val (ll, lr) = (Thm.lambda cv tl, Thm.lambda cv tr)
    val (al, ar) = (Thm.apply ll cv, Thm.apply lr cv)
    val bl = beta al
    val br = meta_eq_to_obj_eq (Thm.symmetric (Thm.beta_conversion false ar))
    val th2 = trans (trans bl th1) br
    val th3 = implies_elim_all th2
    val th4 = Thm.forall_intr cv th3
    val i = Thm.instantiate' [SOME (Thm.ctyp_of_cterm cv), SOME (Thm.ctyp_of_cterm tl)]
      [SOME ll, SOME lr] @{lemma "(\<And>x. f x = g x) \<Longrightarrow> f = g" by (rule ext)}
  in
    meta_mp i th4
  end

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

fun def' c rhs thy =
  let
    val b = Binding.name c
    val ty = type_of rhs
    val thy1 = Sign.add_consts [(b, ty, NoSyn)] thy
    val eq = Logic.mk_equals (Const (Sign.full_name thy1 b, ty), rhs)
    val (th, thy2) = Global_Theory.add_def (Binding.suffix_name "_hldef" b, eq) thy1
    val def_thm = freezeT thy1 th
  in
    (meta_eq_to_obj_eq def_thm, thy2)
  end

fun mdef thy name =
  case Import_Data.get_const_def thy name of
    SOME th => th
  | NONE => error ("constant mapped but no definition: " ^ name)

fun def c rhs thy =
  case Import_Data.get_const_def thy c of
    SOME _ =>
      let
        val () = warning ("Const mapped but def provided: " ^ c)
      in
        (mdef thy c, thy)
      end
  | NONE => def' c (Thm.term_of rhs) thy

fun typedef_hol2hollight nty oty rep abs pred a r =
  Thm.instantiate' [SOME nty, SOME oty] [SOME rep, SOME abs, SOME pred, SOME a, SOME r]
    @{lemma "type_definition Rep Abs (Collect P) \<Longrightarrow> Abs (Rep a) = a \<and> P r = (Rep (Abs r) = r)"
        by (metis type_definition.Rep_inverse type_definition.Abs_inverse
              type_definition.Rep mem_Collect_eq)}

fun typedef_hollight thy th =
  let
    val (th_s, cn) = Thm.dest_comb (Thm.dest_arg (Thm.cprop_of th))
    val (th_s, abst) = Thm.dest_comb th_s
    val rept = Thm.dest_arg th_s
    val P = Thm.dest_arg cn
    val [nty, oty] = Thm.dest_ctyp (Thm.ctyp_of_cterm rept)
  in
    typedef_hol2hollight nty oty rept abst P (Thm.free ("a", nty)) (Thm.free ("r", oty))
  end

fun tydef' tycname abs_name rep_name cP ct td_th thy =
  let
    val ctT = Thm.ctyp_of_cterm ct
    val nonempty = Thm.instantiate' [SOME ctT] [SOME cP, SOME ct]
      @{lemma "P t \<Longrightarrow> \<exists>x. x \<in> Collect P" by auto}
    val th2 = meta_mp nonempty td_th
    val c =
      case Thm.concl_of th2 of
        \<^Const_>\<open>Trueprop for \<^Const_>\<open>Ex _ for \<open>Abs (_, _, \<^Const_>\<open>Set.member _ for _ c\<close>)\<close>\<close>\<close> => c
      | _ => error "type_introduction: bad type definition theorem"
    val tfrees = Term.add_tfrees c []
    val tnames = sort_strings (map fst tfrees)
    val typedef_bindings =
     {Rep_name = Binding.name rep_name,
      Abs_name = Binding.name abs_name,
      type_definition_name = Binding.name ("type_definition_" ^ tycname)}
    val ((_, typedef_info), thy') =
     Named_Target.theory_map_result (apsnd o Typedef.transform_info)
     (Typedef.add_typedef {overloaded = false}
       (Binding.name tycname, map (rpair dummyS) tnames, NoSyn) c
       (SOME typedef_bindings) (fn ctxt => resolve_tac ctxt [th2] 1)) thy
    val aty = Thm.global_ctyp_of thy' (#abs_type (#1 typedef_info))
    val th = freezeT thy' (#type_definition (#2 typedef_info))
    val (th_s, _) = Thm.dest_comb (Thm.dest_arg (Thm.cprop_of th))
    val (th_s, abst) = Thm.dest_comb th_s
    val rept = Thm.dest_arg th_s
    val [nty, oty] = Thm.dest_ctyp (Thm.ctyp_of_cterm rept)
    val typedef_th =
      typedef_hol2hollight nty oty rept abst cP (Thm.free ("a", aty)) (Thm.free ("r", ctT))
  in
    (typedef_th OF [#type_definition (#2 typedef_info)], thy')
  end

fun mtydef thy name =
  case Import_Data.get_typ_def thy name of
    SOME thn => meta_mp (typedef_hollight thy thn) thn
  | NONE => error ("type mapped but no tydef thm registered: " ^ name)

fun tydef tycname abs_name rep_name P t td_th thy =
  case Import_Data.get_typ_def thy tycname of
    SOME _ =>
      let
        val () = warning ("Type mapped but proofs provided: " ^ tycname)
      in
        (mtydef thy tycname, thy)
      end
  | NONE => tydef' tycname abs_name rep_name P t td_th thy

fun inst_type lambda =
  let
    val tyinst =
      TFrees.build (lambda |> fold (fn (a, b) =>
        TFrees.add (Term.dest_TFree (Thm.typ_of a), b)))
  in
    Thm.instantiate_frees (tyinst, Frees.empty)
  end

fun inst sigma th =
  let
    val (dom, rng) = ListPair.unzip (rev sigma)
  in
    th |> forall_intr_list dom
       |> forall_elim_list rng
  end

val make_name = String.translate (fn #"." => "dot" | c => Char.toString c)

fun make_free (x, ty) = Free (make_name x, ty)

fun make_tfree a =
  let val b = "'" ^ String.translate (fn #"?" => "t" | c => Char.toString c) a
  in TFree (b, \<^sort>\<open>type\<close>) end

fun make_type thy (c, args) =
  let
    val d =
      (case Import_Data.get_typ_map thy c of
        SOME d => d
      | NONE => Sign.full_bname thy (make_name c))
  in Type (d, args) end

fun make_const thy (c, ty) =
  let
    val d =
      (case Import_Data.get_const_map thy c of
        SOME d => d
      | NONE => Sign.full_bname thy (make_name c))
  in Const (d, ty) end


datatype state =
  State of theory * (ctyp Inttab.table * int) * (cterm Inttab.table * int) * (thm Inttab.table * int)

fun init_state thy = State (thy, (Inttab.empty, 0), (Inttab.empty, 0), (Inttab.empty, 0))

fun get (tab, no) s =
  (case Int.fromString s of
    NONE => error "Import_Rule.get: not a number"
  | SOME i =>
      (case Inttab.lookup tab (Int.abs i) of
        NONE => error "Import_Rule.get: lookup failed"
      | SOME res => (res, (if i < 0 then Inttab.delete (Int.abs i) tab else tab, no))))

fun get_theory (State (thy, _, _, _)) = thy;
fun map_theory f (State (thy, a, b, c)) = State (f thy, a, b, c);
fun map_theory_result f (State (thy, a, b, c)) =
  let val (res, thy') = f thy in (res, State (thy', a, b, c)) end;

fun ctyp_of (State (thy, _, _, _)) = Thm.global_ctyp_of thy;
fun cterm_of (State (thy, _, _, _)) = Thm.global_cterm_of thy;

fun typ i (State (thy, a, b, c)) = let val (i, a') = get a i in (i, State (thy, a', b, c)) end
fun term i (State (thy, a, b, c)) = let val (i, b') = get b i in (i, State (thy, a, b', c)) end
fun thm i (State (thy, a, b, c)) = let val (i, c') = get c i in (i, State (thy, a, b, c')) end

fun set (tab, no) v = (Inttab.update_new (no + 1, v) tab, no + 1)
fun set_typ ty (State (thy, a, b, c)) = State (thy, set a ty, b, c)
fun set_term tm (State (thy, a, b, c)) = State (thy, a, set b tm, c)
fun set_thm th (State (thy, a, b, c)) = State (thy, a, b, set c th)

fun last_thm (State (_, _, _, (tab, no))) =
  case Inttab.lookup tab no of
    NONE => error "Import_Rule.last_thm: lookup failed"
  | SOME th => th

fun list_last (x :: y :: zs) = apfst (fn t => x :: y :: t) (list_last zs)
  | list_last [x] = ([], x)
  | list_last [] = error "list_last: empty"

fun pair_list (x :: y :: zs) = ((x, y) :: pair_list zs)
  | pair_list [] = []
  | pair_list _ = error "pair_list: odd list length"

fun store_thm binding th0 thy =
  let
    val ctxt = Proof_Context.init_global thy
    val th = Drule.export_without_context_open th0
    val tvs = Term.add_tvars (Thm.prop_of th) []
    val tns = map (fn (_, _) => "'") tvs
    val nms = Name.variants (Variable.names_of ctxt) tns
    val vs = map TVar ((nms ~~ (map (snd o fst) tvs)) ~~ (map snd tvs))
    val th' = Thm.instantiate (TVars.make (tvs ~~ map (Thm.ctyp_of ctxt) vs), Vars.empty) th
  in
    snd (Global_Theory.add_thm ((binding, th'), []) thy)
  end

fun parse_line s =
  (case String.tokens (fn x => x = #"\n" orelse x = #" ") s of
    [] => error "parse_line: empty"
  | cmd :: args =>
      (case String.explode cmd of
        [] => error "parse_line: empty command"
      | c :: cs => (c, String.implode cs :: args)))

fun process_line str =
  let
    fun process (#"R", [t]) = term t #>> refl #-> set_thm
      | process (#"B", [t]) = term t #>> beta #-> set_thm
      | process (#"1", [th]) = thm th #>> conj1 #-> set_thm
      | process (#"2", [th]) = thm th #>> conj2 #-> set_thm
      | process (#"H", [t]) = term t #>> Thm.apply \<^cterm>\<open>Trueprop\<close> #>> Thm.trivial #-> set_thm
      | process (#"A", [_, t]) =
          term t #>> Thm.apply \<^cterm>\<open>Trueprop\<close> #>> Skip_Proof.make_thm_cterm #-> set_thm
      | process (#"C", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry comb #-> set_thm
      | process (#"T", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry trans #-> set_thm
      | process (#"E", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry eq_mp #-> set_thm
      | process (#"D", [th1, th2]) = thm th1 ##>> thm th2 #>> uncurry deduct #-> set_thm
      | process (#"L", [t, th]) = term t ##>> (fn ti => thm th ti) #>> uncurry abs #-> set_thm
      | process (#"M", [s]) = (fn state =>
          let
            val thy = get_theory state
            val ctxt = Proof_Context.init_global thy
            val th = freezeT thy (Global_Theory.get_thm thy s)
            val ((_, [th']), _) = Variable.import true [th] ctxt
          in
            set_thm th' state
          end)
      | process (#"Q", l) = (fn state =>
          let
            val (tys, th) = list_last l
            val (th, state1) = thm th state
            val (tys, state2) = fold_map typ tys state1
          in
            set_thm (inst_type (pair_list tys) th) state2
          end)
      | process (#"S", l) = (fn state =>
          let
            val (tms, th) = list_last l
            val (th, state1) = thm th state
            val (tms, state2) = fold_map term tms state1
          in
            set_thm (inst (pair_list tms) th) state2
          end)
      | process (#"F", [name, t]) = (fn state =>
          let
            val (tm, state1) = term t state
            val (th, state2) = map_theory_result (def (make_name name) tm) state1
          in
            set_thm th state2
          end)
      | process (#"F", [name]) = (fn state => set_thm (mdef (get_theory state) name) state)
      | process (#"Y", [name, absname, repname, t1, t2, th]) = (fn state =>
          let
            val (th, state1) = thm th state
            val (t1, state2) = term t1 state1
            val (t2, state3) = term t2 state2
            val (th, state4) = map_theory_result (tydef name absname repname t1 t2 th) state3
          in
            set_thm th state4
          end)
      | process (#"Y", [name, _, _]) = (fn state => set_thm (mtydef (get_theory state) name) state)
      | process (#"t", [n]) = (fn state => set_typ (ctyp_of state (make_tfree n)) state)
      | process (#"a", n :: l) = (fn state =>
          fold_map typ l state
          |>> (fn tys => ctyp_of state (make_type (get_theory state) (n, map Thm.typ_of tys)))
          |-> set_typ)
      | process (#"v", [n, ty]) = (fn state =>
          typ ty state |>> (fn ty => cterm_of state (make_free (n, Thm.typ_of ty))) |-> set_term)
      | process (#"c", [n, ty]) = (fn state =>
          typ ty state |>> (fn ty =>
            cterm_of state (make_const (get_theory state) (n, Thm.typ_of ty))) |-> set_term)
      | process (#"f", [t1, t2]) = term t1 ##>> term t2 #>> uncurry Thm.apply #-> set_term
      | process (#"l", [t1, t2]) = term t1 ##>> term t2 #>> uncurry Thm.lambda #-> set_term
      | process (#"+", [s]) = (fn state =>
          map_theory (store_thm (Binding.name (make_name s)) (last_thm state)) state)
      | process (c, _) = error ("process: unknown command: " ^ String.implode [c])
  in
    process (parse_line str)
  end

fun import_file path0 thy =
  let
    val path = File.absolute_path (Resources.master_directory thy + path0)
    val lines =
      if Path.is_zst path then Bytes.read path |> Zstd.uncompress |> Bytes.trim_split_lines
      else File.read_lines path
  in get_theory (fold process_line lines (init_state thy)) end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>import_file\<close> "import recorded proofs from HOL Light"
    (Parse.path >> (fn name => Toplevel.theory (fn thy => import_file (Path.explode name) thy)))

end
