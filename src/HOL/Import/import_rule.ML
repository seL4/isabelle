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
  val inst_type : theory -> (ctyp * ctyp) list -> thm -> thm
  val inst : (cterm * cterm) list -> thm -> thm
  val import_file : Path.T -> theory -> theory
end

structure Import_Rule: IMPORT_RULE =
struct

type state = (ctyp Inttab.table * int) * (cterm Inttab.table * int) * (thm Inttab.table * int)

val init_state: state = ((Inttab.empty, 0), (Inttab.empty, 0), (Inttab.empty, 0))

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

fun freezeT thy thm =
  let
    val tvars = Term.add_tvars (Thm.prop_of thm) []
    val tfrees = map (fn ((t, _), s) => TFree (t, s)) tvars
  in
    Thm.instantiate (TVars.make (tvars ~~ map (Thm.global_ctyp_of thy) tfrees), Vars.empty) thm
  end

fun def' c rhs thy =
  let
    val b = Binding.name c
    val typ = type_of rhs
    val thy1 = Sign.add_consts [(b, typ, NoSyn)] thy
    val eq = Logic.mk_equals (Const (Sign.full_name thy1 b, typ), rhs)
    val (thm, thy2) = Global_Theory.add_def (Binding.suffix_name "_hldef" b, eq) thy1
    val def_thm = freezeT thy1 thm
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
    typedef_hol2hollight nty oty rept abst P
      (Thm.global_cterm_of thy (Free ("a", Thm.typ_of nty)))
      (Thm.global_cterm_of thy (Free ("r", Thm.typ_of oty)))
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
    val aty = #abs_type (#1 typedef_info)
    val th = freezeT thy' (#type_definition (#2 typedef_info))
    val (th_s, _) = Thm.dest_comb (Thm.dest_arg (Thm.cprop_of th))
    val (th_s, abst) = Thm.dest_comb th_s
    val rept = Thm.dest_arg th_s
    val [nty, oty] = Thm.dest_ctyp (Thm.ctyp_of_cterm rept)
    val typedef_th =
      typedef_hol2hollight nty oty rept abst cP
        (Thm.global_cterm_of thy' (Free ("a", aty)))
        (Thm.global_cterm_of thy' (Free ("r", Thm.typ_of ctT)))
    val th4 = typedef_th OF [#type_definition (#2 typedef_info)]
  in
    (th4, thy')
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

fun inst_type thy lambda th =
  let
    fun assoc _ [] = error "assoc"
      | assoc x ((x',y)::rest) = if x = x' then y else assoc x rest
    val lambda = map (fn (a, b) => (Thm.typ_of a, b)) lambda
    val tys_before = Term.add_tfrees (Thm.prop_of th) []
    val th1 = Thm.varifyT_global th
    val tys_after = Term.add_tvars (Thm.prop_of th1) []
    val tyinst =
      map2 (fn bef => fn iS =>
        (case try (assoc (TFree bef)) lambda of
          SOME cty => (iS, cty)
        | NONE => (iS, Thm.global_ctyp_of thy (TFree bef))))
      tys_before tys_after
  in
    Thm.instantiate (TVars.make tyinst, Vars.empty) th1
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

fun get (map, no) s =
  case Int.fromString s of
    NONE => error "Import_Rule.get: not a number"
  | SOME i => (case Inttab.lookup map (Int.abs i) of
      NONE => error "Import_Rule.get: lookup failed"
    | SOME res => (res, (if i < 0 then Inttab.delete (Int.abs i) map else map, no)))

fun getty i (thy, (tyi, tmi, thi)) = let val (i, tyi) = (get tyi i) in (i, (thy, (tyi, tmi, thi))) end
fun gettm i (thy, (tyi, tmi, thi)) = let val (i, tmi) = (get tmi i) in (i, (thy, (tyi, tmi, thi))) end
fun getth i (thy, (tyi, tmi, thi)) = let val (i, thi) = (get thi i) in (i, (thy, (tyi, tmi, thi))) end
fun set (map, no) v = (Inttab.update_new (no + 1, v) map, no + 1)
fun setty v (thy, (tyi, tmi, thi)) = (thy, (set tyi v, tmi, thi))
fun settm v (thy, (tyi, tmi, thi)) = (thy, (tyi, set tmi v, thi))
fun setth v (thy, (tyi, tmi, thi)) = (thy, (tyi, tmi, set thi v))

fun last_thm (_, _, (map, no)) =
  case Inttab.lookup map no of
    NONE => error "Import_Rule.last_thm: lookup failed"
  | SOME thm => thm

fun list_last (x :: y :: zs) = apfst (fn t => x :: y :: t) (list_last zs)
  | list_last [x] = ([], x)
  | list_last [] = error "list_last: empty"

fun pair_list (x :: y :: zs) = ((x, y) :: pair_list zs)
  | pair_list [] = []
  | pair_list _ = error "pair_list: odd list length"

fun store_thm binding thm thy =
  let
    val ctxt = Proof_Context.init_global thy
    val thm = Drule.export_without_context_open thm
    val tvs = Term.add_tvars (Thm.prop_of thm) []
    val tns = map (fn (_, _) => "'") tvs
    val nms = Name.variants (Variable.names_of ctxt) tns
    val vs = map TVar ((nms ~~ (map (snd o fst) tvs)) ~~ (map snd tvs))
    val thm' = Thm.instantiate (TVars.make (tvs ~~ map (Thm.ctyp_of ctxt) vs), Vars.empty) thm
  in
    snd (Global_Theory.add_thm ((binding, thm'), []) thy)
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
    fun process (#"R", [t]) = gettm t #>> refl #-> setth
      | process (#"B", [t]) = gettm t #>> beta #-> setth
      | process (#"1", [th]) = getth th #>> conj1 #-> setth
      | process (#"2", [th]) = getth th #>> conj2 #-> setth
      | process (#"H", [t]) = gettm t #>> Thm.apply \<^cterm>\<open>Trueprop\<close> #>> Thm.trivial #-> setth
      | process (#"A", [_, t]) =
          gettm t #>> Thm.apply \<^cterm>\<open>Trueprop\<close> #>> Skip_Proof.make_thm_cterm #-> setth
      | process (#"C", [th1, th2]) = getth th1 ##>> getth th2 #>> uncurry comb #-> setth
      | process (#"T", [th1, th2]) = getth th1 ##>> getth th2 #>> uncurry trans #-> setth
      | process (#"E", [th1, th2]) = getth th1 ##>> getth th2 #>> uncurry eq_mp #-> setth
      | process (#"D", [th1, th2]) = getth th1 ##>> getth th2 #>> uncurry deduct #-> setth
      | process (#"L", [t, th]) = gettm t ##>> (fn ti => getth th ti) #>> uncurry abs #-> setth
      | process (#"M", [s]) = (fn (thy, state) =>
          let
            val ctxt = Proof_Context.init_global thy
            val thm = freezeT thy (Global_Theory.get_thm thy s)
            val ((_, [th']), _) = Variable.import true [thm] ctxt
          in
            setth th' (thy, state)
          end)
      | process (#"Q", l) = (fn (thy, state) =>
          let
            val (tys, th) = list_last l
            val (th, tstate) = getth th (thy, state)
            val (tys, tstate) = fold_map getty tys tstate
          in
            setth (inst_type thy (pair_list tys) th) tstate
          end)
      | process (#"S", l) = (fn tstate =>
          let
            val (tms, th) = list_last l
            val (th, tstate) = getth th tstate
            val (tms, tstate) = fold_map gettm tms tstate
          in
            setth (inst (pair_list tms) th) tstate
          end)
      | process (#"F", [name, t]) = (fn tstate =>
          let
            val (tm, (thy, state)) = gettm t tstate
            val (th, thy) = def (make_name name) tm thy
          in
            setth th (thy, state)
          end)
      | process (#"F", [name]) = (fn (thy, state) => setth (mdef thy name) (thy, state))
      | process (#"Y", [name, absname, repname, t1, t2, th]) = (fn tstate =>
          let
            val (th, tstate) = getth th tstate
            val (t1, tstate) = gettm t1 tstate
            val (t2, (thy, state)) = gettm t2 tstate
            val (th, thy) = tydef name absname repname t1 t2 th thy
          in
            setth th (thy, state)
          end)
      | process (#"Y", [name, _, _]) = (fn (thy, state) => setth (mtydef thy name) (thy, state))
      | process (#"t", [n]) = (fn (thy, state) =>
          setty (Thm.global_ctyp_of thy (make_tfree n)) (thy, state))
      | process (#"a", n :: l) = (fn (thy, state) =>
          fold_map getty l (thy, state) |>>
            (fn tys => Thm.global_ctyp_of thy (make_type thy (n, map Thm.typ_of tys))) |-> setty)
      | process (#"v", [n, ty]) = (fn (thy, state) =>
          getty ty (thy, state) |>> (fn ty => Thm.global_cterm_of thy (make_free (n, Thm.typ_of ty))) |-> settm)
      | process (#"c", [n, ty]) = (fn (thy, state) =>
          getty ty (thy, state) |>> (fn ty => Thm.global_cterm_of thy (make_const thy (n, Thm.typ_of ty))) |-> settm)
      | process (#"f", [t1, t2]) = gettm t1 ##>> gettm t2 #>> uncurry Thm.apply #-> settm
      | process (#"l", [t1, t2]) = gettm t1 ##>> gettm t2 #>> uncurry Thm.lambda #-> settm
      | process (#"+", [s]) = (fn (thy, state) =>
          (store_thm (Binding.name (make_name s)) (last_thm state) thy, state))
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
  in #1 (fold process_line lines (thy, init_state)) end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>import_file\<close> "import recorded proofs from HOL Light"
    (Parse.path >> (fn name => Toplevel.theory (fn thy => import_file (Path.explode name) thy)))

end
