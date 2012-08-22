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
  val mdef : string -> theory -> thm
  val def : string -> cterm -> theory -> thm * theory
  val mtydef : string -> theory -> thm
  val tydef :
    string -> string -> string -> cterm -> cterm -> thm -> theory -> thm * theory
  val inst_type : (ctyp * ctyp) list -> thm -> theory -> thm
  val inst : (cterm * cterm) list -> thm -> thm

  type state
  val init_state : state
  val process_line : string -> (theory * state) -> (theory * state)
  val process_file : Path.T -> theory -> theory
end

structure Import_Rule: IMPORT_RULE =
struct

val init_state = ((Inttab.empty, 0), (Inttab.empty, 0), (Inttab.empty, 0))

type state = (ctyp Inttab.table * int) * (cterm Inttab.table * int) * (thm Inttab.table * int)

fun implies_elim_all th = implies_elim_list th (map Thm.assume (cprems_of th))

fun meta_mp th1 th2 =
  let
    val th1a = implies_elim_all th1
    val th1b = Thm.implies_intr (strip_imp_concl (cprop_of th2)) th1a
    val th2a = implies_elim_all th2
    val th3 = Thm.implies_elim th1b th2a
  in
    implies_intr_hyps th3
  end

fun meta_eq_to_obj_eq th =
  let
    val (tml, tmr) = Thm.dest_binop (strip_imp_concl (cprop_of th))
    val cty = ctyp_of_term tml
    val i = Drule.instantiate' [SOME cty] [SOME tml, SOME tmr]
      @{thm meta_eq_to_obj_eq}
  in
    Thm.implies_elim i th
  end

fun beta ct = meta_eq_to_obj_eq (Thm.beta_conversion false ct)

fun eq_mp th1 th2 =
  let
    val (tm1l, tm1r) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (cprop_of th1)))
    val i1 = Drule.instantiate' [] [SOME tm1l, SOME tm1r] @{thm iffD1}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun comb th1 th2 =
  let
    val t1c = Thm.dest_arg (strip_imp_concl (cprop_of th1))
    val t2c = Thm.dest_arg (strip_imp_concl (cprop_of th2))
    val (cf, cg) = Thm.dest_binop t1c
    val (cx, cy) = Thm.dest_binop t2c
    val [fd, fr] = Thm.dest_ctyp (ctyp_of_term cf)
    val i1 = Drule.instantiate' [SOME fd, SOME fr]
      [SOME cf, SOME cg, SOME cx, SOME cy] @{thm cong}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun trans th1 th2 =
  let
    val t1c = Thm.dest_arg (strip_imp_concl (cprop_of th1))
    val t2c = Thm.dest_arg (strip_imp_concl (cprop_of th2))
    val (r, s) = Thm.dest_binop t1c
    val (_, t) = Thm.dest_binop t2c
    val ty = ctyp_of_term r
    val i1 = Drule.instantiate' [SOME ty] [SOME r, SOME s, SOME t] @{thm trans}
    val i2 = meta_mp i1 th1
  in
    meta_mp i2 th2
  end

fun deduct th1 th2 =
  let
    val th1c = strip_imp_concl (cprop_of th1)
    val th2c = strip_imp_concl (cprop_of th2)
    val th1a = implies_elim_all th1
    val th2a = implies_elim_all th2
    val th1b = Thm.implies_intr th2c th1a
    val th2b = Thm.implies_intr th1c th2a
    val i = Drule.instantiate' []
      [SOME (Thm.dest_arg th1c), SOME (Thm.dest_arg th2c)] @{thm iffI}
    val i1 = Thm.implies_elim i (Thm.assume (cprop_of th2b))
    val i2 = Thm.implies_elim i1 th1b
    val i3 = Thm.implies_intr (cprop_of th2b) i2
    val i4 = Thm.implies_elim i3 th2b
  in
    implies_intr_hyps i4
  end

fun conj1 th =
  let
    val (tml, tmr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (cprop_of th)))
    val i = Drule.instantiate' [] [SOME tml, SOME tmr] @{thm conjunct1}
  in
    meta_mp i th
  end

fun conj2 th =
  let
    val (tml, tmr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (cprop_of th)))
    val i = Drule.instantiate' [] [SOME tml, SOME tmr] @{thm conjunct2}
  in
    meta_mp i th
  end

fun refl ctm =
  let
    val cty = Thm.ctyp_of_term ctm
  in
    Drule.instantiate' [SOME cty] [SOME ctm] @{thm refl}
  end

fun abs cv th =
  let
    val th1 = implies_elim_all th
    val (tl, tr) = Thm.dest_binop (Thm.dest_arg (strip_imp_concl (cprop_of th1)))
    val (ll, lr) = (Thm.lambda cv tl, Thm.lambda cv tr)
    val (al, ar) = (Thm.apply ll cv, Thm.apply lr cv)
    val bl = beta al
    val br = meta_eq_to_obj_eq (Thm.symmetric (Thm.beta_conversion false ar))
    val th2 = trans (trans bl th1) br
    val th3 = implies_elim_all th2
    val th4 = Thm.forall_intr cv th3
    val i = Drule.instantiate' [SOME (ctyp_of_term cv), SOME (ctyp_of_term tl)]
      [SOME ll, SOME lr] @{thm ext2}
  in
    meta_mp i th4
  end

fun freezeT thm =
  let
    val tvars = Term.add_tvars (prop_of thm) []
    val tfrees = map (fn ((t, _), s) => TFree (t, s)) tvars
    val tvars = map TVar tvars
    val thy = Thm.theory_of_thm thm
    fun inst ty = ctyp_of thy ty
  in
    Thm.instantiate ((map inst tvars ~~ map inst tfrees), []) thm
  end

fun def' constname rhs thy =
  let
    val rhs = term_of rhs
    val typ = type_of rhs
    val thy1 = Sign.add_consts_i [(Binding.name constname, typ, NoSyn)] thy
    val eq = Logic.mk_equals (Const (Sign.intern_const thy1 constname, typ), rhs)
    val (thms, thy2) = Global_Theory.add_defs false
      [((Binding.suffix_name "_hldef" (Binding.name constname), eq), [])] thy1
    val def_thm = freezeT (hd thms)
  in
    (meta_eq_to_obj_eq def_thm, thy2)
  end

fun mdef name thy =
  case Import_Data.get_const_def name thy of
    SOME th => th
  | NONE => error ("constant mapped but no definition: " ^ name)

fun def constname rhs thy =
  case Import_Data.get_const_def constname thy of
    SOME _ =>
      let
        val () = warning ("Const mapped but def provided: " ^ constname)
      in
        (mdef constname thy, thy)
      end
  | NONE => def' constname rhs thy

fun typedef_hollight th thy =
  let
    val (th_s, cn) = Thm.dest_comb (Thm.dest_arg (cprop_of th))
    val (th_s, abst) = Thm.dest_comb th_s
    val rept = Thm.dest_arg th_s
    val P = Thm.dest_arg cn
    val [nty, oty] = Thm.dest_ctyp (ctyp_of_term rept)
  in
    Drule.instantiate' [SOME nty, SOME oty] [SOME rept, SOME abst, SOME P,
      SOME (cterm_of thy (Free ("a", typ_of nty))),
      SOME (cterm_of thy (Free ("r", typ_of oty)))] @{thm typedef_hol2hollight}
  end

fun tydef' tycname abs_name rep_name cP ct td_th thy =
  let
    val ctT = ctyp_of_term ct
    val nonempty = Drule.instantiate' [SOME ctT] [SOME cP, SOME ct] @{thm light_ex_imp_nonempty}
    val th2 = meta_mp nonempty td_th
    val c = case concl_of th2 of
        _ $ (Const(@{const_name Ex},_) $ Abs(_,_,Const(@{const_name Set.member},_) $ _ $ c)) => c
      | _ => error "type_introduction: bad type definition theorem"
    val tfrees = Term.add_tfrees c []
    val tnames = sort_strings (map fst tfrees)
    val ((_, typedef_info), thy') =
     Typedef.add_typedef_global false NONE
       (Binding.name tycname, map (rpair dummyS) tnames, NoSyn) c
       (SOME(Binding.name rep_name,Binding.name abs_name)) (rtac th2 1) thy
    val aty = #abs_type (#1 typedef_info)
    val th = freezeT (#type_definition (#2 typedef_info))
    val (th_s, _) = Thm.dest_comb (Thm.dest_arg (cprop_of th))
    val (th_s, abst) = Thm.dest_comb th_s
    val rept = Thm.dest_arg th_s
    val [nty, oty] = Thm.dest_ctyp (ctyp_of_term rept)
    val typedef_th =
       Drule.instantiate'
          [SOME nty, SOME oty]
          [SOME rept, SOME abst, SOME cP, SOME (cterm_of thy' (Free ("a", aty))),
             SOME (cterm_of thy' (Free ("r", typ_of ctT)))]
          @{thm typedef_hol2hollight}
    val th4 = typedef_th OF [#type_definition (#2 typedef_info)]
  in
    (th4, thy')
  end

fun mtydef name thy =
  case Import_Data.get_typ_def name thy of
    SOME thn => meta_mp (typedef_hollight thn thy) thn
  | NONE => error ("type mapped but no tydef thm registered: " ^ name)

fun tydef tycname abs_name rep_name P t td_th thy =
  case Import_Data.get_typ_def tycname thy of
    SOME _ =>
      let
        val () = warning ("Type mapped but proofs provided: " ^ tycname)
      in
        (mtydef tycname thy, thy)
      end
  | NONE => tydef' tycname abs_name rep_name P t td_th thy

fun inst_type lambda th thy =
  let
    fun assoc _ [] = error "assoc"
      | assoc x ((x',y)::rest) = if x = x' then y else assoc x rest
    val lambda = map (fn (a, b) => (typ_of a, b)) lambda
    val tys_before = Term.add_tfrees (prop_of th) []
    val th1 = Thm.varifyT_global th
    val tys_after = Term.add_tvars (prop_of th1) []
    val tyinst = map2 (fn bef => fn iS =>
       (case try (assoc (TFree bef)) lambda of
              SOME cty => (ctyp_of thy (TVar iS), cty)
            | NONE => (ctyp_of thy (TVar iS), ctyp_of thy (TFree bef))
       )) tys_before tys_after
  in
    Thm.instantiate (tyinst,[]) th1
  end

fun inst sigma th =
  let
    val (dom, rng) = ListPair.unzip (rev sigma)
  in
    th |> forall_intr_list dom
       |> forall_elim_list rng
  end

fun transl_dotc #"." = "dot"
  | transl_dotc c = Char.toString c
val transl_dot = String.translate transl_dotc

fun transl_qmc #"?" = "t"
  | transl_qmc c = Char.toString c
val transl_qm = String.translate transl_qmc

fun getconstname s thy =
  case Import_Data.get_const_map s thy of
      SOME s => s
    | NONE => Sign.full_name thy (Binding.name (transl_dot s))
fun gettyname s thy =
  case Import_Data.get_typ_map s thy of
    SOME s => s
  | NONE => Sign.full_name thy (Binding.name s)

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

fun listLast (h1 :: (h2 :: t)) = apfst (fn t => h1 :: h2 :: t) (listLast t)
  | listLast [p] = ([], p)
  | listLast [] = error "listLast: empty"

fun pairList (h1 :: (h2 :: t)) = ((h1, h2) :: pairList t)
  | pairList [] = []
  | pairList _ = error "pairList: odd list length"

fun store_thm binding thm thy =
  let
    val thm = Drule.export_without_context_open thm
    val tvs = Term.add_tvars (prop_of thm) []
    val tns = map (fn (_, _) => "'") tvs
    val nms = fst (fold_map Name.variant tns (Variable.names_of (Proof_Context.init_global thy)))
    val vs = map TVar ((nms ~~ (map (snd o fst) tvs)) ~~ (map snd tvs))
    val cvs = map (ctyp_of thy) vs
    val ctvs = map (ctyp_of thy) (map TVar tvs)
    val thm' = Thm.instantiate ((ctvs ~~ cvs), []) thm
  in
    snd (Global_Theory.add_thm ((binding, thm'), []) thy)
  end

fun log_timestamp () =
  let
    val time = Time.now ()
    val millis = nth (space_explode "." (Time.fmt 3 time)) 1
  in
    Date.fmt "%d.%m.%Y %H:%M:%S." (Date.fromTimeLocal time) ^ millis
  end

fun process_line str tstate =
  let
    fun process tstate (#"R", [t]) = gettm t tstate |>> refl |-> setth
      | process tstate (#"B", [t]) = gettm t tstate |>> beta |-> setth
      | process tstate (#"1", [th]) = getth th tstate |>> conj1 |-> setth
      | process tstate (#"2", [th]) = getth th tstate |>> conj2 |-> setth
      | process tstate (#"H", [t]) =
          gettm t tstate |>> Thm.apply @{cterm Trueprop} |>> Thm.trivial |-> setth
      | process tstate (#"A", [_, t]) =
          gettm t tstate |>> Thm.apply @{cterm Trueprop} |>> Skip_Proof.make_thm_cterm |-> setth
      | process tstate (#"C", [th1, th2]) =
          getth th1 tstate ||>> getth th2 |>> (fn (t1, t2) => comb t1 t2) |-> setth
      | process tstate (#"T", [th1, th2]) =
          getth th1 tstate ||>> getth th2 |>> (fn (t1, t2) => trans t1 t2) |-> setth
      | process tstate (#"E", [th1, th2]) =
          getth th1 tstate ||>> getth th2 |>> (fn (t1, t2) => eq_mp t1 t2) |-> setth
      | process tstate (#"D", [th1, th2]) =
          getth th1 tstate ||>> getth th2 |>> (fn (t1, t2) => deduct t1 t2) |-> setth
      | process tstate (#"L", [t, th]) =
          gettm t tstate ||>> (fn ti => getth th ti) |>> (fn (tm, th) => abs tm th) |-> setth
      | process (thy, state) (#"M", [s]) =
          let
            val ctxt = Variable.set_body false (Proof_Context.init_global thy)
            val thm = freezeT (Global_Theory.get_thm thy s)
            val ((_, [th']), _) = Variable.import true [thm] ctxt
          in
            setth th' (thy, state)
          end
      | process (thy, state) (#"Q", l) =
          let
            val (tys, th) = listLast l
            val (th, tstate) = getth th (thy, state)
            val (tys, tstate) = fold_map getty tys tstate
          in
            setth (inst_type (pairList tys) th thy) tstate
          end
      | process tstate (#"S", l) =
          let
            val (tms, th) = listLast l
            val (th, tstate) = getth th tstate
            val (tms, tstate) = fold_map gettm tms tstate
          in
            setth (inst (pairList tms) th) tstate
          end
      | process tstate (#"F", [name, t]) =
          let
            val (tm, (thy, state)) = gettm t tstate
            val (th, thy) = def (transl_dot name) tm thy
          in
            setth th (thy, state)
          end
      | process (thy, state) (#"F", [name]) = setth (mdef name thy) (thy, state)
      | process tstate (#"Y", [name, absname, repname, t1, t2, th]) =
          let
            val (th, tstate) = getth th tstate
            val (t1, tstate) = gettm t1 tstate
            val (t2, (thy, state)) = gettm t2 tstate
            val (th, thy) = tydef name absname repname t1 t2 th thy
          in
            setth th (thy, state)
          end
      | process (thy, state) (#"Y", [name, _, _]) = setth (mtydef name thy) (thy, state)
      | process (thy, state) (#"t", [n]) =
          setty (ctyp_of thy (TFree ("'" ^ (transl_qm n), ["HOL.type"]))) (thy, state)
      | process (thy, state) (#"a", n :: l) =
          fold_map getty l (thy, state) |>>
            (fn tys => ctyp_of thy (Type (gettyname n thy, map typ_of tys))) |-> setty
      | process (thy, state) (#"v", [n, ty]) =
          getty ty (thy, state) |>> (fn ty => cterm_of thy (Free (transl_dot n, typ_of ty))) |-> settm
      | process (thy, state) (#"c", [n, ty]) =
          getty ty (thy, state) |>> (fn ty => cterm_of thy (Const (getconstname n thy, typ_of ty))) |-> settm
      | process tstate (#"f", [t1, t2]) =
          gettm t1 tstate ||>> gettm t2 |>> (fn (t1, t2) => Thm.apply t1 t2) |-> settm
      | process tstate (#"l", [t1, t2]) =
          gettm t1 tstate ||>> gettm t2 |>> (fn (t1, t2) => Thm.lambda t1 t2) |-> settm
      | process (thy, state) (#"+", [s]) =
          let
            val _ = tracing ("NOTING " ^ log_timestamp () ^ ": " ^ s)
          in
            (store_thm (Binding.name (transl_dot s)) (last_thm state) thy, state)
          end
      | process _ (c, _) = error ("process: unknown command: " ^ String.implode [c])

    fun parse_line s =
        case String.tokens (fn x => (x = #"\n" orelse x = #" ")) s of
          [] => error "parse_line: empty"
        | h :: t => (case String.explode h of
            [] => error "parse_line: empty command"
          | sh :: st => (sh, (String.implode st) :: t))
  in
    process tstate (parse_line str)
  end

fun process_file path thy =
  (thy, init_state) |> File.fold_lines process_line path |> fst

val _ = Outer_Syntax.command @{command_spec "import_file"}
  "Import a recorded proof file"
  (Parse.path >> (fn name => Toplevel.theory (fn thy => process_file (Path.explode name) thy)))


end
