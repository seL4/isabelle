(*  Title:      doc-src/more_antiquote.ML
    Author:     Florian Haftmann, TU Muenchen

More antiquotations.
*)

signature MORE_ANTIQUOTE =
sig
  val typewriter: string -> string
end;

structure More_Antiquote : MORE_ANTIQUOTE =
struct

(* printing typewriter lines *)

fun typewriter s =
  let
    val parse = Scan.repeat
      (Scan.this_string "\n" |-- Scan.succeed "\\\\\n\\hspace*{0pt}"
        || (Scan.this_string " "
          || Scan.this_string "."
          || Scan.this_string ","
          || Scan.this_string ":"
          || Scan.this_string ";"
          || Scan.this_string "\"" |-- Scan.succeed "{\\char34}"
          || Scan.this_string "#" |-- Scan.succeed "{\\char35}"
          || Scan.this_string "$" |-- Scan.succeed "{\\char36}"
          || Scan.this_string "%" |-- Scan.succeed "{\\char37}"
          || Scan.this_string "&" |-- Scan.succeed "{\\char38}"
          || Scan.this_string "\\" |-- Scan.succeed "{\\char92}"
          || Scan.this_string "^" |-- Scan.succeed "{\\char94}"
          || Scan.this_string "_" |-- Scan.succeed "{\\char95}"
          || Scan.this_string "{" |-- Scan.succeed "{\\char123}"
          || Scan.this_string "}" |-- Scan.succeed "{\\char125}"
          || Scan.this_string "~" |-- Scan.succeed "{\\char126}")
          -- Scan.repeat (Scan.this_string " ")
          >> (fn (x, xs) => x ^ replicate_string (length xs) "~")
        || Scan.one Symbol.not_eof);
    fun is_newline s = (s = "\n");
    val cs = explode s |> take_prefix is_newline |> snd
      |> take_suffix is_newline |> fst;
    val (texts, []) =  Scan.finite Symbol.stopper parse cs
  in if null texts
    then ""
    else implode ("\\isatypewriter%\n\\noindent%\n\\hspace*{0pt}" :: texts)
  end


(* class and type constructor antiquotation *)

local

val pr_text = enclose "\\isa{" "}" o Pretty.output o Pretty.str;

fun pr_class ctxt = Sign.read_class (ProofContext.theory_of ctxt)
  #> Sign.extern_class (ProofContext.theory_of ctxt)
  #> pr_text;

fun pr_type ctxt = Sign.intern_type (ProofContext.theory_of ctxt)
  #> tap (Sign.arity_number (ProofContext.theory_of ctxt))
  #> Sign.extern_type (ProofContext.theory_of ctxt)
  #> pr_text;

in

val _ = ThyOutput.antiquotation "class" (Scan.lift Args.name) (pr_class o #context);
val _ = ThyOutput.antiquotation "type" (Scan.lift Args.name) (pr_type o #context);

end;


(* code theorem antiquotation *)

local

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

fun no_vars ctxt thm =
  let
    val ctxt' = Variable.set_body false ctxt;
    val ((_, [thm]), _) = Variable.import_thms true [thm] ctxt';
  in thm end;

fun pretty_code_thm src ctxt raw_const =
  let
    val thy = ProofContext.theory_of ctxt;
    val const = Code_Unit.check_const thy raw_const;
    val (_, funcgr) = Code_Preproc.obtain thy [const] [];
    fun holize thm = @{thm meta_eq_to_obj_eq} OF [thm];
    val thms = Code_Preproc.eqns funcgr const
      |> map_filter (fn (thm, linear) => if linear then SOME thm else NONE)
      |> map (holize o no_vars ctxt o AxClass.overload thy);
  in ThyOutput.output (ThyOutput.maybe_pretty_source (pretty_thm ctxt) src thms) end;

in

val _ = ThyOutput.antiquotation "code_thms" Args.term
  (fn {source, context, ...} => pretty_code_thm source context);

end;


(* code antiquotation *)

local

  val parse_const_terms = Scan.repeat1 Args.term
    >> (fn ts => fn thy => map (Code_Unit.check_const thy) ts);
  val parse_consts = Scan.lift (Args.parens (Args.$$$ "consts")) |-- parse_const_terms
    >> (fn mk_cs => fn thy => fn naming => map_filter (Code_Thingol.lookup_const naming) (mk_cs thy));
  val parse_types = Scan.lift (Args.parens (Args.$$$ "types") |-- Scan.repeat1 Args.name)
    >> (fn tycos => fn thy => fn naming => map_filter (Code_Thingol.lookup_tyco naming o Sign.intern_type thy) tycos);
  val parse_classes = Scan.lift (Args.parens (Args.$$$ "classes") |-- Scan.repeat1 Args.name)
    >> (fn classes => fn thy => fn naming => map_filter (Code_Thingol.lookup_class naming o Sign.intern_class thy) classes);
  val parse_instances = Scan.lift (Args.parens (Args.$$$ "instances") |-- Scan.repeat1 (Args.name --| Args.$$$ "::" -- Args.name))
    >> (fn insts => fn thy => fn naming => map_filter (Code_Thingol.lookup_instance naming o apsnd (Sign.intern_type thy) o apfst (Sign.intern_class thy) o swap) insts);
  val parse_names = parse_consts || parse_types || parse_classes || parse_instances;

in

val _ = ThyOutput.antiquotation "code_stmts"
  (parse_const_terms -- Scan.repeat parse_names -- Scan.lift (Args.parens Args.name))
  (fn {context = ctxt, ...} => fn ((mk_cs, mk_stmtss), target) =>
    let val thy = ProofContext.theory_of ctxt in
      Code_Target.code_of thy
        target "Example" (mk_cs thy)
        (fn naming => maps (fn f => f thy naming) mk_stmtss)
      |> typewriter
    end);

end;

end;
