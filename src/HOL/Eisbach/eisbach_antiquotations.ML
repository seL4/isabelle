(*  Title:      HOL/Eisbach/eisbach_antiquotations.ML
    Author:     Daniel Matichuk, NICTA/UNSW

ML antiquotations for Eisbach.
*)

structure Eisbach_Antiquotations: sig end =
struct

(** evaluate Eisbach method from ML **)

val _ =
  Theory.setup
    (ML_Antiquotation.inline @{binding method}  (* FIXME ML_Antiquotation.value (!?) *)
      (Args.context -- Scan.lift (Args.mode "drop_cases") -- Scan.lift (Parse.position Parse.name)
        >> (fn ((ctxt, drop_cases), nameref) =>
          let
            val ((targs, (factargs, margs)), _) = Method_Closure.get_method ctxt nameref;

            val has_factargs = not (null factargs);

            val (targnms, ctxt') =
              fold_map (fn (Var ((x, _), _)) => ML_Context.variant x) targs ctxt;
            val (margnms, ctxt'') = fold_map ML_Context.variant margs ctxt';
            val (factsnm, _) = ML_Context.variant "facts" ctxt'';

            val fn_header =
              margnms
              |> has_factargs ? append [factsnm]
              |> append targnms
              |> map (fn nm => "fn " ^ nm ^ " => ")
              |> implode;

            val ML_context = ML_Context.struct_name ctxt ^ ".ML_context";
            val ml_inner =
              ML_Syntax.atomic
                ("Method_Closure.get_method " ^  ML_context ^
                  ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_position nameref ^
                  "|> (fn ((targs, (_, margs)), text) => Method_Closure.eval_method " ^
                  ML_context ^ " ((targs, margs), text))");

            val drop_cases_suffix =
              if drop_cases then "#> (fn f => (fn ctxt => fn thms => f ctxt thms |> Seq.map snd))"
              else "";

            val factsnm = if has_factargs then factsnm else "[]";
          in
            ML_Syntax.atomic
              (fn_header ^ ml_inner ^ " " ^ ML_Syntax.print_list I targnms ^ " " ^
                factsnm ^ " " ^
                ML_Syntax.print_list I margnms ^ drop_cases_suffix)
          end)));

end;
