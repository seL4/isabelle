(*  Title:      Tools/profiling.thy
    Author:     Makarius

Session profiling based on loaded ML image.
*)

theory Profiling
  imports Pure
begin

ML \<open>
signature PROFILING =
sig
  val locales: theory -> string list
  val locale_thms: theory -> string -> thm list
  val locales_thms: theory -> thm list
  val global_thms: theory -> thm list
  val all_thms: theory -> thm list
  type session_statistics =
   {theories: int,
    garbage_theories: int,
    locales: int,
    locale_thms: int,
    global_thms: int,
    sizeof_thys_id: int,
    sizeof_thms_id: int,
    sizeof_terms: int,
    sizeof_types: int,
    sizeof_names: int,
    sizeof_spaces: int}
  val session_statistics: string list -> session_statistics
  val main: unit -> unit
end;

structure Profiling: PROFILING =
struct

(* theory content *)

fun locales thy =
  let
    val parent_spaces = map Locale.locale_space (Theory.parents_of thy);
    fun add name =
      if exists (fn space => Name_Space.declared space name) parent_spaces then I
      else cons name;
  in fold add (Locale.get_locales thy) [] end;

fun proper_thm thm = not (Thm.eq_thm_prop (Drule.dummy_thm, thm));

fun locale_thms thy loc =
  (Locale.locale_notes thy loc, []) |->
    (fold (#2 #> fold (#2 #> (fold (#1 #> fold (fn thm => proper_thm thm ? cons thm ))))));

fun locales_thms thy =
  maps (locale_thms thy) (locales thy);

fun global_thms thy =
  Facts.dest_static true
    (map Global_Theory.facts_of (Theory.parents_of thy)) (Global_Theory.facts_of thy)
  |> maps #2;

fun all_thms thy = locales_thms thy @ global_thms thy;


(* session content *)

fun session_content thys =
  let
    val thms = maps all_thms thys;
    val thys_id = map Context.theory_id thys;
    val thms_id = map Thm.theory_id thms;
    val terms =
      Termset.dest ((fold o Thm.fold_terms {hyps = true}) Termset.insert thms Termset.empty);
    val types = Typset.dest ((fold o fold_types) Typset.insert terms Typset.empty);
    val spaces =
      maps (fn f => map f thys)
       [Sign.class_space,
        Sign.type_space,
        Sign.const_space,
        Theory.axiom_space,
        Thm.oracle_space,
        Global_Theory.fact_space,
        Locale.locale_space,
        Attrib.attribute_space o Context.Theory,
        Method.method_space o Context.Theory];
     val names = Symset.dest (Symset.merges (map (Symset.make o Name_Space.get_names) spaces));
  in
    {thys_id = thys_id, thms_id = thms_id, terms = terms,
      types = types, names = names, spaces = spaces}
  end;

fun sizeof1_diff (a, b) = ML_Heap.sizeof1 a - ML_Heap.sizeof1 b;
fun sizeof_list_diff (a, b) = ML_Heap.sizeof_list a - ML_Heap.sizeof_list b;
fun sizeof_diff (a, b) = ML_Heap.sizeof a - ML_Heap.sizeof b;


(* session statistics *)

type session_statistics =
 {theories: int,
  garbage_theories: int,
  locales: int,
  locale_thms: int,
  global_thms: int,
  sizeof_thys_id: int,
  sizeof_thms_id: int,
  sizeof_terms: int,
  sizeof_types: int,
  sizeof_names: int,
  sizeof_spaces: int};

fun session_statistics theories : session_statistics =
  let
    val theories_member = Symtab.defined (Symtab.make_set theories) o Context.theory_long_name;

    val context_thys =
      #contexts (Context.finish_tracing ())
      |> map_filter (fn (Context.Theory thy, _) => SOME thy | _ => NONE);

    val loader_thys = map Thy_Info.get_theory (Thy_Info.get_names ());
    val loaded_thys = filter theories_member loader_thys;
    val loaded_context_thys = filter theories_member context_thys;

    val all_thys = loader_thys @ context_thys;
    val base_thys = filter_out theories_member all_thys;

    val {thys_id = all_thys_id, thms_id = all_thms_id, terms = all_terms,
          types = all_types, names = all_names, spaces = all_spaces} = session_content all_thys;
    val {thys_id = base_thys_id, thms_id = base_thms_id, terms = base_terms,
          types = base_types, names = base_names, spaces = base_spaces} = session_content base_thys;

    val n = length loaded_thys;
    val m = (case length loaded_context_thys of 0 => 0 | l => l - n);
  in
    {theories = n,
     garbage_theories = m,
     locales = Integer.sum (map (length o locales) loaded_thys),
     locale_thms = Integer.sum (map (length o locales_thms) loaded_thys),
     global_thms = Integer.sum (map (length o global_thms) loaded_thys),
     sizeof_thys_id =
      sizeof1_diff ((all_thys_id, all_thms_id), (base_thys_id, all_thms_id)) -
        sizeof_list_diff (all_thys_id, base_thys_id),
     sizeof_thms_id =
      sizeof1_diff ((all_thms_id, all_thys_id), (base_thms_id, all_thys_id)) -
        sizeof_list_diff (all_thms_id, base_thms_id),
     sizeof_terms =
      sizeof1_diff ((all_terms, all_types, all_names), (base_terms, all_types, all_names)) -
        sizeof_list_diff (all_terms, base_terms),
     sizeof_types =
      sizeof1_diff ((all_types, all_names), (base_types, all_names)) -
        sizeof_list_diff (all_types, base_types),
     sizeof_spaces =
      sizeof1_diff ((all_spaces, all_names), (base_spaces, all_names)) -
        sizeof_list_diff (all_spaces, base_spaces),
     sizeof_names = sizeof_diff (all_names, base_names)}
  end;


(* main entry point for external process *)

local

val decode_args : string list XML.Decode.T =
  let open XML.Decode in list string end;

val encode_result : session_statistics XML.Encode.T =
  (fn {theories = a,
       garbage_theories = b,
       locales = c,
       locale_thms = d,
       global_thms = e,
       sizeof_thys_id = f,
       sizeof_thms_id = g,
       sizeof_terms = h,
       sizeof_types = i,
       sizeof_names = j,
       sizeof_spaces = k} => ((a, (b, (c, (d, (e, (f, (g, (h, (i, (j, k)))))))))))) #>
  let open XML.Encode in
    pair int (pair int (pair int (pair int (pair int (pair int (pair int
      (pair int (pair int (pair int int)))))))))
  end;

in

fun main () =
  (case Options.default_string \<^system_option>\<open>profiling_dir\<close> of
    "" => ()
  | dir_name =>
      let
        val dir = Path.explode dir_name;
        val args = decode_args (YXML.parse_body (File.read (dir + \<^path>\<open>args.yxml\<close>)));
        val result = session_statistics args;
      in File.write (dir + \<^path>\<open>result.yxml\<close>) (YXML.string_of_body (encode_result result)) end);

end;

end;
\<close>

ML_command \<open>Profiling.main ()\<close>

end
