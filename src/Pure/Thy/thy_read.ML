(*  Title:      Pure/Thy/thy_read.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel and Sonia Mahjoub and
                Tobias Nipkow and L C Paulson
    Copyright   1994 TU Muenchen

Functions for reading theory files.
*)

signature THY_READ =
sig
  datatype basetype = Thy  of string
                    | File of string

  val loadpath       : string list ref
  val delete_tmpfiles: bool ref

  val use_thy        : string -> unit
  val time_use_thy   : string -> unit
  val use_dir        : string -> unit
  val exit_use_dir   : string -> unit
  val update         : unit -> unit
  val unlink_thy     : string -> unit
  val mk_base        : basetype list -> string -> theory
end;


structure ThyRead: THY_READ =
struct

open ThmDatabase ThyInfo BrowserInfo;


datatype basetype = Thy  of string
                  | File of string;


(*Default search path for theory files*)
val loadpath = ref ["."];


(*Directory given as parameter to use_thy. This is temporarily added to
  loadpath while the theory's ancestors are loaded.*)
val tmp_loadpath = ref [] : string list ref;


(*Remove temporary files after use*)
val delete_tmpfiles = ref true;
       

(*Make name of the TextIO.output ML file for a theory *)
fun out_name tname = "." ^ tname ^ ".thy.ML";


(*Read a file specified by thy_file containing theory tname*)
fun read_thy tname thy_file =
  let
    val intext = File.read thy_file;
    val outext = ThySyn.parse tname intext;
  in
    File.write (out_name tname) outext
  end;


(*Check if a theory was completly loaded *)
fun already_loaded thy =
  let val t = get_thyinfo thy
  in if is_none t then false
     else let val {thy_time, ml_time, ...} = the t
          in is_some thy_time andalso is_some ml_time end
  end;


(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML *)
fun thy_unchanged thy thy_file ml_file =
  case get_thyinfo thy of
      Some {thy_time, ml_time, ...} =>
       let val tn = is_none thy_time;
           val mn = is_none ml_time
       in if not tn andalso not mn then
            ((file_info thy_file = the thy_time),
             (file_info ml_file = the ml_time))
          else if not tn andalso mn then
            (file_info thy_file = the thy_time, false)
          else
            (false, false)
       end
    | None => (false, false)


(*Get all descendants of a theory list *)
fun get_descendants [] = []
  | get_descendants (t :: ts) =
      let val children = children_of t
      in children union (get_descendants (children union ts)) end;


(*Find a file using a list of paths if no absolute or relative path is
  specified.*)
fun find_file "" name =
      let fun find_it (cur :: paths) =
                if File.exists (tack_on cur name) then
                  (if cur = "." then name else tack_on cur name)
                else
                  find_it paths
           | find_it [] = ""
      in find_it (!tmp_loadpath @ !loadpath) end
  | find_file path name =
      if File.exists (tack_on path name) then tack_on path name
                                         else "";


(*Get absolute pathnames for a new or already loaded theory *)
fun get_filenames path name =
  let fun new_filename () =
        let val found = find_file path (name ^ ".thy");
            val absolute_path = absolute_path (OS.FileSys.getDir ());
            val thy_file = absolute_path found;
            val (thy_path, _) = split_filename thy_file;
            val found = find_file path (name ^ ".ML");
            val ml_file = if thy_file = "" then absolute_path found
                          else if File.exists (tack_on thy_path (name ^ ".ML"))
                          then tack_on thy_path (name ^ ".ML")
                          else "";
            val searched_dirs = if path = "" then (!tmp_loadpath @ !loadpath)
                                             else [path]
        in if thy_file = "" andalso ml_file = "" then
             error ("Could not find file \"" ^ name ^ ".thy\" or \""
                    ^ name ^ ".ML\" for theory \"" ^ name ^ "\"\n"
                    ^ "in the following directories: \"" ^
                    (space_implode "\", \"" searched_dirs) ^ "\"")
           else ();
           (thy_file, ml_file)
        end;

      val tinfo = get_thyinfo name;
  in if is_some tinfo andalso path = "" then
       let val {path = abs_path, ...} = the tinfo;
           val (thy_file, ml_file) = if abs_path = "" then new_filename ()
                                     else (find_file abs_path (name ^ ".thy"),
                                           find_file abs_path (name ^ ".ML"))
       in if thy_file = "" andalso ml_file = "" then
            (warning ("File \"" ^ (tack_on path name)
                      ^ ".thy\"\ncontaining theory \"" ^ name
                      ^ "\" no longer exists.");
             new_filename ()
            )
          else (thy_file, ml_file)
       end
     else new_filename ()
  end;


(*Remove theory from all child lists in loaded_thys *)
fun unlink_thy tname =
  let fun remove ({path, children, parents, thy_time, ml_time, theory}) =
        {path = path, children = children \ tname, parents = parents,
                 thy_time = thy_time, ml_time = ml_time, theory = theory}
  in loaded_thys := Symtab.map remove (!loaded_thys) end;


(*Remove a theory from loaded_thys *)
fun remove_thy tname =
  loaded_thys := Symtab.make (filter_out (fn (id, _) => id = tname)
                 (Symtab.dest (!loaded_thys)));


(*Change thy_time and ml_time for an existent item *)
fun set_info tname thy_time ml_time =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
          Some ({path, children, parents, theory, thy_time = _, ml_time = _}) =>
            {path = path, children = children, parents = parents,
                     thy_time = thy_time, ml_time = ml_time, theory = theory}
        | None => error ("set_info: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;


(*Mark theory as changed since last read if it has been completly read *)
fun mark_outdated tname =
  let val t = get_thyinfo tname;
  in if is_none t then ()
     else
       let val {thy_time, ml_time, ...} = the t
       in set_info tname (if is_none thy_time then None else Some "")
                         (if is_none ml_time then None else Some "")
       end
  end;


(*Read .thy and .ML files that haven't been read yet or have changed since
  they were last read;
  loaded_thys is a thy_info list ref containing all theories that have
  completly been read by this and preceeding use_thy calls.
  tmp_loadpath is temporarily added to loadpath while the ancestors of a
  theory that the user specified as e.g. "ex/Nat" are loaded. Because of
  raised exceptions we cannot guarantee that it's value is always valid.
  Therefore this has to be assured by the first parameter of use_thy1 which
  is "true" if use_thy gets invoked by mk_base and "false" else.
*)
fun use_thy1 tmp_loadpath_valid name =
  let
    val (path, tname) = split_filename name;
    val dummy = (tmp_loadpath :=
      (if not tmp_loadpath_valid then (if path = "" then [] else [path])
       else !tmp_loadpath));
    val (thy_file, ml_file) = get_filenames path tname;
    val (abs_path, _) = if thy_file = "" then split_filename ml_file
                        else split_filename thy_file;
    val (thy_uptodate, ml_uptodate) = thy_unchanged tname thy_file ml_file;
    val old_parents = parents_of_name tname;

    (*Set absolute path for loaded theory *)
    fun set_path () =
      let val {path = _, children, parents, thy_time, ml_time, theory} =
            the (Symtab.lookup (!loaded_thys, tname));
      in loaded_thys := Symtab.update ((tname,
                          {path = abs_path,
                                   children = children, parents = parents,
                                   thy_time = thy_time, ml_time = ml_time,
                                   theory = theory}),
                          !loaded_thys)
      end;

    (*Mark all direct descendants of a theory as changed *)
    fun mark_children thy =
      let val children = children_of thy;
          val present = filter (is_some o get_thyinfo) children;
          val loaded = filter already_loaded present;
      in if loaded <> [] then
           writeln ("The following children of theory " ^ (quote thy)
                    ^ " are now out-of-date: "
                    ^ (quote (space_implode "\",\"" loaded)))
         else ();
         seq mark_outdated present
      end;

    (*Make sure that loaded_thys contains an entry for tname*)
    fun init_thyinfo () =
    let val tinfo = {path = "", children = [], parents = [],
                             thy_time = None, ml_time = None,
                             theory = None};
    in if is_some (get_thyinfo tname) then ()
       else loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys)
    end;
  in if thy_uptodate andalso ml_uptodate then ()
     else
      (if thy_file = "" then ()
       else
         (writeln ("Reading \"" ^ name ^ ".thy\"");

          init_thyinfo ();
          read_thy tname thy_file;
          Use.use (out_name tname);

          if not (!delete_tmpfiles) then ()
          else OS.FileSys.remove (out_name tname);

          thyfile2html tname abs_path
         );
       
       set_info tname (Some (file_info thy_file)) None;
                                       (*mark thy_file as successfully loaded*)

       if ml_file = "" then ()
       else (writeln ("Reading \"" ^ name ^ ".ML\"");
             Use.use ml_file);

       (*Store theory again because it could have been redefined*)
       use_strings
         ["val _ = store_theory (" ^ tname ^ ".thy, " ^ quote tname ^ ");"];

       (*Add theory to list of all loaded theories (for index.html)
         and add it to its parents' sub-charts*)
       let val path = path_of tname;
       in if path = "" then               (*first time theory has been read*)
          (
            (*Add theory to list of all loaded theories (for index.html)
              and add it to its parents' sub-charts*)
            mk_html tname abs_path old_parents;

            (*Add theory to graph definition file*)
            mk_graph tname abs_path
          )
          else ()
       end;

       (*Now set the correct info*)
       set_info tname (Some (file_info thy_file)) (Some (file_info ml_file));
       set_path ();

       (*Mark theories that have to be reloaded*)
       mark_children tname;

       (*Close HTML file*)
       close_html ()
      )
  end;


val use_thy = use_thy1 false;


fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");
    use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****"))
   );


(*Load all thy or ML files that have been changed and also
  all theories that depend on them.*)
fun update () =
  let (*List theories in the order they have to be loaded in.*)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level [] = []
                  | next_level (t :: ts) =
                      let val children = children_of t
                      in children union (next_level ts) end;

                val descendants = next_level thys;
            in load_order descendants ((result \\ descendants) @ descendants)
            end;

      fun reload_changed (t :: ts) =
            let val abspath = case get_thyinfo t of
                                  Some ({path, ...}) => path
                                | None => "";

                val (thy_file, ml_file) = get_filenames abspath t;
                val (thy_uptodate, ml_uptodate) =
                        thy_unchanged t thy_file ml_file;
            in if thy_uptodate andalso ml_uptodate then ()
                                                   else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ();

     (*Remove all theories that are no descendants of ProtoPure.
       If there are still children in the deleted theory's list
       schedule them for reloading *)
     fun collect_garbage no_garbage =
       let fun collect ((tname, {children, ...}: thy_info) :: ts) =
                 if tname mem no_garbage then collect ts
                 else (writeln ("Theory \"" ^ tname ^
                       "\" is no longer linked with ProtoPure - removing it.");
                       remove_thy tname;
                       seq mark_outdated children)
             | collect [] = ()
       in collect (Symtab.dest (!loaded_thys)) end;
  in tmp_loadpath := [];
     collect_garbage ("ProtoPure" :: (load_order ["ProtoPure"] []));
     reload_changed (load_order ["Pure", "CPure"] [])
  end;


(*Merge theories to build a base for a new theory.
  Base members are only loaded if they are missing.*)
fun mk_base bases child =
  let (*Show the cycle that would be created by add_child*)
      fun show_cycle base =
        let fun find_it result curr =
              let val tinfo = get_thyinfo curr
              in if base = curr then
                   error ("Cyclic dependency of theories: "
                          ^ child ^ "->" ^ base ^ result)
                 else if is_some tinfo then
                   let val {children, ...} = the tinfo
                   in seq (find_it ("->" ^ curr ^ result)) children
                   end
                 else ()
              end
        in find_it "" child end;

      (*Check if a cycle would be created by add_child*)
      fun find_cycle base =
        if base mem (get_descendants [child]) then show_cycle base
        else ();

      (*Add child to child list of base*)
      fun add_child base =
        let val tinfo =
              case Symtab.lookup (!loaded_thys, base) of
                  Some ({path, children, parents, thy_time, ml_time,
                           theory}) =>
                    {path = path,
                             children = child ins children, parents = parents,
                             thy_time = thy_time, ml_time = ml_time,
                             theory = theory}
                | None => {path = "", children = [child], parents = [],
                                   thy_time = None, ml_time = None,
                                   theory = None};
        in loaded_thys := Symtab.update ((base, tinfo), !loaded_thys) end;

      (*Load a base theory if not already done
        and no cycle would be created *)
      fun load base =
          let val thy_loaded = already_loaded base
                                       (*test this before child is added *)
          in
            if child = base then
                error ("Cyclic dependency of theories: " ^ child
                       ^ "->" ^ child)
            else
              (find_cycle base;
               add_child base;
               if thy_loaded then ()
               else (writeln ("Autoloading theory " ^ quote base
                              ^ " (required by " ^ quote child ^ ")");
                     use_thy1 true base)
              )
          end;

      (*Load all needed files and make a list of all real theories *)
      fun load_base (Thy b :: bs) =
           (load b;
            b :: load_base bs)
        | load_base (File b :: bs) =
           (load b;
            load_base bs)                    (*don't add it to mergelist *)
        | load_base [] = [];

      val dummy = unlink_thy child;
      val mergelist = load_base bases;

      val base_thy =
       (writeln ("Loading theory " ^ quote child);
         if null mergelist then ProtoPure.thy
         else Theory.prep_ext_merge (map theory_of mergelist));

      val dummy =
        let val tinfo = case Symtab.lookup (!loaded_thys, child) of
              Some ({path, children, parents = _, thy_time, ml_time, theory}) =>
                 {path = path, children = children, parents = mergelist,
                   thy_time = thy_time, ml_time = ml_time, theory = theory}
             | None => sys_error ("set_parents: theory " ^ child ^ " not found");
        in loaded_thys := Symtab.update ((child, tinfo), !loaded_thys) end;

 in
    cur_thyname := child;
    base_thy
 end;


(*Temporarily enter a directory and load its ROOT.ML file;
  also do some work for HTML and graph generation*)
local

  fun gen_use_dir use_cmd dirname =
    let val old_dir = OS.FileSys.getDir ();
    in OS.FileSys.chDir dirname;
       if !make_html then init_html() else ();
       if !make_graph then init_graph dirname else ();
       use_cmd "ROOT.ML";
       finish_html();
       OS.FileSys.chDir old_dir
    end;

in

  val use_dir = gen_use_dir Use.use;
  val exit_use_dir = gen_use_dir Use.exit_use;

end

end;
