(*  Title:      Pure/Thy/thy_read.ML
    ID:         $Id$
    Author:     Sonia Mahjoub / Tobias Nipkow / L C Paulson
    Copyright   1993  TU Muenchen

Reading and writing the theory definition files.

For theory XXX, the  input file is called XXX.thy
                the output file is called .XXX.thy.ML
                and it then tries to read XXX.ML
*)

datatype thy_info = ThyInfo of {name: string, path: string,
                                children: string list,
                                thy_info: string option, ml_info: string option,
                                theory: Thm.theory option};

signature THY_READ =
sig
  datatype basetype = Thy  of string
                    | File of string

  val loaded_thys    : thy_info list ref
  val loadpath       : string list ref
  val delete_tmpfiles: bool ref

  val use_thy        : string -> unit
  val update         : unit -> unit
  val time_use_thy   : string -> unit
  val unlink_thy     : string -> unit
  val base_on        : basetype list -> string -> Thm.theory
  val store_theory   : string -> Thm.theory -> unit
end;


functor ThyReadFun(structure ThyParse: THY_PARSE): THY_READ =
struct

datatype basetype = Thy  of string
                  | File of string;

val loaded_thys = ref [ThyInfo {name = "Pure", path = "", children = [], 
                                thy_info = Some "", ml_info = Some "", 
                                theory = Some Thm.pure_thy}];

val loadpath = ref ["."];           (*default search path for theory files *)

val delete_tmpfiles = ref true;         (*remove temporary files after use *)

(*Make name of the output ML file for a theory *)
fun out_name thy = "." ^ thy ^ ".thy.ML";

(*Read a file specified by thy_file containing theory thy *)
fun read_thy thy thy_file =
  let 
    open ThyParse;
    val instream  = open_in thy_file;
    val outstream = open_out (out_name thy);
  in  
    output (outstream, parse_thy pure_syntax (input (instream, 999999)));
    close_out outstream;
    close_in instream
  end;

fun file_exists file =
  let val instream = open_in file in close_in instream; true end
    handle Io _ => false;

(*Get thy_info for a loaded theory *)
fun get_thyinfo thy =
  let fun do_search (t :: loaded : thy_info list) =
            let val ThyInfo {name, ...} = t
            in if name = thy then Some t else do_search loaded end
        | do_search [] = None
  in do_search (!loaded_thys) end;

(*Replace an item by the result of make_change *)
fun change_thyinfo make_change =
  let fun search (t :: loaded) =
            let val ThyInfo {name, path, children, thy_info, ml_info,
                             theory} = t
                val (new_t, continue) = make_change name path children thy_info
                                                    ml_info theory
            in if continue then            
                 new_t :: (search loaded)
               else
                 new_t :: loaded
            end
        | search [] = []
  in loaded_thys := search (!loaded_thys) end;

(*Check if a theory was already loaded *)
fun already_loaded thy =
  let val t = get_thyinfo thy
  in if is_none t then false
     else let val ThyInfo {thy_info, ml_info, ...} = the t
          in if is_none thy_info orelse is_none ml_info then false 
             else true end
  end;

(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML *)
fun thy_unchanged thy thy_file ml_file = 
  let val t = get_thyinfo thy
  in if is_some t then
       let val ThyInfo {thy_info, ml_info, ...} = the t
           val tn = is_none thy_info;
           val mn = is_none ml_info
       in if not tn andalso not mn then
              ((file_info thy_file = the thy_info), 
               (file_info ml_file = the ml_info))
          else if not tn andalso mn then (true, false)
          else (false, false)
       end
     else (false, false)
  end;

exception FILE_NOT_FOUND;   (*raised by find_file *)

(*Find a file using a list of paths if no absolute or relative path is
  specified.*)
fun find_file "" name =
      let fun find_it (curr :: paths) =
                if file_exists (tack_on curr name) then
                    tack_on curr name
                else 
                    find_it paths
           | find_it [] = ""
      in find_it (!loadpath) end
  | find_file path name =
      if file_exists (tack_on path name) then tack_on path name
                                         else "";

(*Get absolute pathnames for a new or already loaded theory *)
fun get_filenames path name =
  let fun make_absolute file =
        if file = "" then "" else 
            if hd (explode file) = "/" then file else tack_on (pwd ()) file;

      fun new_filename () =
        let val found = find_file path (name ^ ".thy")
                        handle FILE_NOT_FOUND => "";
            val thy_file = make_absolute found;
            val (thy_path, _) = split_filename thy_file;
            val found = find_file path (name ^ ".ML");
            val ml_file = if thy_file = "" then make_absolute found
                          else if file_exists (tack_on thy_path (name ^ ".ML"))
                          then tack_on thy_path (name ^ ".ML")
                          else "";
            val searched_dirs = if path = "" then (!loadpath) else [path]
        in if thy_file = "" andalso ml_file = "" then
             error ("Could not find file \"" ^ name ^ ".thy\" or \""
                    ^ name ^ ".ML\" for theory \"" ^ name ^ "\"\n"
                    ^ "in the following directories: \"" ^
                    (space_implode "\", \"" searched_dirs) ^ "\"")
           else ();
           (thy_file, ml_file) 
        end;

      val thy = get_thyinfo name
  in if is_some thy andalso path = "" then
       let val ThyInfo {path = abs_path, ...} = the thy;
           val (thy_file, ml_file) = if abs_path = "" then new_filename ()
                                     else (find_file abs_path (name ^ ".thy"),
                                           find_file abs_path (name ^ ".ML"))
       in if thy_file = "" andalso ml_file = "" then
            (writeln ("Warning: File \"" ^ (tack_on path name)
                      ^ ".thy\"\ncontaining theory \"" ^ name
                      ^ "\" no longer exists.");
             new_filename ()
            )
          else (thy_file, ml_file)
       end
     else new_filename ()
  end;

(*Remove theory from all child lists in loaded_thys *)
fun unlink_thy thy =
  let fun remove name path children thy_info ml_info theory =
            (ThyInfo {name = name, path = path, children = children \ thy, 
                      thy_info = thy_info, ml_info = ml_info,
                      theory = theory}, true)
  in change_thyinfo remove end;

(*Remove a theory from loaded_thys *)
fun remove_thy thy =
  let fun remove (t :: ts) =
            let val ThyInfo {name, ...} = t
            in if name = thy then ts
                             else t :: (remove ts)
            end
        | remove [] = []
  in loaded_thys := remove (!loaded_thys) end;

(*Change thy_info and ml_info for an existent item *)
fun set_info thy_new ml_new thy =
  let fun change name path children thy_info ml_info theory =
        if name = thy then
            (ThyInfo {name = name, path = path, children = children,
                      thy_info = Some thy_new, ml_info = Some ml_new,
                      theory = theory}, false)
        else
            (ThyInfo {name = name, path = path, children = children,
                      thy_info = thy_info, ml_info = ml_info,
                      theory = theory}, true)
  in change_thyinfo change end;

(*Mark theory as changed since last read if it has been completly read *)
fun mark_outdated thy =
  if already_loaded thy then set_info "" "" thy
                        else ();

(*Read .thy and .ML files that haven't been read yet or have changed since 
  they were last read;
  loaded_thys is a thy_info list ref containing all theories that have 
  completly been read by this and preceeding use_thy calls.
  If a theory changed since its last use its children are marked as changed *)
fun use_thy name =
    let val (path, thy_name) = split_filename name;
        val (thy_file, ml_file) = get_filenames path thy_name;
        val (abs_path, _) = if thy_file = "" then split_filename ml_file
                            else split_filename thy_file;
        val (thy_uptodate, ml_uptodate) = thy_unchanged thy_name 
                                                        thy_file ml_file;

         (*Set absolute path for loaded theory *)
         fun set_path () =
           let fun change name path children thy_info ml_info theory =
                 if name = thy_name then            
                   (ThyInfo {name = name, path = abs_path, children = children,
                             thy_info = thy_info, ml_info = ml_info,
                             theory = theory}, false)
                 else
                   (ThyInfo {name = name, path = path, children = children,
                             thy_info = thy_info, ml_info = ml_info,
                             theory = theory}, true)
           in change_thyinfo change end;

         (*Mark all direct descendants of a theory as changed *)
         fun mark_children thy =
           let val ThyInfo {children, ...} = the (get_thyinfo thy)
               val loaded = filter already_loaded children
           in if loaded <> [] then
                  (writeln ("The following children of theory " ^ (quote thy)
                            ^ " are now out-of-date: "
                            ^ (quote (space_implode "\",\"" loaded)));
                   seq mark_outdated loaded
                  )
              else ()
           end

    in if thy_uptodate andalso ml_uptodate then ()
       else
       (
         if thy_uptodate orelse thy_file = "" then ()
         else (writeln ("Reading \"" ^ name ^ ".thy\"");
               read_thy thy_name thy_file;
               use (out_name thy_name)
              );

         if ml_file = "" then () 
         else (writeln ("Reading \"" ^ name ^ ".ML\"");
               use ml_file);

         use_string ["store_theory " ^ quote thy_name ^ " " ^ thy_name 
                     ^ ".thy;"];

         (*Now set the correct info*)
         set_info (file_info thy_file) (file_info ml_file) thy_name;
         set_path ();

         (*Mark theories that have to be reloaded*)
         mark_children thy_name;

         (*Remove temporary files*)
         if not (!delete_tmpfiles) orelse (thy_file = "") orelse thy_uptodate 
           then ()
         else delete_file (out_name thy_name)
        )
    end;

fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");  
    use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****"))
   );

(*Load all thy or ML files that have been changed and also
  all theories that depend on them *)
fun update () =
  let (*List theories in the order they have to be loaded *)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level (t :: ts) =
                      let val thy = get_thyinfo t
                      in if is_some thy then
                             let val ThyInfo {children, ...} = the thy
                             in children union (next_level ts)
                             end
                         else next_level ts
                      end
                  | next_level [] = [];
                  
                val children = next_level thys
            in load_order children ((result \\ children) @ children) end;

      fun reload_changed (t :: ts) =
            let val thy = get_thyinfo t;

                fun abspath () =
                  if is_some thy then
                    let val ThyInfo {path, ...} = the thy in path end
                  else "";

                val (thy_file, ml_file) = get_filenames (abspath ()) t;
                val (thy_uptodate, ml_uptodate) =
                        thy_unchanged t thy_file ml_file;
            in if thy_uptodate andalso ml_uptodate then ()
                                                   else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ();

     (*Remove all theories that are no descendants of Pure.
       If there are still children in the deleted theory's list
       schedule them for reloading *)
     fun collect_garbage not_garbage =
       let fun collect (t :: ts) =
                 let val ThyInfo {name, children, ...} = t
                 in if name mem not_garbage then collect ts
                    else (writeln("Theory \"" ^ name 
                           ^ "\" is no longer linked with Pure - removing it.");
                          remove_thy name;
                          seq mark_outdated children
                         )
                 end
             | collect [] = ()

       in collect (!loaded_thys) end

  in collect_garbage ("Pure" :: (load_order ["Pure"] []));
     reload_changed (load_order ["Pure"] [])
  end;

(*Merge theories to build a base for a new theory.
  Base members are only loaded if they are missing. *)
fun base_on bases child =
      let (*List all descendants of a theory list *)
          fun list_descendants (t :: ts) =
                let val tinfo = get_thyinfo t
                in if is_some tinfo then
                     let val ThyInfo {children, ...} = the tinfo
                     in children union (list_descendants (ts union children))
                     end
                   else []
                end
            | list_descendants [] = [];

          (*Show the cycle that would be created by add_child *)
          fun show_cycle base =
            let fun find_it result curr =
                  let val tinfo = get_thyinfo curr
                  in if base = curr then 
                       error ("Cyclic dependency of theories: "
                              ^ child ^ "->" ^ base ^ result)
                     else if is_some tinfo then
                       let val ThyInfo {children, ...} = the tinfo
                       in seq (find_it ("->" ^ curr ^ result)) children
                       end
                     else ()
                  end
            in find_it "" child end;
        
          (*Check if a cycle will be created by add_child *)
          fun find_cycle base =
            if base mem (list_descendants [child]) then show_cycle base
            else ();
                   
          (*Add child to child list of base *)
          fun add_child base =
            let fun add (t :: loaded) =
                      let val ThyInfo {name, path, children,
                                       thy_info, ml_info, theory} = t
                      in if name = base then
                           ThyInfo {name = name, path = path,
                                    children = child ins children,
                                    thy_info = thy_info, ml_info = ml_info,
                                    theory = theory} :: loaded
                         else
                           t :: (add loaded)
                      end
                  | add [] =
                      [ThyInfo {name = base, path = "", children = [child], 
                                thy_info = None, ml_info = None, theory = None}]
            in loaded_thys := add (!loaded_thys) end;       

          (*Load a base theory if not already done
            and no cycle would be created *)
          fun load base =
              let val thy_present = already_loaded base
                                            (*test this before child is added *)
              in
                if child = base then
                    error ("Cyclic dependency of theories: " ^ child
                           ^ "->" ^ child)
                else 
                  (find_cycle base;
                   add_child base;
                   if thy_present then ()
                   else (writeln ("Autoloading theory " ^ (quote base)
                                  ^ " (used by " ^ (quote child) ^ ")");
                         use_thy base)
                  )
              end; 

          (*Load all needed files and make a list of all real theories *)
          fun load_base (Thy b :: bs) =
               (load b;
                b :: (load_base bs))
            | load_base (File b :: bs) =
               (load b;
                load_base bs)    (*don't add it to merge_theories' parameter *)
            | load_base [] = [];

          (*Get theory object for a loaded theory *)
          fun get_theory name =
            let val ThyInfo {theory, ...} = the (get_thyinfo name)
            in the theory end;

          val mergelist = (unlink_thy child;
                           load_base bases);
          val (t :: ts) = if mergelist = [] then ["Pure"] else mergelist
                                               (*we have to return something *)
     in writeln ("Loading theory " ^ (quote child));
        foldl Thm.merge_theories (get_theory t, map get_theory ts) end;

(*Change theory object for an existent item of loaded_thys 
  or create a new item *)
fun store_theory thy_name thy =
  let fun make_change (t :: loaded) =
            let val ThyInfo {name, path, children, thy_info, ml_info, ...} = t
            in if name = thy_name then            
                    ThyInfo {name = name, path = path, children = children,
                             thy_info = thy_info, ml_info = ml_info,
                             theory = Some thy} :: loaded
               else
                    t :: (make_change loaded)
            end
        | make_change [] =
            [ThyInfo {name = thy_name, path = "", children = [],
                      thy_info = Some "", ml_info = Some "",
                      theory = Some thy}]
  in loaded_thys := make_change (!loaded_thys) end;

end;

