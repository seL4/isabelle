(*  Title:      HOLCF/IOA/ABP/Check.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1994  TU Muenchen

The Model Checker
*)

 
(* ----------------------------------------------------------------
       P r o t o t y p e   M o d e l   C h e c k e r 
   ----------------------------------------------------------------*)

fun check(extacts,intacts,string_of_a,startsI,string_of_s,
          nexts,hom,transA,startsS) =
  let fun check_s(s,unchecked,checked) =
        let fun check_sa(unchecked,a) =
              let fun check_sas(unchecked,t) =
                    (if a mem extacts then
                          (if transA(hom s,a,hom t) then ( )
                           else (writeln("Error: Mapping of Externals!");
                                 string_of_s s; writeln"";
                                 string_of_a a; writeln"";
                                 string_of_s t;writeln"";writeln"" ))
                     else (if hom(s)=hom(t) then ( )
                           else (writeln("Error: Mapping of Internals!");
                                 string_of_s s; writeln"";
                                 string_of_a a; writeln"";
                                 string_of_s t;writeln"";writeln"" ));
                     if t mem checked then unchecked else t ins unchecked)
              in foldl check_sas (unchecked,nexts s a) end;
              val unchecked' = foldl check_sa (unchecked,extacts @ intacts)
        in    (if s mem startsI then 
                    (if hom(s) mem startsS then ()
                     else writeln("Error: At start states!"))
               else ();  
               checks(unchecked',s::checked)) end
      and checks([],_) = ()
        | checks(s::unchecked,checked) = check_s(s,unchecked,checked)
  in checks(startsI,[]) end;


(* ------------------------------------------------------
                 A B P     E x a m p l e
   -------------------------------------------------------*)

datatype msg = m | n | l;
datatype act = Next | S_msg of msg | R_msg of msg
                    | S_pkt of bool * msg | R_pkt of bool * msg
                    | S_ack of bool | R_ack of bool;

(* -------------------- Transition relation of Specification -----------*)

fun transA((u,s),a,(v,t)) = 
    (case a of 
       Next       => v andalso t = s |                         
       S_msg(q)   => u andalso not(v) andalso t = s@[q]   |    
       R_msg(q)   => u = v andalso s = (q::t)  |                    
       S_pkt(b,q) => false |                    
       R_pkt(b,q) => false |                    
       S_ack(b)   => false |                      
       R_ack(b)   => false);


(* ---------------------- Abstraction function --------------------------*)

fun hom((env,p,a,q,b,_,_)) = (env,q@(if (a=b) then tl(p) else p));


(* --------------------- Transition relation of Implementation ----------*)

fun nexts (s as (env,p,a,q,b,ch1,ch2)) action =
    (case action of
       Next       => if p=[] then [(true,p,a,q,b,ch1,ch2)] else [] |                         
       S_msg(mornorl)   => if env then [(false,p@[mornorl],a,q,b,ch1,ch2)] else [] |     
       R_msg(mornorl)   => if (q<>[] andalso mornorl=hd(q)) 
                        then [(env,p,a,tl(q),b,ch1,ch2)]
                        else [] |                    
       S_pkt(h,mornorl) => if (p<>[] andalso mornorl=hd(p) andalso h=a)
                        then (if (ch1<>[] andalso hd(rev(ch1))=(h,mornorl))
                              then [s]
                              else [s,(env,p,a,q,b,ch1@[(h,mornorl)],ch2)])
                        else [] |
       R_pkt(h,mornorl) => if (ch1<>[] andalso hd(ch1)=(h,mornorl))
                         then (if (h<>b andalso q=[])
                               then [(env,p,a,q@[mornorl],not(b),ch1,ch2),
                                     (env,p,a,q@[mornorl],not(b),tl(ch1),ch2)]
                               else [s,(env,p,a,q,b,tl(ch1),ch2)])
                          else [] | 
       S_ack(h)   => if (h=b)
                        then (if (ch2<>[] andalso h=hd(rev(ch2))) 
                              then [s]
                              else [s,(env,p,a,q,b,ch1,ch2@[h])])
                        else []  |                      
       R_ack(h)   => if (ch2<>[] andalso hd(ch2)=h)
                        then (if h=a
                              then [(env,tl(p),not(a),q,b,ch1,ch2),
                                    (env,tl(p),not(a),q,b,ch1,tl(ch2))]
                              else [s,(env,p,a,q,b,ch1,tl(ch2))]) 
                         else [])


val extactions = [Next,S_msg(m),R_msg(m),S_msg(n),R_msg(n),S_msg(l),R_msg(l)];
val intactions = [S_pkt(true,m),R_pkt(true,m),S_ack(true),R_ack(true),
                  S_pkt(false,m),R_pkt(false,m),S_ack(false),R_ack(false),
                  S_pkt(true,n),R_pkt(true,n),S_pkt(true,l),R_pkt(true,l),
               S_pkt(false,n),R_pkt(false,n),S_pkt(false,l),R_pkt(false,l)];


(* ------------------------------------
           Input / Output utilities 
   ------------------------------------*)

fun print_list (lpar, rpar, pre: 'a -> unit) (lll : 'a list) =
  let fun prec x = (prs ","; pre x)
  in
    (case lll of
      [] => (prs lpar; prs rpar)
    | x::lll => (prs lpar; pre x; seq prec lll; prs rpar))
   end;

fun pr_bool true = output(std_out,"true")
|   pr_bool false = output(std_out,"false");

fun pr_msg m = output(std_out,"m")
|   pr_msg n = output(std_out,"n")
|   pr_msg l = output(std_out,"l");

fun pr_act a = output(std_out, case a of
      Next => "Next"|                         
      S_msg(ma) => "S_msg(ma)"  |
      R_msg(ma) => "R_msg(ma)"  |
      S_pkt(b,ma) => "S_pkt(b,ma)" |                    
      R_pkt(b,ma) => "R_pkt(b,ma)" |                    
      S_ack(b)   => "S_ack(b)" |                      
      R_ack(b)   => "R_ack(b)");

fun pr_pkt (b,ma) = (prs "<"; pr_bool b;prs ", "; pr_msg ma; prs ">");

val pr_bool_list  = print_list("[","]",pr_bool);
val pr_msg_list   = print_list("[","]",pr_msg);
val pr_pkt_list   = print_list("[","]",pr_pkt);

fun pr_tuple (env,p,a,q,b,ch1,ch2) = 
        (prs "{"; pr_bool env; prs ", "; pr_msg_list p;  prs ", ";
         pr_bool a;  prs ", "; pr_msg_list q; prs ", ";
         pr_bool b;  prs ", "; pr_pkt_list ch1;  prs ", ";
         pr_bool_list ch2; prs "}");



(* ---------------------------------
         Main function call
   ---------------------------------*)

(*
check(extactions,intactions,pr_act, [(true,[],true,[],false,[],[])], 
      pr_tuple, nexts, hom, transA, [(true,[])]);
*)





(*
           Little test example

datatype act = A;
fun transA(s,a,t) = (not(s)=t);
fun hom(i) = i mod 2 = 0;
fun nexts s A = [(s+1) mod 4];
check([A],[],K"A", [0], string_of_int, nexts, hom, transA, [true]);

fun nexts s A = [(s+1) mod 5];

*)
