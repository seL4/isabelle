(*  Title:      HOL/IOA/ABP/Check.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Olaf Mueller
    Copyright   1995  TU Muenchen

Simple ModelChecker prototype checking Spec against 
the finite version of the ABP-protocol.
*)


(* model checker function prototype *)

fun check(extacts,intacts,string_of_a,startsI,string_of_s,
          nexts,hom,transA,startsS) =
  let fun check_s(s,unchecked,checked) =
        let fun check_sa(unchecked,a) =
              let fun check_sas(unchecked,t) =
                    (if a mem extacts then
                          (if transA(hom s,a,hom t) then ()
                           else (writeln("Error: Mapping of Externals!");
                                 string_of_s s; writeln"";
                                 string_of_a a; writeln"";
                                 string_of_s t;writeln"";writeln""))
                     else (if hom(s)=hom(t) then ()
                           else (writeln("Error: Mapping of Internals!");
                                 string_of_s s;writeln"";
                                 string_of_a a;writeln"";
                                 string_of_s t;writeln"";writeln""));
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


(* datatypes for ABP example *)

datatype msg = m;
datatype act = Next | S_msg of msg | R_msg of msg
                    | S_pkt of bool * msg | R_pkt of bool * msg
                    | S_ack of bool | R_ack of bool;

fun transA((u,s),a,(v,t)) = 
    (case a of 
       Next       => v andalso t = s |                         
       S_msg(m)   => u andalso not(v) andalso t = s@[m]   |    
       R_msg(m)   => u = v andalso s = (m::t)  |                    
       S_pkt(b,m) => false |                    
       R_pkt(b,m) => false |                    
       S_ack(b)   => false |                      
       R_ack(b)   => false);

fun hom((env,p,a,q,b,_,_)) = (env,q@(if (a=b) then tl(p) else p));

fun nexts (s as (env,p,a,q,b,ch1,ch2)) action =
    (case action of
       Next       => if p=[] then [(true,p,a,q,b,ch1,ch2)] else [] |                         
       S_msg(m)   => if env then [(false,p@[m],a,q,b,ch1,ch2)] else [] |     
       R_msg(m)   => if (q<>[] andalso m=hd(q)) 
                        then [(env,p,a,tl(q),b,ch1,ch2)]
                        else [] |                    
       S_pkt(h,m) => if (p<>[] andalso m=hd(p) andalso h=a)
                        then (if (ch1<>[] andalso hd(rev(ch1))=(h,m))
                              then [s]
                              else [s,(env,p,a,q,b,ch1@[(h,m)],ch2)])
                        else [] |
       R_pkt(h,m) => if (ch1<>[] andalso hd(ch1)=(h,m))
                         then (if (h<>b andalso q=[])
                               then [(env,p,a,q@[m],not(b),ch1,ch2),
                                     (env,p,a,q@[m],not(b),tl(ch1),ch2)]
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


val extactions = [Next,S_msg(m),R_msg(m)];
val intactions = [S_pkt(true,m),R_pkt(true,m),S_ack(true),R_ack(true),
                  S_pkt(false,m),R_pkt(false,m),S_ack(false),R_ack(false)];
 

(* Input / Output auxiliary functions *)

fun print_list (lpar, rpar, pre: 'a -> unit) (l : 'a list) =
  let fun prec x = (prs ","; pre x)
  in
    (case l of
      [] => (prs lpar; prs rpar)
    | x::l => (prs lpar; pre x; seq prec l; prs rpar))
   end;

fun pr_bool true = output(std_out,"true")
|   pr_bool false = output(std_out,"false");

fun pr_msg m = output(std_out,"m");

fun pr_act a = output(std_out, case a of
      Next => "Next"|                         
      S_msg(m) => "S_msg(m)"  |
      R_msg(m) => "R_msg(m)"  |
      S_pkt(b,m) => "S_pkt(b,m)" |                    
      R_pkt(b,m) => "R_pkt(b,m)" |                    
      S_ack(b)   => "S_ack(b)" |                      
      R_ack(b)   => "R_ack(b)");

fun pr_pkt (b,m) = (prs "<"; pr_bool b;prs ", "; pr_msg m; prs ">");

val pr_bool_list  = print_list("[","]",pr_bool);
val pr_msg_list   = print_list("[","]",pr_msg);
val pr_pkt_list   = print_list("[","]",pr_pkt);

fun pr_tuple (env,p,a,q,b,ch1,ch2) = 
        (prs "{"; pr_bool env; prs ", "; pr_msg_list p;  prs ", ";
         pr_bool a;  prs ", "; pr_msg_list q; prs ", ";
         pr_bool b;  prs ", "; pr_pkt_list ch1;  prs ", ";
         pr_bool_list ch2; prs "}");

(* ----------------------------*)
(* main check function call    *)
(* ----------------------------*)

check(extactions,intactions,pr_act, [(true,[],true,[],false,[],[])], 
      pr_tuple, nexts, hom, transA, [(true,[])]);


