(*Hash tables. Taken from SML/NJ version 110.57.
  Copyright (c) 1989-2002 by Lucent Technologies*)
signature HASHTABLE =
sig
   type ('a,'b) table

   val create : { hash : 'a -> word, 
                  ==   : 'a * 'a -> bool,
                  exn  : exn,
                  size : int 
                } -> ('a,'b) table 

   val size         : ('a,'b) table -> int
   val clear        : ('a,'b) table -> unit
   val insert       : ('a,'b) table -> 'a * 'b -> unit
   val remove       : ('a,'b) table -> 'a -> unit
   val lookup       : ('a,'b) table -> 'a -> 'b 
   val copy         : ('a,'b) table -> ('a,'b) table
   val app          : ('a * 'b -> unit) -> ('a,'b) table -> unit
   val map          : ('a * 'b -> 'c) -> ('a,'b) table -> 'c list
   val fold         : ('a * 'b * 'c -> 'c) -> 'c -> ('a,'b) table -> 'c

   (*Additions due to L. C. Paulson and Jia Meng*)
   val hash_word : word * word -> word
   val hash_char : Char.char * word -> word
   val hash_vector : word Vector.vector * word -> word
   val hash_string : string * word -> word
   val hash_strings : string list * word -> word
end

structure Hashtable :> HASHTABLE =
struct

   structure A = Array

   type ('a,'b) table = ('a -> word) * 
                        ('a * 'a -> bool) *
                        exn *
                        ('a * 'b) list A.array ref * 
                        int ref

   infix ==

   fun create{hash,==,exn,size} = (hash,op==,exn,ref(A.array(size,[])),ref 0)
   fun copy(hash,op==,exn,ref a,ref c) = 
         (hash,op==,exn,ref(A.tabulate(A.length a,fn i => A.sub(a,i))), ref c)
   fun size (_,_,_,_,ref n) = n
   fun clear (_,_,_,ref a,c) =
       let fun f ~1 = ()
             | f i  = (A.update(a,i,[]); f(i-1))
       in  f(A.length a - 1); c := 0 end
   fun insert (hash,op==,exn,A as ref a,c) (k,v) =
   let val N  = A.length a
       val h  = Word.toIntX(hash k) mod N
       val es = A.sub(a,h)
       fun insrt ([],es') = (A.update(a,h,(k,v)::es'); 
			     c := !c + 1;
			     if !c >= N then grow(hash,A,N) else ())
         | insrt ((e as (k',_))::es,es') = 
            if k == k' then A.update(a,h,(k,v)::es'@es) 
            else insrt(es,e::es')
   in  insrt (es,[])
   end

   and grow(hash,A as ref a,N) =
       let val M = N + N
           val M = if M < 13 then 13 else M
           val a' = A.array(M,[])
           fun insrt (k,v) = let val h = Word.toIntX(hash k) mod M
                             in  A.update(a',h,(k,v)::A.sub(a',h)) end
       in  A.app (fn es => app insrt es) a;
           A := a'
       end

   fun remove (hash,op==,exn,ref a,c) k =
   let val N  = A.length a
       val h  = Word.toIntX(hash k) mod N
       val es = A.sub(a,h)
       fun del ([],es') = ()
         | del ((e as (k',_))::es,es') = 
            if k == k' then (A.update(a,h,es'@es); c := !c - 1)
            else del(es,e::es')
   in  del (es,[])
   end
 
   fun lookup(hash,op==,exn,ref a,_) k =
   let val N  = A.length a
       val h  = Word.toIntX(hash k) mod N
       fun find [] = raise exn
         | find ((k',v)::es) = if k == k' then v else find es
   in  find(A.sub(a,h))
   end

   fun app f (_,_,_,ref A,_) = A.app (List.app f) A

   fun map f (_,_,_,ref A,_) =
   let fun fl([],x) = x
         | fl((k,v)::es,x) = f(k,v)::fl(es,x)
   in  A.foldr fl [] A end

   fun fold f x (_,_,_,ref A,_) = 
   let fun fl([],x) = x
         | fl((k,v)::es,x) = f(k,v,fl(es,x))
   in  A.foldr fl x A end


   (*Additions due to L. C. Paulson and Jia Meng*)

   val myw = ref 0w0;
   val () = myw := 0wx70000000;  (*workaround for Poly/ML bug*)

   local open Word
	 infix << >>
   in
   fun hash_word (u,w) =
     let val w' = (w << 0w4) + u
	 val g = Word.andb(w', !myw)    (*I hope this hex constant is correct!*)
     in  
	 if g = 0w0 then Word.xorb(w', Word.xorb(g, g >> 0w24))
	 else w'
     end;
   end;
   
   fun hash_char (c,w) = hash_word (Word.fromInt (Char.ord c), w);
   
   fun hash_vector (v,w) = Vector.foldl hash_word w v;
   
   fun hash_string (s:string, w) = CharVector.foldl hash_char w s;
   
   fun hash_strings (ss, w) = List.foldl hash_string w ss;

end

