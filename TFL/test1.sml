(*---------------------------------------------------------------------------
 * Pattern matching extensions.
 *---------------------------------------------------------------------------*)

fun cread thy s = read_cterm (sign_of thy) (s, (TVar(("DUMMY",0),[])));
fun read thy = term_of o cread thy;
fun Term s = read WF1.thy s;

fun Rfunc thy R eqs =
   let val {induction,rules,theory,tcs} = 
              timeit(fn () => Tfl.Rfunction thy (read thy R) (read thy eqs))
   in {induction=induction, rules=rules, theory=theory, 
       tcs = map (cterm_of (sign_of theory)) tcs}
   end;

fun def tm = timeit (fn () => Tfl.function WF1.thy (Term tm));




(*---------------------------------------------------------------------------
 * Normal patterns
 *---------------------------------------------------------------------------*)
def "(f(x,y) = x+y)";

def "(f1 0 = 1) & (f1 (Suc n) = 2)";

(*---------------------------------------------------------------------------
 * Omitted patterns
 *---------------------------------------------------------------------------*)
def "(f2 0 = 1)";

def "(f3 (h#t) = h)";

def "(f4 [a,b] = a)  &  (f4 [b] = b)";

def "(f5 (0,0) = 0)";

def "(f6 (0,0) = 0) & (f6 (0,Suc x) = x) & (f6 (Suc x, y) = y+x)"; 

def "(f7 (Suc 0, h#t) = 1) & (f7 (Suc(Suc n),h1#h2#t) = h1)";

def "(f8 (Suc(Suc n),h1#h2#t) = h1)";


(*---------------------------------------------------------------------------
 * Overlapping patterns 
 *---------------------------------------------------------------------------*)
def "(f9 (h1#h2#t) = t) & (f9 x = x)";

def "(g (x,0) = 1) & (g (0,x) = 2)"; 

def "(g1 (0,x) = x) & (g1 (x,0) = x)"; 

def "(g2 ([], a#b#x) = 1) & (g2 (a#b#x, y) = 2) & (g2 (z, a#y) = a)";	

def "(g3 (x,y,0) = 1) & (g3 (x,0,y) = 2) & (g3 (0,x,y) = x)";

def "(g4 (0,y,z) = 1) & (g4 (x,0,z) = 2) & (g4 (x,y,0) = x)";

def "(g5(0,x,y,z) = 1) & (g5(w,0,y,z) = 2) & (g5(w,x,0,z) = z) & \
  \  (g5(w,x,y,0) = y)";

def "(g6 (0,w,x,y,z) = 1) & (g6 (v,0,x,y,z) = 2) & (g6 (v,w,0,y,z) = z) & \
  \  (g6 (v,w,x,0,z) = z) & (g6 (v,w,x,y,0) = 0)";

def "(g7 [x, 0] = x) & (g7 [Suc v] = 1) & (g7 z = 2)";

def "(g8 (h1#h2#h3#h4#h5#h6) = [h1,h2,h3,h4,h5]# g8 h6) & (g8 x = [x])";

(* Normal *)
def "(g9 (Suc(Suc x)) = 1) & (g9 (Suc x) = 2) & (g9 0 = 0)";

(*---------------------------------------------------------------------------
 * Inaccessible patterns
 *---------------------------------------------------------------------------*)
def "(h x = 1) & (h x = 2)";

def "(h1 (x,0) = 1) & (h1 (x,Suc y) = 2) & \
  \  (h1 (x,y) = x) & (h1 (x,y) = y)";

def "(h2 (x,0) = 1) & (h2 (0,x) = 2) & \
  \  (h2 (0,0) = 0) & (h2 (x,y) = x)"; 
