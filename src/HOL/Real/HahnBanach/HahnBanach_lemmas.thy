
theory HahnBanach_lemmas = FunctionOrder + NormedSpace + Zorn_Lemma + FunctionNorm + RComplete:;


theorems [dest!!] = subsetD;
theorems [intro!!] = subspace_subset; 

lemma rabs_ineq: "[| is_subspace H E; is_vectorspace E; is_quasinorm E p; is_linearform H h |] \
 \ ==>  (ALL x:H. rabs (h x) <= p x)  = ( ALL x:H. h x <= p x)" (concl is "?L = ?R");
proof -;
  assume "is_subspace H E" "is_vectorspace E" "is_quasinorm E p" "is_linearform H h";
  have H: "is_vectorspace H"; by (rule subspace_vs);
  show ?thesis;
  proof; 
    assume l: ?L;
    then; show ?R;
    proof (intro ballI); 
      fix x; assume "x:H";
      have "h x <= rabs (h x)"; by (rule rabs_ge_self);
      also; have "rabs (h x) <= p x"; by fast;
      finally; show "h x <= p x"; .;
    qed;
  next;
    assume r: ?R;
    then; show ?L;
    proof (intro ballI);
      fix x; assume "x:H";
      have lem: "!! r x. [| - r <= x; x <= r |] ==> rabs x <= r";
        by (rule conjI [RS rabs_interval_iff_1 [RS iffD2]]); (* arith *)
      show "rabs (h x) <= p x"; 
      proof (rule lem);  
	show "- p x <= h x"; 
	proof (rule minus_le);
	  from H; have "- h x = h ([-] x)"; by (rule linearform_neg_linear [RS sym]);
	  also; from r; have "... <= p ([-] x)"; 
	  proof -; 
	    from H; have "[-] x : H"; by asm_simp;
            with r; show ?thesis; ..;
          qed;
	  also; have "... = p x"; 
          proof (rule quasinorm_minus);
            show "x:E";
            proof (rule subsetD);
              show "H <= E"; ..; 
            qed;
          qed;
	  finally; show "- h x <= p x"; .; 
	qed;
	from r; show "h x <= p x"; ..; 
      qed;
    qed;
  qed;
qed;  


lemma  some_H'h't:
  "[| M = norm_prev_extensions E p F f; c: chain M; graph H h = Union c; x:H|]
   ==> EX H' h' t. t : (graph H h) & t = (x, h x) & (graph H' h'):c & t:graph H' h' &
                       is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
                       (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)";
proof -;
  assume "M = norm_prev_extensions E p F f" and cM: "c: chain M" 
     and "graph H h = Union c" "x:H"; 

  let ?P = "%H h. is_linearform H h 
                    & is_subspace H E 
                    & is_subspace F H
                    & (graph F f <= graph H h)
                    & (ALL x:H. h x <= p x)";

  have "EX t : (graph H h). t = (x, h x)"; 
    by (rule graph_lemma1);
  thus ?thesis;
  proof (elim bexE); 
    fix t; assume "t : (graph H h)" and "t = (x, h x)";
    have ex1: "EX g:c. t:g";
      by (asm_simp only: Union_iff);
    thus ?thesis;
    proof (elim bexE);
      fix g; assume "g:c" "t:g";
      have gM: "g:M"; 
      proof -;
        from cM; have "c <= M"; by (rule chainD2);
        thus ?thesis; ..;
      qed;
      have "EX H' h'. graph H' h' = g & ?P H' h'"; 
      proof (rule norm_prev_extension_D);
        from gM; show "g: norm_prev_extensions E p F f"; by asm_simp;
      qed;
      thus ?thesis; by (elim exE conjE, intro exI conjI) (asm_simp+);
    qed;
  qed;
qed;
      

lemma some_H'h': "[| M = norm_prev_extensions E p F f; c: chain M; graph H h = Union c; x:H|] 
 ==> EX H' h'. x:H' & (graph H' h' <= graph H h) & 
               is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
               (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume "M = norm_prev_extensions E p F f" "c: chain M" "graph H h = Union c" "x:H"; 

  have "EX H' h' t. t : (graph H h) & t = (x, h x) & (graph H' h'):c & t:graph H' h'
                  & is_linearform H' h' & is_subspace H' E & is_subspace F H'
                  & (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)";
    by (rule some_H'h't);
 
  thus ?thesis; 
  proof (elim exE conjE, intro exI conjI);
    fix H' h' t; 
    assume "t : graph H h" "t = (x, h x)" "graph H' h' : c" "t : graph H' h'" 
           "is_linearform H' h'" "is_subspace H' E" "is_subspace F H'" 
           "graph F f <= graph H' h'" "ALL x:H'. h' x <= p x";
    show x: "x:H'"; by (asm_simp, rule graphD1);
    show "graph H' h' <= graph H h";
      by (asm_simp only: chain_ball_Union_upper);
  qed;
qed;


lemma some_H'h'2: 
  "[| M = norm_prev_extensions E p F f; c: chain M; graph H h = Union c; x:H; y:H|] 
  ==> EX H' h'. x:H' & y:H' & (graph H' h' <= graph H h)
                & is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
                (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume "M = norm_prev_extensions E p F f" "c: chain M" "graph H h = Union c";
 
  let ?P = "%H h. is_linearform H h 
                    & is_subspace H E 
                    & is_subspace F H
                    & (graph F f <= graph H h)
                    & (ALL x:H. h x <= p x)";
  assume "x:H";
  have e1: "EX H' h' t. t : (graph H h) & t = (x, h x) & (graph H' h'):c & t:graph H' h' &
                        ?P H' h'";
    by (rule some_H'h't); 
  assume "y:H";
  have e2: "EX H' h' t. t : (graph H h) & t = (y, h y) & (graph H' h'):c & t:graph H' h' & 
                        ?P H' h'";
    by (rule some_H'h't); 

  from e1 e2; show ?thesis; 
  proof (elim exE conjE);
    fix H' h' t' H'' h'' t''; 
    assume "t' : graph H h" "t'' : graph H h" 
      "t' = (y, h y)" "t'' = (x, h x)"
      "graph H' h' : c" "graph H'' h'' : c"
      "t' : graph H' h'" "t'' : graph H'' h''" 
      "is_linearform H' h'" "is_linearform H'' h''"
      "is_subspace H' E" "is_subspace H'' E"
      "is_subspace F H'" "is_subspace F H''"
      "graph F f <= graph H' h'" "graph F f <= graph H'' h''"
      "ALL x:H'. h' x <= p x" "ALL x:H''. h'' x <= p x";

    have "(graph H'' h'') <= (graph H' h') | (graph H' h') <= (graph H'' h'')";
      by (rule chainD);
    thus "?thesis";
    proof; 
      assume "(graph H'' h'') <= (graph H' h')";
      show ?thesis;
      proof (intro exI conjI);
	have xh: "(x, h x): graph H' h'"; by (fast);
	thus x: "x:H'"; by (rule graphD1);
	show y: "y:H'"; by (asm_simp, rule graphD1);
	show "(graph H' h') <= (graph H h)";
	  by (asm_simp only: chain_ball_Union_upper);
      qed;
    next;
      assume "(graph H' h') <= (graph H'' h'')";
      show ?thesis;
      proof (intro exI conjI);
	show x: "x:H''"; by (asm_simp, rule graphD1);
	have yh: "(y, h y): graph H'' h''"; by (fast);
        thus y: "y:H''"; by (rule graphD1);
        show "(graph H'' h'') <= (graph H h)";
          by (asm_simp only: chain_ball_Union_upper);
      qed;
    qed;
  qed;
qed;



lemma sup_uniq: "[| is_vectorspace E; is_subspace F E; is_quasinorm E p; is_linearform F f;
       ALL x:F. f x <= p x; M == norm_prev_extensions E p F f; c : chain M;
       EX x. x : c; (x, y) : Union c; (x, z) : Union c |]
     ==> z = y";
proof -;
  assume "M == norm_prev_extensions E p F f" "c : chain M" "(x, y) : Union c" " (x, z) : Union c";
  have "EX H h. (x, y) : graph H h & (x, z) : graph H h"; 
  proof (elim UnionE chainD2 [elimify]); 
    fix G1 G2; assume "(x, y) : G1" "G1 : c" "(x, z) : G2" "G2 : c" "c <= M";
    have "G1 : M"; by (rule subsetD);
    hence e1: "EX H1 h1. graph H1 h1 = G1";  
      by (force dest: norm_prev_extension_D);
    have "G2 : M"; by (rule subsetD);
    hence e2: "EX H2 h2. graph H2 h2 = G2";  
      by (force dest: norm_prev_extension_D);
    from e1 e2; show ?thesis; 
    proof (elim exE);
      fix H1 h1 H2 h2; assume "graph H1 h1 = G1" "graph H2 h2 = G2";
      have "G1 <= G2 | G2 <= G1"; by (rule chainD);
      thus ?thesis;
      proof;
        assume "G1 <= G2";
        thus ?thesis;
        proof (intro exI conjI);
          show "(x, y) : graph H2 h2"; by force;
          show "(x, z) : graph H2 h2"; by asm_simp;
        qed;
      next;
        assume "G2 <= G1";
        thus ?thesis;
        proof (intro exI conjI);
          show "(x, y) : graph H1 h1"; by asm_simp;
          show "(x, z) : graph H1 h1"; by force; 
        qed;
      qed;
    qed;
  qed;
  thus ?thesis; 
  proof (elim exE conjE);
    fix H h; assume "(x, y) : graph H h" "(x, z) : graph H h";
    have "y = h x"; by (rule graph_lemma2);
    also; have "h x = z"; by (rule graph_lemma2 [RS sym]);
    finally; show "z = y"; by (rule sym);
  qed;
qed;


lemma sup_lf: "[| M = norm_prev_extensions E p F f; c: chain M; graph H h = Union c|] 
   ==> is_linearform H h";
proof -; 
  assume "M = norm_prev_extensions E p F f" "c: chain M" "graph H h = Union c";
 
  let ?P = "%H h. is_linearform H h 
                    & is_subspace H E 
                    & is_subspace F H
                    & (graph F f <= graph H h)
                    & (ALL x:H. h x <= p x)";

  show "is_linearform H h";
  proof;
    fix x y; assume "x : H" "y : H"; 
    show "h (x [+] y) = h x + h y"; 
    proof -;
      have "EX H' h'. x:H' & y:H' & (graph H' h' <= graph H h) &
                    is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
                    (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)";
        by (rule some_H'h'2);
      thus ?thesis; 
      proof (elim exE conjE);
        fix H' h'; assume "x:H'" "y:H'" 
          and b: "graph H' h' <= graph H h" 
          and "is_linearform H' h'" "is_subspace H' E";
        have h'x: "h' x = h x"; by (rule graph_lemma3); 
        have h'y: "h' y = h y"; by (rule graph_lemma3);
        have h'xy: "h' (x [+] y) = h' x + h' y"; by (rule linearform_add_linear);
        have "h' (x [+] y) = h (x [+] y)";  
        proof -;
          have "x [+] y : H'";
            by (rule subspace_add_closed);
          with b; show ?thesis; by (rule graph_lemma3);
        qed;
        with h'x h'y h'xy; show ?thesis;
          by asm_simp; 
      qed;
    qed;

  next;  
    fix a x; assume  "x : H";
    show "h (a [*] x) = a * (h x)"; 
    proof -;
      have "EX H' h'. x:H' & (graph H' h' <= graph H h) &
                      is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
                      (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)";
	by (rule some_H'h');
      thus ?thesis; 
      proof (elim exE conjE);
	fix H' h';
	assume b: "graph H' h' <= graph H h";
	assume "x:H'" "is_linearform H' h'" "is_subspace H' E";
	have h'x: "h' x = h x"; by (rule graph_lemma3);
	have h'ax: "h' (a [*] x) = a * h' x"; by (rule linearform_mult_linear);
	have "h' (a [*] x) = h (a [*] x)";
	proof -;
	  have "a [*] x : H'";
	    by (rule subspace_mult_closed);
	  with b; show ?thesis; by (rule graph_lemma3);
	qed;
	with h'x h'ax; show ?thesis;
	  by asm_simp;
      qed;
    qed;
  qed;
qed;


lemma sup_ext: "[| M = norm_prev_extensions E p F f; c: chain M; EX x. x:c; graph H h = Union c|] 
   ==> graph F f <= graph H h";
proof -;
  assume "M = norm_prev_extensions E p F f" "c: chain M"  "graph H h = Union c"
    and  e: "EX x. x:c";
 
  show ?thesis; 
  proof (elim exE);
    fix x; assume "x:c"; 
    show ?thesis;    
    proof -;
      have "x:norm_prev_extensions E p F f"; 
      proof (rule subsetD);
	show "c <= norm_prev_extensions E p F f"; by (asm_simp add: chainD2);
      qed;
 
      hence "(EX G g. graph G g = x
                    & is_linearform G g 
                    & is_subspace G E
                    & is_subspace F G
                    & (graph F f <= graph G g) 
                    & (ALL x:G. g x <= p x))";
	by (asm_simp add: norm_prev_extension_D);

      thus ?thesis; 
      proof (elim exE conjE); 
	fix G g; assume "graph G g = x" "graph F f <= graph G g";
	show ?thesis; 
        proof -; 
          have "graph F f <= graph G g"; by assumption;
          also; have "graph G g <= graph H h"; by (asm_simp, fast);
          finally; show ?thesis; .;
        qed;
      qed;
    qed;
  qed;
qed;


lemma sup_supF: "[| M = norm_prev_extensions E p F f; c: chain M; EX x. x:c; graph H h = Union c;
                    is_subspace F E |] ==> is_subspace F H";
proof -; 
  assume "M = norm_prev_extensions E p F f" "c: chain M" "EX x. x:c" "graph H h = Union c"
    "is_subspace F E";

  show ?thesis; 
  proof (rule subspace_I);
    show "<0> : F"; by (rule zero_in_subspace); 
    show "F <= H"; 
    proof (rule graph_lemma4);
      show "graph F f <= graph H h";
        by (rule sup_ext);
    qed;
    show "ALL x:F. ALL y:F. x [+] y : F"; 
    proof (intro ballI); 
      fix x y; assume "x:F" "y:F";
      show "x [+] y : F"; by asm_simp;
    qed;
    show "ALL x:F. ALL a. a [*] x : F";
    proof (intro ballI allI);
      fix x a; assume "x:F";
      show "a [*] x : F"; by asm_simp;
    qed;
  qed;
qed;


lemma sup_subE: "[| M = norm_prev_extensions E p F f; c: chain M; EX x. x:c; graph H h = Union c;
                    is_subspace F E|] ==> is_subspace H E";
proof -; 
  assume "M = norm_prev_extensions E p F f" "c: chain M" "EX x. x:c" "graph H h = Union c"
    "is_subspace F E";

  show ?thesis; 
  proof (rule subspace_I);

    show "<0> : H"; 
    proof (rule subsetD [of F H]);
      have "is_subspace F H"; by (rule sup_supF);
      thus "F <= H"; by (rule subspace_subset);
      show  "<0> :F"; by (rule zero_in_subspace); 
    qed;

    show "H <= E"; 
    proof;
      fix x; assume "x:H";
      show "x:E";
      proof -;
	have "EX H' h'. x:H' & (graph H' h' <= graph H h) & 
               is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
               (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
	  by (rule some_H'h');
	thus ?thesis;
	proof (elim exE conjE);
	  fix H' h'; assume "x:H'" "is_subspace H' E";
	  show "x:E"; 
	  proof (rule subsetD);
	    show "H' <= E";
	      by (rule subspace_subset);    
	  qed;
	qed;
      qed;
    qed;

    show "ALL x:H. ALL y:H. x [+] y : H"; 
    proof (intro ballI); 
      fix x y; assume "x:H" "y:H";
      show "x [+] y : H";   
      proof -;
 	have "EX H' h'. x:H' & y:H' & (graph H' h' <= graph H h) & 
               is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
               (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
	  by (rule some_H'h'2); 
	thus ?thesis;
	proof (elim exE conjE); 
	  fix H' h'; assume "x:H'" "y:H'" "is_subspace H' E" "graph H' h' <= graph H h";
	  have "H' <= H"; by (rule graph_lemma4);
	  thus ?thesis;
	  proof (rule subsetD);
	    show "x [+] y : H'"; by (rule subspace_add_closed);
	  qed;
	qed;
      qed;
    qed;      

    show "ALL x:H. ALL a. a [*] x : H"; 
    proof (intro ballI allI); 
      fix x and a::real; assume "x:H";
      show "a [*] x : H"; 
      proof -;
	have "EX H' h'. x:H' & (graph H' h' <= graph H h) & 
               is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
               (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
	  by (rule some_H'h'); 
	thus ?thesis;
	proof (elim exE conjE);
	  fix H' h'; assume "x:H'" "is_subspace H' E" "graph H' h' <= graph H h";
  	  have "H' <= H"; by (rule graph_lemma4);
	  thus ?thesis;
	  proof (rule subsetD);
	    show "a [*] x : H'"; by (rule subspace_mult_closed);
	  qed;
	qed;
      qed;
    qed;
  qed;
qed;


lemma sup_norm_prev: "[| M = norm_prev_extensions E p F f; c: chain M; graph H h = Union c|] 
   ==> ALL x::'a:H. h x <= p x";
proof;
  assume "M = norm_prev_extensions E p F f" "c: chain M" "graph H h = Union c";
  fix x; assume "x:H";
  show "h x <= p x"; 
  proof -; 
    have "EX H' h'. x:H' & (graph H' h' <= graph H h) & 
               is_linearform H' h' & is_subspace H' E & is_subspace F H' & 
               (graph F f <= graph H' h') & (ALL x:H'. h' x <= p x)"; 
      by (rule some_H'h');
    thus ?thesis; 
    proof (elim exE conjE);
      fix H' h'; assume "x: H'" "graph H' h' <= graph H h" and a: "ALL x: H'. h' x <= p x" ;
      have "h x = h' x"; 
      proof(rule sym); 
        show "h' x = h x"; by (rule graph_lemma3);
      qed;
      also; from a; have "... <= p x "; ..;
      finally; show ?thesis; .;  
    qed;
  qed;
qed;


end;