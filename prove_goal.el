;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; special function for Isabelle
;;
;;
; goalify.el
;
; Emacs command to change "goal" proofs to "prove_goal" proofs 
; and reverse IN A REGION.
;    [would be difficult in "sed" since replacements involve multiple lines]
;
;; origin is prove_goalify.el
;; enhanced by Franz Regensburger
;;    corrected some errors in regular expressions
;;    changed name prove_goalify --> goalify
;;    added inverse functions        ungoalify
;
; function goalify:
; 
; val PAT = goalARGS;$
; COMMANDS;$
; val ID = result();
; 
; to
; 
; val ID = prove_goalARGS
;  (fn PAT=>
;  [
;  COMMANDS
;  ]);
;;
;; Note: PAT must be an identifier. _ as pattern is not supported.
;;
; function ungoalify:
; 
; val ID = prove_goalARGS
;  (fn PAT=>
;  [
;  COMMANDS
;  ]);
;
;
; to 
; val PAT = goalARGS;$
; COMMANDS;$
; val ID = result();
; 


(defun ungoalify (alpha omega)
 "Change well-formed prove_goal proofs to goal...result"
  (interactive "r"
	       "*") 
  ; 0: restrict editing to region
  (narrow-to-region alpha omega)

  ; 1: insert delimiter ID 
  (goto-char (point-min))
  (replace-regexp  
  "[ \t]*val[ \t]+\\([^ \t\n=]+\\)[ \t\n=]+prove_goal" "\\1")

  ; 2: insertt delimiter ARGS  PAT  and  before first command   
  (goto-char (point-min))
  (replace-regexp  
  "[ \n\t]*(fn[ \t]+\\([^=]+\\)=>[^(]*" "\\1\n")

  ; 3: shift  over all commands
  ; Note: only one line per command
  (goto-char (point-max))
  (while (not (equal (point) (point-min)))
    (goto-char (point-min))
    (replace-regexp  
    "[ \t]*\\(.*\\),[ \t]*\n" "by \\1;\n"))
    
  ; 4: fix last 
  (goto-char (point-min))
  (replace-regexp  
    "[ \t]*\\(.*\\)[ \t\n]*\][ \t\n]*)[ \t\n]*;" "by \\1;")

  ; 5: arange new val Pat = goal .. 
  (goto-char (point-min))
  (replace-regexp  
  "\\([^]*\\)\\([^]*\\)\\([^]*\\)\n\\([^]*\\)"
  "val \\3= goal\\2;\n\\4\nval \\1 = result();")

  ; widen again
  (widen)
)


(defun goalify (alpha omega)
 "Change well-formed goal...result proofs to use prove_goal"
  (interactive "r"
               "*") 

  ; 0: restrict editing to region
  (narrow-to-region alpha omega)

  ; 1: delimit the identifier in "val ID = result()" using ^Q
  (goto-char (point-min))
  (replace-regexp  "val[ \t\n]+\\([^ \t\n=]+\\)[ \t\n=]+result();[ \t]*$"
   "\\1")

  ; 2: replace terminal \";  by  
  (goto-char (point-min))
  (replace-regexp  "\";[ \t]*$" "")

  ; 3: replace lines "by ...;" with "...,"
  (goto-char (point-min))
  (replace-regexp  "by[ \n\t]*\\([^;]*\\)[ \t\n]*;"  "\t\\1,")

  ; 4: removing the extra commas, those followed by ^Q
  (goto-char (point-min))
  (replace-regexp  ",[ \n\t]*"  "")

  ; 5: transforming goal... to prove_goal...
  (goto-char (point-min))
  (replace-regexp
  "val[ \t\n]+\\([^ \n\t=]+\\)[ \t\n=]+goal\\([^]*\\)
\\([^]*\\)\\([^]*\\)"  
  "val \\4 = prove_goal\\2\"\n (fn \\1 =>\n\t[\n\\3\n\t]);")

  ; 6: widen again
  (widen)
)

