;
; $Id$
;
; Setup Emacs for Isabelle environment.
;

;; Misc settings

(setq isa-use-sml-mode nil)


;; Fonts and Keymaps

(load (concat (getenv "ISABELLE_HOME") "/src/Tools/8bit/xemacs/isa_xemacs.emacs"
))
