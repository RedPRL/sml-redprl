 ;;; redprl-mode.el --- redprl major mode

(defvar redprl-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `redprl-mode'.")

(defvar redprl-syntax-table
  (let ((table (make-syntax-table)))
    ; C++-style comment start
    (modify-syntax-entry ?\/ ". 12b" table)
    ; end comment on line-break
    (modify-syntax-entry ?\n "> b" table)
    table)
  "Syntax table for `redprl-mode'.")

(defvar redprl-vernacular-keywords-regexp
  (regexp-opt
   '("Def" "Thm" "Sym" "Tac")
   'words))

(defvar redprl-builtin-constants-regexp
  (regexp-opt
   '("Base" "lbase" "lsuc" "Ax" "Univ" "member" "Squash" "Ensemble" "extract" "Atom" "ifeq" "dfun" "fun" "lam" "ap")
   'words))

(defvar redprl-sorts-regexp
  (regexp-opt
   '("exp" "lvl" "tac" "thm")
   'words))

(defvar redprl-tactic-name-regexp
  (regexp-opt
   '("auto" "eval" "ceval" "csym" "cstep" "witness" "trace" "intro" "elim" "eq" "id" "normalize" "unfold")
   'words))

(defun redprl-font-lock-defaults ()
  `((,redprl-vernacular-keywords-regexp . font-lock-keyword-face)
    (,redprl-builtin-constants-regexp . font-lock-constant-face)
    (,redprl-sorts-regexp . font-lock-type-face)
    (,redprl-tactic-name-regexp . font-lock-function-name-face)))

(defun redprl-imenu-generic-expression ()
  "To generate a table of contents for a RedPRL signature"
  '(("Definitions" "^Def\\s-+\\(\\w+\\)" 1)
    ("Theorems" "^Thm\\s-+\\(\\w+\\)" 1)
    ("Symbols" "^Sym\\s-+\\(\\w+\\)" 1)
    ("Tactics" "^Tac\\s-+\\(\\w+\\)" 1)))

(define-derived-mode redprl-mode fundamental-mode "redprl"
  :syntax-table redprl-syntax-table
  (setq-local comment-start "// ")
  (setq-local comment-start-skip "//+\\s-*")
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)
  (setq-local font-lock-defaults '((redprl-font-lock-defaults)))
  (setq-local imenu-generic-expression (redprl-imenu-generic-expression)))

(push '("\\.prl\\'" . redprl-mode) auto-mode-alist)

(provide 'redprl-mode)
 ;;; redprl-mode.el ends here
