 ;;; red-jonprl-mode.el --- Red-Jonprl major mode

(defvar red-jonprl-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `red-jonprl-mode'.")

(defvar red-jonprl-syntax-table
  (let ((table (make-syntax-table)))
    ; C++-style comment start
    (modify-syntax-entry ?\/ ". 12b" table)
    ; end comment on line-break
    (modify-syntax-entry ?\n "> b" table)
    table)
  "Syntax table for `red-jonprl-mode'.")

(defvar red-jonprl-vernacular-keywords-regexp
  (regexp-opt
   '("Def" "Thm" "Sym" "Tac")
   'words))

(defvar red-jonprl-builtin-constants-regexp
  (regexp-opt
   '("Base" "lbase" "lsuc" "Ax" "Univ" "member" "Squash" "Ensemble" "extract" "Atom" "ifeq" "dfun" "fun" "lam" "ap")
   'words))

(defvar red-jonprl-sorts-regexp
  (regexp-opt
   '("exp" "lvl" "tac" "thm")
   'words))

(defvar red-jonprl-tactic-name-regexp
  (regexp-opt
   '("auto" "eval" "ceval" "csym" "cstep" "witness" "trace" "intro" "elim" "eq" "id" "normalize" "unfold")
   'words))

(defun red-jonprl-font-lock-defaults ()
  `((,red-jonprl-vernacular-keywords-regexp . font-lock-keyword-face)
    (,red-jonprl-builtin-constants-regexp . font-lock-constant-face)
    (,red-jonprl-sorts-regexp . font-lock-type-face)
    (,red-jonprl-tactic-name-regexp . font-lock-function-name-face)))

(defun red-jonprl-imenu-generic-expression ()
  "To generate a table of contents for a Red JonPRL signature"
  '(("Definitions" "^Def\\s-+\\(\\w+\\)" 1)
    ("Theorems" "^Thm\\s-+\\(\\w+\\)" 1)
    ("Symbols" "^Sym\\s-+\\(\\w+\\)" 1)
    ("Tactics" "^Tac\\s-+\\(\\w+\\)" 1)))

(define-derived-mode red-jonprl-mode fundamental-mode "red-jonprl"
  :syntax-table red-jonprl-syntax-table
  (setq-local comment-start "// ")
  (setq-local comment-start-skip "//+\\s-*")
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)
  (setq-local font-lock-defaults '((red-jonprl-font-lock-defaults)))
  (setq-local imenu-generic-expression (red-jonprl-imenu-generic-expression)))

(push '("\\.prl\\'" . red-jonprl-mode) auto-mode-alist)

(provide 'red-jonprl-mode)
 ;;; red-jonprl-mode.el ends here
