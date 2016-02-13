 ;;; red-jonprl-mode.el --- Red-Jonprl-Mode major mode

(defvar red-jonprl-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `red-jonprl-mode'.")

(defvar red-jonprl-syntax-table
  (let ((st (make-syntax-table)))
    st)
  "Syntax table for `red-jonprl-mode'.")

(defvar red-jonprl-vernacular-keywords-regexp
  (regexp-opt
   '("Def" "Thm" "Tac")
   'words))

(defvar red-jonprl-builtin-constants-regexp
  (regexp-opt
   '("Base" "lbase" "lsuc" "Ax" "Univ" "member" "Squash" "Species" "extract")
   'words))

(defvar red-jonprl-sorts-regexp
  (regexp-opt
   '("exp" "lvl" "tac" "thm")
   'words))

(defvar red-jonprl-tactic-name-regexp
  (regexp-opt
   '("auto" "eval-goal" "ceval" "csym" "cstep" "witness" "trace")
   'words))

(defun red-jonprl-font-lock-defaults ()
  `((,red-jonprl-vernacular-keywords-regexp . font-lock-keyword-face)
    ("^\\s-*\\(//.*\\)$" . font-lock-comment-face)
    (,red-jonprl-builtin-constants-regexp . font-lock-constant-face)
    (,red-jonprl-sorts-regexp . font-lock-type-face)
    (,red-jonprl-tactic-name-regexp . font-lock-function-name-face)))

(define-derived-mode red-jonprl-mode fundamental-mode "red-jonprl"
  :syntax-table red-jonprl-syntax-table
  (setq-local comment-start "// ")
  (setq-local comment-start-skip "//+\\s-*")
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)
  (setq-local font-lock-defaults '((red-jonprl-font-lock-defaults)))
  (setq-local imenu-generic-expression
              '(("Theorems" "^Thm\\s-+\\(\\w+\\)" 1)
                ("Definitions" "^Def\\s-+\\(\\w+\\)" 1)
                ("Tactics" "^Tac\\s-+\\(\\w+\\)" 1)))
  )


(provide 'red-jonprl-mode)
(push '("\\.prl\\'" . red-jonprl-mode) auto-mode-alist)
 ;;; red-jonprl-mode.el ends here
