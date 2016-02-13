 ;;; red-jonprl-mode.el --- Red-Jonprl-Mode major mode

(defvar red-jonprl-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `red-jonprl-mode'.")

(defvar red-jonprl-mode-syntax-table
  (let ((st (make-syntax-table)))
    st)
  "Syntax table for `red-jonprl-mode'.")

(defvar red-jonprl-mode-font-lock-defaults
  '(("\\<Def\\>\\|\\<Thm\\>\\|\\<Tac\\>" . font-lock-keyword-face)
    ("^\\s-*\\(//.*\\)$" . font-lock-comment-face)
    ("\\<exp\\>\\|\\<lvl\\>\\|\\<tac\\>" . font-lock-type-face)
    ("\\<Base\\>\\|\\<lbase\\>\\|\\<lsuc\\>\\|\\<Ax\\>\\|\\<Univ\\>\\|\\<member\\>\\|\\<Squash\\>\\|\\<Species\\>" . font-lock-constant-face)
    ("\\<auto\\>\\|\\<eval-goal\\>\\|\\<ceval\\>\\|\\<cstep\\>\\|\\<witness\\>" . font-lock-function-name-face)
    )
  "Highlighting specification for `red-jonprl-mode'.")

(define-derived-mode red-jonprl-mode fundamental-mode "red-jonprl"
  :syntax-table red-jonprl-mode-syntax-table
  (setq-local comment-start "// ")
  (setq-local comment-start-skip "//+\\s-*")
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)
  (setq-local font-lock-defaults '(red-jonprl-mode-font-lock-defaults))
  (setq-local imenu-generic-expression
              '(("Theorems" "^Thm\\s-+\\(\\w+\\)" 1)
                ("Definitions" "^Def\\s-+\\(\\w+\\)" 1)
                ("Tactics" "^Tac\\s-+\\(\\w+\\)" 1)))

  )


(provide 'red-jonprl-mode)

(push '("\\.prl\\'" . red-jonprl-mode) auto-mode-alist)
 ;;; red-jonprl-mode.el ends here
