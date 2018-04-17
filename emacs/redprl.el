;;; redprl.el --- Major mode for editing RedPRL proofs and interacting with RedPRL  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Jonathan Sterling
;; Copyright (C) 2017  Jonathan Sterling, Favonia

;; Author: Jonathan Sterling <jon@jonmsterling.com>
;; Package-Requires: ((emacs "24.3"))
;; Version: 0.0.1
;; Keywords: languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing RedPRL developments.  The current
;; editing features include simple syntax highlighting, imenu, and
;; completion support.  Additionally, there is a command to run RedPRL
;; in a compilation buffer.
;;
;; RedPRL can be obtained from https://github.com/RedPRL/sml-redprl .
;;
;; Make sure to set the variable `redprl-command' to the location of the
;; redprl binary.

;;; Code:

(require 'cl-lib)

(defgroup redprl nil "RedPRL" :prefix 'redprl :group 'languages)

(defface redprl-declaration-keyword-face
  '((t (:inherit font-lock-keyword-face))) "Face for RedPRL's declaration keywords."
  :group 'redprl)

(defface redprl-sort-face
  '((t (:inherit font-lock-type-face))) "Face for RedPRL's built-in sorts."
  :group 'redprl)

(defface redprl-metavar-face
  '((t (:inherit font-lock-variable-name-face))) "Face for RedPRL's meta variables."
  :group 'redprl)

(defface redprl-number-face
  '((t (:inherit font-lock-constant-face))) "Face for RedPRL's numbers."
  :group 'redprl)

(defface redprl-expression-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's expression keywords."
  :group 'redprl)

(defface redprl-expression-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's expression symbols."
  :group 'redprl)

(defface redprl-tactic-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's tactic keywords."
  :group 'redprl)

(defface redprl-tactic-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's tactic symbols."
  :group 'redprl)

(defface redprl-sequent-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's sequent keywords."
  :group 'redprl)

(defface redprl-sequent-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for RedPRL's sequent symbols."
  :group 'redprl)

(defcustom redprl-command "redprl"
  "The command to be run for RedPRL."
  :group 'redprl
  :type 'string
  :tag "Command for RedPRL"
  :options '("redprl"))

(defcustom redprl-mode-hook '(redprl-display-revolutionary-saying)
  "Hook to be run on starting `redprl-mode'."
  :group 'redprl
  :type 'hook
  :options '(redprl-display-revolutionary-saying))

(defvar redprl-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?- "w" table)
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?= "w" table)
    (modify-syntax-entry ?' "w" table)
    (modify-syntax-entry ?/  "_ 123" table)
    (modify-syntax-entry ?\n ">" table)
    table)
  "Syntax table for RedPRL.")

(defconst redprl-declaration-keywords
  '("define" "extract" "print" "quit" "tactic" "theorem")
  "RedPRL's keywords.")

(defconst redprl-sort-keywords
  '("dim" "hyp" "exp" "lvl" "tac" "jdg")
  "RedPRL's built-in sorts.")

(defconst redprl-expression-keywords
  '("tv" "ax" "fcom"
    "bool" "tt" "ff" "if"
    "nat" "zero" "succ" "nat-rec" "int" "pos" "negsucc" "int-rec"
    "void"
    "S1" "base" "loop" "S1-rec"
    "lam" "app"
    "record" "tuple"
    "path" "line" "abs"
    "pushout" "left" "right" "glue" "pushout-rec"
    "coeq" "cecod" "cedom" "coeq-rec"
    "mem" "ni"
    "box" "cap"
    "ecom"
    "V" "Vin" "Vproj"
    "universe" "U"
    "hcom" "ghcom" "coe" "com" "gcom"
    "lmax")
  "RedPRL's expression keywords.")

(defconst redprl-expression-symbols
  '("->" "~>" "<~" "$" "*" "!" "@" "=" "+" "++" "=>")
  "RedPRL's expression symbols.")

(defconst redprl-tactic-keywords
  '("auto" "auto-step" "case" "concl" "cut-lemma" "elim" "else" "exact" "goal"
    "hyp" "id" "lemma" "let" "claim" "match" "of" "progress"
    "query" "rec" "reduce" "refine" "repeat" "rewrite" "symmetry" "inversion" "assumption"
    "then" "unfold" "use" "with")
  "RedPRL's tactic keywords.")

(defconst redprl-tactic-symbols
  '("?" ";")
  "RedPRL's tactic symbols.")

(defconst redprl-sequent-keywords
  '("at" "by" "in" "true" "type" "synth" "discrete" "kan" "hcom" "coe" "pre")
  "RedPRL's sequent keywords.")

(defconst redprl-sequent-symbols
  '(">>")
  "RedPRL's sequent symbols.")

(defconst redprl-def-name-regexp
  '(: "Def" (+ whitespace) (group-n 1 (+ word)) not-wordchar))

(defconst redprl-thm-name-regexp
  '(: "Thm" (+ whitespace) (group-n 1 (+ word)) not-wordchar))

(defconst redprl-tac-name-regexp
  '(: "Tac" (+ whitespace) (group-n 1 (+ word)) not-wordchar))

(defconst redprl-declaration-name-regexp
  `(or ,redprl-def-name-regexp
       ,redprl-thm-name-regexp
       ,redprl-tac-name-regexp))

(defvar redprl-mode-font-lock-keywords
  `(
    ;; Declaration keyword
    (,(regexp-opt redprl-declaration-keywords 'words) 0 'redprl-declaration-keyword-face)

    ;; Built-in sorts
    (,(regexp-opt redprl-sort-keywords 'words) 0 'redprl-sort-face)

    ;; Meta variables
    (,(rx "#" (+ word)) 0 'redprl-metavar-face)

    ;; Numbers
    (,(rx word-start (? "-") (+ digit)) 0 'redprl-number-face)

    ;; Built-in expressions
    (,(regexp-opt redprl-expression-keywords 'words) 0 'redprl-expression-keyword-face)
    (,(regexp-opt redprl-expression-symbols 'nil) 0 'redprl-expression-symbol-face)

    ;; Built-in tactics
    (,(regexp-opt redprl-tactic-keywords 'words) 0 'redprl-tactic-keyword-face)
    (,(regexp-opt redprl-tactic-symbols 'nil) 0 'redprl-tactic-symbol-face)

    ;; Sequents
    (,(regexp-opt redprl-sequent-keywords 'words) 0 'redprl-sequent-keyword-face)
    (,(regexp-opt redprl-sequent-symbols 'nil) 0 'redprl-sequent-symbol-face)
    ))

(defun redprl-defined-names ()
  "Find all names defined in this buffer."
  (save-excursion
    (let ((names ()))
      (goto-char (point-min))
      (while (re-search-forward (rx-to-string redprl-declaration-name-regexp) nil t)
        ;; Do not save if inside comment
        (unless (nth 4 (syntax-ppss))
          (push (match-string-no-properties 1) names)))
      names)))

(defun redprl-completion-at-point ()
  "Attempt to perform completion for RedPRL's keywords."
  (when (looking-back (rx (+ word)) nil t)
    (let* ((match (match-string-no-properties 0))
           (start-pos (match-beginning 0))
           (end-pos (match-end 0))
           (candidates (cl-remove-if-not
                        (apply-partially #'string-prefix-p match)
                        (append redprl-tactic-keywords
                                redprl-expression-keywords
                                redprl-sequent-keywords
                                redprl-sort-keywords
                                (redprl-defined-names)))))
      (if (null candidates)
          nil
        (list start-pos end-pos candidates)))))

(defconst redprl--compilation-buffer-name
  "*RedPRL*"
  "The name to use for RedPRL compilation buffers.")

(defun redprl--compilation-buffer-name-function (_mode)
  "Compute a buffer name for the `redprl-mode' compilation buffer."
  redprl--compilation-buffer-name)

(defun redprl-compile-buffer ()
  "Load the current file into RedPRL."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if filename
        (progn
          (when (buffer-modified-p) (save-buffer))
          (let* ((dir (file-name-directory filename))
                 (file (file-name-nondirectory filename))
                 (command (concat redprl-command " " file))

                 ;; Emacs compile config stuff - these are special vars
                 (compilation-buffer-name-function
                  'redprl--compilation-buffer-name-function)
                 (default-directory dir))
            (compile command)))
      (error "Buffer has no file name"))))


(defconst redprl--revolutionary-sayings
  '("Decisively Smash the Formalist Clique!"
    "Long Live the Anti-Realist Struggle!"
    "We Can Prove It!"
    "Uphold Cubical Thought!"
    "Criticize The Old World And Build A New World Using Cubical Thought As A Weapon!")
  "Words of encouragement to be displayed when RedPRL is initially launched.")

(defun redprl-display-revolutionary-saying ()
  "Display a revolutionary saying to hearten RedPRL users."
  (interactive)
  (let ((revolutionary-saying (nth (random (length redprl--revolutionary-sayings))
                                   redprl--revolutionary-sayings)))
    (message "%s" revolutionary-saying)))

;;;###autoload
(define-derived-mode redprl-mode prog-mode "RedPRL"
  "Major mode for editing RedPRL proofs.
\\{redprl-mode-map}"

  (set (make-local-variable 'comment-start) "// ")

  (setq font-lock-defaults '((redprl-mode-font-lock-keywords) nil nil))

  (set (make-local-variable 'imenu-generic-expression)
       `(("Def" ,(rx-to-string redprl-def-name-regexp) 1)
         ("Thm" ,(rx-to-string redprl-thm-name-regexp) 1)
         ("Tac" ,(rx-to-string redprl-tac-name-regexp) 1)))

  ;; Bind mode-specific commands to keys
  (define-key redprl-mode-map (kbd "C-c C-l") 'redprl-compile-buffer)

  (eval-after-load 'flycheck
    '(progn
       (flycheck-define-checker redprl
         "A RedPRL proof checker."
         :command ("redprl" source)
         :error-patterns
         ((error line-start
                 (file-name) ":" line "." column "-" (+ num) "." (+ num) " [Error]:\n"
                 (message
                  (+ not-newline)
                  (* "\n  " (* not-newline)))
                 line-end)
          (warning line-start
                   (file-name) ":" line "." column "-" (+ num) "." (+ num) " [Warning]:\n"
                   (message
                    (+ not-newline)
                    (* "\n  " (* not-newline)))
                   line-end)
          (info line-start
                (file-name) ":" line "." column "-" (+ num) "." (+ num) " [Info]:\n"
                (message
                 (+ not-newline)
                 (* "\n  " (* not-newline)))
                line-end))
         :modes redprl-mode)

       (add-to-list 'flycheck-checkers 'redprl)))


  (set (make-local-variable 'completion-at-point-functions)
       '(redprl-completion-at-point)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.prl\\'" . redprl-mode))

(provide 'redprl)
;;; redprl.el ends here
