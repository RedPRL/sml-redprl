;;; ob-red-jonprl.el --- org-babel functions for red-jonprl evaluation

;; Copyright (C) 2012 K. Adam Christensen

;; Author: K. Adam Christensen
;; Keywords: red-jonprllang, red-jonprl, literate programming, reproducible research
;; Homepage: http://orgmode.org
;; Version: 0.01
;; Package-Requires: ((red-jonprl-mode "1.0.0"))

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Org-Babel support for evaluating red-jonprl code.
;;; Code:
(require 'org)
(require 'ob)
(require 'ob-eval)
(require 'ob-ref)


;; optionally define a file extension for this language
(add-to-list 'org-babel-tangle-lang-exts '("red-jonprl" . "prl"))

(defvar org-babel-default-header-args:red-jonprl '())

(defvar org-babel-red-jonprl-command "jonprl"
  "The red-jonprl command to use to compile and run the red-jonprl code.")

(defmacro org-babel-red-jonprl-as-list (val)
  (list 'if (list 'listp val) val (list 'list val)))

(defun org-babel-expand-body:red-jonprl (body params &optional processed-params)
  "Expand BODY according to PARAMS, return the expanded body."
  (require 'red-jonprl-mode)
  body)

(defun org-babel-execute:red-jonprl (body params)
  (let* ((tangle (cdr (assoc :tangle params)))
         (script-file
          (if (string-equal tangle "no")
              (org-babel-temp-file "org-babel-" ".prl")
            tangle)))
    (with-temp-file script-file
      (insert body))
    (let* ((pn (org-babel-process-file-name script-file))
           (cmd (format "%s %s" org-babel-red-jonprl-command pn)))
      (message cmd)
      (shell-command-to-string cmd)
      )))

;; This function should be used to assign any variables in params in
;; the context of the session environment.
(defun org-babel-prep-session:red-jonprl (session params)
  "This function does nothing as Red-Jonprl is a compiled language with no
support for sessions"
  (error "Red-Jonprl is a compiled languages -- no support for sessions"))

(defun org-babel-red-jonprl-var-to-red-jonprl (pair)
  "Convert an elisp var into a string of red-jonprl source code
specifying a var of the same value."
  (let ((var (car pair))
        (val (cdr pair)))
    (when (symbolp val)
      (setq val (symbol-name val)))
    ;; TODO(pope): Handle tables and lists.
    (format "var %S = %S" var val)))

(defun org-babel-red-jonprl-table-or-string (results)
  "If the results look like a table, then convert them into an
Emacs-lisp table, otherwise return the results as a string."
  (org-babel-script-escape results))

(provide 'ob-red-jonprl)
;;; ob-red-jonprl.el ends here
