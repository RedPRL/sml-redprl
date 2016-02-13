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
  (let* ((script-file (org-babel-temp-file "org-babel-" ".prl")))
    (with-temp-file script-file
      (insert body))
    (let*
        ((pn (org-babel-process-file-name script-file))
         (cmd (format "%s %s" org-babel-red-jonprl-command pn)))
      (message cmd)
      (shell-command-to-string cmd))))

(defun org-babel-red-jonprl-table-or-string (results)
  "If the results look like a table, then convert them into an Emacs-lisp table, otherwise return the results as a string."
  (org-babel-script-escape results))

(provide 'ob-red-jonprl)
;;; ob-red-jonprl.el ends here
