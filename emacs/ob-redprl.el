;; Org-Babel support for evaluating redprl code.
;;; Code:
(require 'org)
(require 'ob)
(require 'ob-eval)
(require 'ob-ref)


;; optionally define a file extension for this language
(add-to-list 'org-babel-tangle-lang-exts '("redprl" . "prl"))

(defvar org-babel-default-header-args:redprl '())

(defvar org-babel-redprl-command "redprl"
  "The redprl command to use to compile and run the redprl code.")

(defmacro org-babel-redprl-as-list (val)
  (list 'if (list 'listp val) val (list 'list val)))

(defun org-babel-expand-body:redprl (body params &optional processed-params)
  "Expand BODY according to PARAMS, return the expanded body."
  (require 'redprl-mode)
  body)

(defun org-babel-execute:redprl (body params)
  (let* ((script-file (org-babel-temp-file "org-babel-" ".prl")))
    (with-temp-file script-file
      (insert body))
    (let*
        ((pn (org-babel-process-file-name script-file))
         (cmd (format "%s %s" org-babel-redprl-command pn)))
      (message cmd)
      (shell-command-to-string cmd))))

(defun org-babel-redprl-table-or-string (results)
  "If the results look like a table, then convert them into an Emacs-lisp table, otherwise return the results as a string."
  (org-babel-script-escape results))

(provide 'ob-redprl)
;;; ob-redprl.el ends here
