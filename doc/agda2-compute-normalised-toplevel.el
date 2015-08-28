#!/bin/sh
":"; exec emacs --quick --script "$0" "$@" 2>/dev/null # -*- mode: emacs-lisp; lexical-binding: t; -*-


;;; Set Agda include path
(custom-set-variables
 '(agda2-include-dirs (quote (
    "."
    "/Users/pepijn/Projects/thesis/src"
    "/Users/pepijn/Projects/agda-stdlib/src"
    ))))


;;; Load given file
(find-file-literally (pop argv))


;;; Load Agda mode
(load-file (let ((coding-system-for-read 'utf-8))
             (shell-command-to-string "agda-mode locate")))
(agda2-mode)
(while agda2-in-progress (sleep-for 0 500))


;;; Load buffer into Agda
(agda2-load)
(while agda2-in-progress (sleep-for 0 500))


;;; Print normalised expression
(agda2-compute-normalised-toplevel (pop argv))
(while agda2-in-progress (sleep-for 0 500))
(with-current-buffer "*Agda information*"
  (princ (replace-regexp-in-string "[.]\\([^.^ ]+[.]\\)+" "" (buffer-string)))
  (terpri))


;;; Exit Emacs
(kill-emacs 0)
