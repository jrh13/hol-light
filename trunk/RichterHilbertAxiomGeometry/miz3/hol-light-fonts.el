;; The function Math-fonts-for-HOL-Light replace the expressions
;; ==>, <=>, ~, \/, /\, !, ?, SUBSET, IN, UNION, INTER and {} 
;;  in a file with the mathematical characters (used by Isabelle) 
;; ⇒, ⇔, ¬, ∨, ∧, ∀, ∃, ⊂, ∈, ∪, ∩ and ∅.
;; The function Remove-math-fonts-for-HOL-Light turns the mathematical characters
;; ⇒, ⇔, ¬ etc back to HOL Light expressions ==>, <=>, ~ etc.

;; Given a file with mathematical characters, the function
;; File-remove-math-fonts-for-HOL-Light makes the X-selection a
;; version of the file with ∀, ∃, ∩,... replaced by !, ?, INTER,... so
;; it can be pasted into a ocaml/HOL-Light process.

;; the function Region-math-fonts-removed-for-HOL-Light similarly
;; processes the region.

(defun Math-fonts-for-HOL-Light ()
  "replace HOL Light expressions (!, ?, INTER,...) with mathematical characters (∀, ∃, ∩,...) in the entire buffer."
  (interactive)
  (let ((start (point)))
    (setq case-fold-search nil)
    (goto-char (point-min))
    (while (search-forward "\\/" nil t)
      (replace-match "∨" nil t))
    (goto-char (point-min))
    (while (search-forward "/\\" nil t)
      (replace-match "∧" nil t))
    (goto-char (point-min))
    (while (search-forward "===" nil t)
      (replace-match "≡" nil t))
    (goto-char (point-min))
    (while (search-forward "==>" nil t)
      (replace-match "⇒" nil t))
    (goto-char (point-min))
    (while (search-forward "~" nil t)
      (replace-match "¬" nil t))
    (goto-char (point-min))
    (while (search-forward "<=>" nil t)
      (replace-match "⇔" nil t))
    (goto-char (point-min))
    (while (search-forward "!" nil t)
      (replace-match "∀" nil t))
    (goto-char (point-min))
    (while (search-forward "?" nil t)
      (replace-match "∃" nil t))
    (goto-char (point-min))
    (while (search-forward "∃∀" nil t)
      (replace-match "∃!" nil t))
    (goto-char (point-min))
    (while (search-forward " SUBSET " nil t)
      (replace-match " ⊂ " nil t))
    (goto-char (point-min))
    (while (search-forward " SUBSET
" nil t)
      (replace-match " ⊂
" nil t))
    (goto-char (point-min))
    (while (search-forward " INTER " nil t)
      (replace-match " ∩ " nil t))
    (goto-char (point-min))
    (while (search-forward " INTER
" nil t)
      (replace-match " ∩
" nil t))
    (goto-char (point-min))
    (while (search-forward " UNION " nil t)
      (replace-match " ∪ " nil t))
    (goto-char (point-min))
    (while (search-forward " UNION
" nil t)
      (replace-match " ∪
" nil t))
    (goto-char (point-min))
    (while (search-forward "{}" nil t)
      (replace-match "∅" nil t))
    (goto-char (point-min))
    (while (search-forward "cong" nil t)
      (replace-match "≅" nil t))
    (goto-char (point-min))
    (while (search-forward " IN " nil t)
      (replace-match " ∈ " nil t))
    (goto-char (point-min))
    (while (search-forward " DIFF " nil t)
      (replace-match " ━ " nil t))
    (goto-char (point-min))
    (while (search-forward " DIFF
" nil t)
      (replace-match " ━
" nil t))
    (goto-char (point-min))
    (while (search-forward " INSERT " nil t)
      (replace-match " ╪ " nil t))
    (goto-char (point-min))
    (while (search-forward "alpha" nil t)
      (replace-match "α" nil t))
    (goto-char (point-min))
    (while (search-forward "beta" nil t)
      (replace-match "β" nil t))
    (goto-char (point-min))
    (while (search-forward "gamma" nil t)
      (replace-match "γ" nil t))
    (goto-char (point-min))
    (while (search-forward " angle " nil t)
      (replace-match " ∡ " nil t))
    (goto-char (point-min))
    (while (search-forward "(angle " nil t)
      (replace-match "(∡ " nil t))
    (goto-char (point-min))
    (while (search-forward "not===" nil t)
      (replace-match " ≢ " nil t))
    (goto-char (point-min))
    (while (search-forward "NOTIN" nil t)
      (replace-match "∉" nil t))
    (goto-char (point-min))
    (while (search-forward "neq" nil t)
      (replace-match " ≠ " nil t))
    (goto-char (point-min))
    (while (search-forward "\\" nil t)
      (replace-match "λ" nil t))
    (goto-char (point-min))
    (while (search-forward "parallel" nil t)
      (replace-match "∥" nil t))
    (goto-char (point-min))
    (while (search-forward "theta" nil t)
      (replace-match "θ" nil t))
    (goto-char (point-min))
    (while (search-forward "mu" nil t)
      (replace-match "μ" nil t))
    (goto-char (point-min))
    (while (search-forward "--->" nil t)
      (replace-match "→" nil t))
    (goto-char (point-min))
    (while (search-forward " prod " nil t)
      (replace-match " ∏ " nil t))
    (goto-char (point-min))
    (while (search-forward " _o_ " nil t)
      (replace-match " ∘ " nil t))
    (goto-char start)))

(defun Remove-math-fonts-for-HOL-Light ()
  "replace mathematical characters (∀, ∃, ∩,...) with HOL Light expressions (!, ?, INTER,...)."
  (interactive)
  (setq case-fold-search nil)
  (untabify (point-min) (point-max))
  (goto-char (point-min))
  (while (search-forward "∨" nil t)
    (replace-match "\\/" nil t))
  (goto-char (point-min))
  (while (search-forward "∧" nil t)
    (replace-match "/\\" nil t))
  (goto-char (point-min))
  (while (search-forward "≡" nil t)
    (replace-match "===" nil t))
  (goto-char (point-min))
  (while (search-forward "⇒" nil t)
    (replace-match "==>" nil t))
  (goto-char (point-min))
  (while (search-forward "¬" nil t)
    (replace-match "~" nil t))
  (goto-char (point-min))
  (while (search-forward "⇔" nil t)
    (replace-match "<=>" nil t))
  (goto-char (point-min))
  (while (search-forward "∀" nil t)
    (replace-match "!" nil t))
  (goto-char (point-min))
  (while (search-forward "∃" nil t)
    (replace-match "?" nil t))
  (goto-char (point-min))
  (while (search-forward " ⊂ " nil t)
    (replace-match " SUBSET " nil t))
  (goto-char (point-min))
  (while (search-forward " ∩ " nil t)
    (replace-match " INTER " nil t))
  (goto-char (point-min))
  (while (search-forward " ∪ " nil t)
    (replace-match " UNION " nil t))
  (goto-char (point-min))
  (while (search-forward "∅" nil t)
    (replace-match "{}" nil t))
  (goto-char (point-min))
  (while (search-forward "≅" nil t)
    (replace-match "cong" nil t))
  (goto-char (point-min))
  (while (search-forward " ∈ " nil t)
    (replace-match " IN " nil t))
  (goto-char (point-min))
  (while (search-forward " ━ " nil t)
    (replace-match " DIFF " nil t))
  (goto-char (point-min))
  (while (search-forward " ╪ " nil t)
    (replace-match " INSERT " nil t))
  (goto-char (point-min))
  (while (search-forward "α" nil t)
    (replace-match "alpha" nil t))
  (goto-char (point-min))
  (while (search-forward "β" nil t)
    (replace-match "beta" nil t))
  (goto-char (point-min))
  (while (search-forward "γ" nil t)
    (replace-match "gamma" nil t))
  (goto-char (point-min))
  (while (search-forward " ∡ " nil t)
    (replace-match " angle " nil t))
  (goto-char (point-min))
  (while (search-forward "(∡ " nil t)
    (replace-match "(angle " nil t))
  (goto-char (point-min))
  (while (search-forward " ≢ " nil t)
    (replace-match " not=== " nil t))
  (goto-char (point-min))
  (while (search-forward "∉" nil t)
    (replace-match "NOTIN" nil t))
  (goto-char (point-min))
  (while (search-forward " ≠ " nil t)
    (replace-match " neq " nil t))
  (goto-char (point-min))
  (while (search-forward "λ" nil t)
    (replace-match "\\" nil t))
  (goto-char (point-min))
  (while (search-forward "∥" nil t)
    (replace-match "parallel" nil t))
  (goto-char (point-min))
  (while (search-forward "θ" nil t)
    (replace-match "theta" nil t))
  (goto-char (point-min))
  (while (search-forward "μ" nil t)
    (replace-match "mu" nil t))
  (goto-char (point-min))
  (while (search-forward "→" nil t)
    (replace-match "--->" nil t))
  (goto-char (point-min))
  (while (search-forward " ∏ " nil t)
    (replace-match " prod " nil t))
    (goto-char (point-min))
    (while (search-forward " ∘ " nil t)
      (replace-match " _o_ " nil t))
  (goto-char (point-min)))

(defun Region-math-fonts-removed-for-HOL-Light (bottom top)
  "writes the file joe.ml in which the mathematical characters (∀, ∃, ∩,...) of the region of this file are replaced by HOL Light expressions (!, ?, INTER,...), and makes joe.ml the X-selection."
  (interactive "r")
  (let ((rebuff (current-buffer)))
    ;; (save-current-buffer
    (save-window-excursion
      (find-file "joe.ml")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (insert-buffer-substring rebuff bottom top)
      (Remove-math-fonts-for-HOL-Light)
      (goto-char (point-max))
      (untabify (point-min) (point-max))
      (copy-region-as-kill (point-min) (point-max))
      (save-buffer)
      (kill-buffer "joe.ml"))))

(defun File-math-fonts-removed-for-HOL-Light ()
  "writes the file joe.ml in which the mathematical characters (∀, ∃, ∩,...) of this file are replaced by HOL Light expressions (!, ?, INTER,...), and makes joe.ml the X-selection."
  (interactive)
  (Region-math-fonts-removed-for-HOL-Light (point-min) (point-max)))

;; Assuming the function key F2 is an unbound prefix key in Emacs, and
;; this code binds the keys
;; F2 i,  F2 b (for biconditional) etc 
;; to inserting the symbols (sometimes padded with spaces), as indicated:

(global-set-key '[f2 73]  '(lambda () (interactive) (insert " ⇒ ")))     ;; F2 I
(global-set-key '[f2 98]  '(lambda () (interactive) (insert " ⇔ ")))     ;; F2 b
(global-set-key '[f2 110] '(lambda () (interactive) (insert "¬")))        ;; F2 n
(global-set-key '[f2 111] '(lambda () (interactive) (insert " ∨ ")))     ;; F2 o
(global-set-key '[f2 97]  '(lambda () (interactive) (insert " ∧ ")))     ;; F2 a
(global-set-key '[f2 102] '(lambda () (interactive) (insert "∀ ")))      ;; F2 f
(global-set-key '[f2 69]  '(lambda () (interactive) (insert "∃ ")))      ;; F2 E
(global-set-key '[f2 115] '(lambda () (interactive) (insert " ⊂ ")))     ;; F2 s
(global-set-key '[f2 105] '(lambda () (interactive) (insert " ∈ ")))       ;; F2 i
(global-set-key '[f2 86]  '(lambda () (interactive) (insert " ∪ ")))       ;; F2 V
(global-set-key '[f2 65]  '(lambda () (interactive) (insert " ∩ ")))       ;; F2 A
(global-set-key '[f2 99]  '(lambda () (interactive) (insert " ≅ ")))     ;; F2 c
(global-set-key '[f2 101] '(lambda () (interactive) (insert " ≡ ")))     ;; F2 e
(global-set-key '[f2 78]  '(lambda () (interactive) (insert "∅")))       ;; F2 N
(global-set-key '[f2 100]  '(lambda () (interactive) (insert " ━ ")))       ;; F2 d
(global-set-key '[f2 112]  '(lambda () (interactive) (insert " ╪ ")))       ;; F2 p
(global-set-key '[f2 108]  '(lambda () (interactive) (insert "λ")))       ;; F2 l
(global-set-key '[f2 109]  '(lambda () (interactive) (insert "μ")))       ;; F2 m
(global-set-key '[f2 49]  '(lambda () (interactive) (insert "α")))       ;; F2 1
(global-set-key '[f2 50]  '(lambda () (interactive) (insert "β")))       ;; F2 2
(global-set-key '[f2 51]  '(lambda () (interactive) (insert "γ")))       ;; F2 3
(global-set-key '[f2 52]  '(lambda () (interactive) (insert "θ")))       ;; F2 4
(global-set-key '[f2 53]  '(lambda () (interactive) (insert "φ")))       ;; F2 5
(global-set-key '[f2 125]  '(lambda () (interactive) (insert " ≠ " )))       ;; F2 }
(global-set-key '[f2 123]  '(lambda () (interactive) (insert " ∉ ")))       ;; F2 {
(global-set-key '[f2 48]  '(lambda () (interactive) (insert " ≢ ")))       ;; F2 0
(global-set-key '[f2 57]  '(lambda () (interactive) (insert "∡ ")))       ;; F2 9
(global-set-key '[f2 56]  '(lambda () (interactive) (insert " ≇ ")))       ;; F2 8
(global-set-key '[f2 55]  '(lambda () (interactive) (insert " ∥ ")))       ;; F2 7
(global-set-key '[f2 54]  '(lambda () (interactive) (insert " ∦ ")))       ;; F2 6
(global-set-key '[f2 70]  '(lambda () (interactive) (insert " → ")))       ;; F2 F
(global-set-key '[f2 80]  '(lambda () (interactive) (insert " ∏ ")))       ;; F2 P
(global-set-key '[f2 79]  '(lambda () (interactive) (insert " ∘ ")))       ;; F2 O
(global-set-key '[f2 79]  '(lambda () (interactive) (insert " ∘ ")))       ;; F2 O
(global-set-key '[f2 68]  '(lambda () (interactive) (insert " ◼ ")))       ;; F2 D

;; Two Emacs functions are useful in this context: 
;; (string-to-char "⇒") => 8658
;; (char-to-string 8660) => "⇔"

;; Here's my low-level system using math symbols in HOL-Light/Miz3 .
;; In the Emacs buffer containing math symbols, type 
;;                     M-x remove-math-fonts-for-HOL-Light
;; and then mouse-paste into a terminal window (or Emacs shell)
;; running ocaml/HOL Light/miz3.  The X selection pasted by the mouse
;; is copied to a file joe.ml, which is the original file with the math symbols
;; ∅ etc replaced by into their HOL Light versions {} etc.

;; The command M-x remove-math-fonts-for-HOL-Light will be in the
;; command history, and you can recall it with repeat-complex-command,
;; which I bind to the function key F8 by 
;; (global-set-key [f8] 'repeat-complex-command)

(setq auto-mode-alist (append  `(("ml\\'" . text-mode))
			       auto-mode-alist))
(add-hook 'text-mode-hook 'turn-off-auto-fill)
(add-hook 'text-mode-hook 'turn-on-visual-line-mode)
(add-hook 'text-mode-hook 
	  (lambda ()
		      (setq comment-start "::")))

(setq select-active-regions nil)
(setq mouse-drag-copy-region t)
(setq x-select-enable-primary t)
(setq x-select-enable-clipboard nil)
