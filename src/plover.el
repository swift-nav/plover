;;; plover.el --- Plover major mode

;;; Code:

(defvar plover-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [C-c C-l] 'plover-do-foo)
    map)
  "Keymap for `plover-mode`.")

(defvar plover-mode-syntax-table
  (let ((st (make-syntax-table))
        (i 0))

    ;; Default is atom-constituent
    (modify-syntax-entry '(0 . 255) "_   " st)
    ;; Word components
    (modify-syntax-entry '(?0 . ?9) "w   " st)
    (modify-syntax-entry '(?A . ?Z) "w   " st)
    (modify-syntax-entry '(?a . ?z) "w   " st)
    
    ;; Whitespace
    (modify-syntax-entry ?\t "    " st)
    (modify-syntax-entry ?\n ">   " st)
    (modify-syntax-entry ?\r "    " st)
    (modify-syntax-entry ?\s "    " st)

    ;; Delimiters
    (modify-syntax-entry ?\( "()  " st)
    (modify-syntax-entry ?\) ")(  " st)
    (modify-syntax-entry ?\[ "(]  " st)
    (modify-syntax-entry ?\] ")[  " st)
    (modify-syntax-entry ?\{ "(}  " st)
    (modify-syntax-entry ?\} "){  " st)

    ;; Strings
    (modify-syntax-entry ?| "\" 23bn" st)
    (modify-syntax-entry ?\" "\"    " st)
    (modify-syntax-entry ?\\ "\\    " st)

    ;; Quotations
    (modify-syntax-entry ?' "'   " st)
    (modify-syntax-entry ?` "'   " st)
    (modify-syntax-entry ?~ "'   " st)

    ;; Other tokens
    (modify-syntax-entry ?@ "' p " st)
    (modify-syntax-entry ?, ".   " st)
    (modify-syntax-entry ?\; ".   " st)
    (modify-syntax-entry ?# ".  " st)

    ;; pesky regexp
    ;(modify-syntax-entry ?@ "' 1c" st)
    ;(modify-syntax-entry ?/ ">/ 2c" st)

    ;; Comments
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)

    st)
  "Syntax tabel for `plover-mode`.")

(defvar plover-font-lock-keywords
  (eval-when-compile
    (list
     (list
      "\\b\\(def\\(?:\\sw\\|\\s_\\)*\\)[ \t]+\\(\\(?:\\s_\\|\\sw\\)+\\)"
      '(1 font-lock-keyword-face)
      '(2 font-lock-function-name-face))
     ;; (list
     ;;  "\\b\\(\\(?:\\sw\\|\\s_\\)+\\)(\\(?:\\s-\\|.\\)*?)\\s-+=>"
     ;;  '(1 font-lock-function-name-face)
     ;;  )
     ;; (list
     ;;  "\\b\\(\\(?:\\sw\\|\\s_\\)+\\)\\(?:\\s-+\\(?:\\sw\\|\\s_\\)+\\)+\\s-+=>"
     ;;  '(1 font-lock-function-name-face)
     ;;  )
     ;; (list
     ;;  "\\b\\(\\(?:\\sw\\|\\s_\\)+\\)\\s-*=\\_>"
     ;;  '(1 font-lock-variable-name-face)
     ;;  )
     '("\\_<\\(?:import\\|extern\\|static\\|inline\\|struct\\|vec\\|mat\\|for\\|sum\\|in\\|out\\|inout\\|if\\|then\\|else\\|True\\|False\\|Void\\|T\\|_\\|and\\|or\\|not\\|storing\\|assert\\)\\_>" . font-lock-keyword-face)
     '("\\_<error\\_>" . font-lock-warning-face)
;     '("@\\sw+" . font-lock-constant-face)
     '("~" . font-lock-preprocessor-face)
;     '("#" . font-lock-preprocessor-face)
;     '("\\_<\\(?::\\(?:\\s_\\|\\sw\\)+\\)\\_>" 0 font-lock-constant-face)
     '("::\\|:=\\|<-" . font-lock-constant-face)
     '("\\_<\\(?:u8\\|s8\\|u16\\|s16\\|u32\\|s32\\|u64\\|s64\\|float\\|double\\|string\\|bool\\)\\_>" . font-lock-type-face)
     ;;'("\\_<&\\s_+\\_>" 0 font-lock-variable-name-face)
     ))
  "Keyword highlighting specification for `plover-mode`.")

;; plover-imenu-generic-expression
;; plover-outline-regexp

;;;###autoload
(define-derived-mode plover-mode prog-mode "Plover"
  "A major mode for editing Plover code"
  :syntax-table plover-mode-syntax-table
  (setq-local comment-start "-- ")
  (setq-local comment-start-skip "--+\\s*")
  (setq-local font-lock-defaults '(plover-font-lock-keywords))
  (setq-local indent-line-function 'plover-indent-line)
  ;;(setq-local imenu-generic-expression plover-imenu-generic-expression)
  ;;(setq-local outline-regexp plover-outline-regexp)
  )

;;; Indentation

(defun plover-brack-vec (s pos)
  "0. bracket char; 1. source pos; 2. same-line bracket column; 3. continuation code (0,1,2)"
  (vector s pos nil 0))
(defun plover-note-char-column (last-brack-line indents column)
  (if (and last-brack-line
           (eq nil (elt (car indents) 2)))
      (aset (car indents) 2 column)))
(defmacro plover-pop (indents)
  `(if (< 1 (length ,indents))
       (pop ,indents)))
(defun plover-note-continuation (indents stuff)
  (cond
   ((eq stuff 0) (aset (car indents) 3 0))
   ((eq stuff 1) (if (eq (elt (car indents) 3) 0)
                     (aset (car indents) 3 1)))
   ((eq stuff 2) (if (not (eq (elt (car indents) 3) 0))
                     (aset (car indents) 3 2)))))

(defun plover-compute-indent (end-point)
  (goto-char (point-min))
  (let ((indents (list (plover-brack-vec 0 (point))))
        (str nil)
        (line-comment nil)
        (comment-depth nil)
        (last-brack-line nil)
        ch)
    (while (and (not (eobp))
                (< (point) end-point))
      (if (eq 0 comment-depth) (setq comment-depth nil))
      (setq ch (char-after)) (forward-char)
      (cond
       (str (cond
             ((eq ch str)  (setq str nil))
             ((eq ch ?\\)  (forward-char))))
       (line-comment (cond
                      ((eq ch ?\n)  (setq line-comment nil))
                      (t 'nothing)))
       (comment-depth (cond
                       ((and (eq ch ?\{) (eq (char-after) ?-))  (incf comment-depth) (forward-char))
                       ((and (eq ch ?-) (eq (char-after) ?\}))  (decf comment-depth) (forward-char))
                       (t 'nothing)))
       ((or (eq ch ?\") (eq ch ?\|))
        (setq str ch)
        (plover-note-char-column last-brack-line indents (- (current-column) 1))
        (plover-note-continuation indents 1)
        (setq last-brack-line nil))
       ((and (eq ch ?-) (eq (char-after) ?-))
        (setq line-comment t)
        (setq last-brack-line nil)
        (forward-char))
       ((and (eq ch ?\{) (eq (char-after) ?-))
        (setq comment-depth 1)
        (setq last-brack-line nil)
        (forward-char))
       ((or (eq ch ?\() (eq ch ?\[) (eq ch ?\{))
        (plover-note-char-column last-brack-line indents (- (current-column) 1))
        (plover-note-continuation indents 1)
        (push (plover-brack-vec ch (point)) indents)
        (setq last-brack-line t))
       ((or (eq ch ?\)) (eq ch ?\]) (eq ch ?\}))
        (plover-pop indents)
        (setq last-brack-line nil))
       ((eq ch ?\n)
        (plover-note-continuation indents 2)
        (setq last-brack-line nil))
       ((or (eq ch ?\;) (eq ch ?\,))
        (plover-note-continuation indents 0))
       ((or (eq ch ?\ ) (eq ch ?\r) (eq ch ?\t))
        'nothing)
       (t
        (plover-note-char-column last-brack-line indents (- (current-column) 1))
        (plover-note-continuation indents 1)
        (setq last-brack-line nil))))
    (let ((de-bracket-pos nil))
      (if (and (not str) (not line-comment) (not comment-depth))
          (while (looking-at "[ \t\r]\\|)\\|}\\|\\]\\|;")
            (unless (looking-at "\\s-\\|;")
              (let ((v (plover-pop indents)))
                (if (and v
                         (elt v 2))
                    (setq de-bracket-pos (elt v 1)))))
            (forward-char)))
      (vector indents
              str
              (or line-comment comment-depth)
              de-bracket-pos))))


(defun plover-indent-line ()
  "Indent current line of Plover code"
  (interactive)
  (let ((savep (> (current-column) (current-indentation)))
        (indent (max (plover-calculate-indentation) 0)))
    (if savep
        (save-excursion (indent-line-to indent))
      (indent-line-to indent))))

(defun plover-calculate-indentation ()
  "Return the column to which the current line should be indented."
  (save-excursion
    (beginning-of-line)
    
    (let* ((state (plover-compute-indent (point)))
           (cont (if (eq 2 (elt (car (elt state 0)) 3))
                     1 0)))
      
      ;;(message "%s" state)
      (cond
       ((elt state 1) (current-indentation))
       ((elt state 2) (current-indentation))
       ((elt state 3)
        (let ((col (save-excursion
                     (goto-char (elt state 3))
                     (current-column))))
          (- col 1)))
       ((eq nil (elt state 0)) 0)
       ((elt (car (elt state 0)) 2)
        (+ (elt (car (elt state 0)) 2) (* c-basic-offset cont)))
       (t  (* c-basic-offset (+ (length (elt state 0)) -1 cont)))))))

(provide 'plover)
;;; plover.el ends here
