;; Mr. Siddhartha Kattoju:
;; We need a function that would perform the last step in resolution - renaming of the variables.
;; e.g.:  when we have initially something like this
;; a) b(x) OR ~c(x) OR d(x)
;; b) g(John)
;; c) c(x) OR ~e(x)
;; then after the call to RenameVariables() we should get results as follows:
;; a') b(x1) OR ~c(x1) OR d(x1)
;; b') g(John)
;; c') c(x3) OR ~e(x3)
;; 
;; You may use either your own counter in order to implement naming scheme, or there is a function
;; "gensym" that produces unique symbol. Furthermore, in latter variant you will need to use function
;; "symbol-name" to convert symbol into string, as well as you may need to use function "concatenate" 
;; in order to create string like this combine "?" and your unique variable name; the format required 
;; for concatenatiation of two strings is "(concatenate 'string "ABC" "CDE")" where "ABC" - string1, 
;; and "CDE" - string2. Finally, you will need to use function "INTERN" to convert your string back to 
;; symbol.

(defun rename-variables (x &optional (new-prefix nil)
;Replace all variables in x with new ones."
(sublis )(mapcar #'(lambda (var (make-binding var (new-variable var new-prefix)))
		(variables-in x)) x))

;; sublis <alist> <expr>
;; alist => association list (cons A' B') 
;; where  A -> (old1 old2 old3)<pattern> B -> (new1 new2 new3)<replace>
;; Replaces every occurrence of <pattern> in <expr> with <replace>


;; mapcar is a function that calls its first argument with each element of its second argument, in turn. 
;; The second argument must be a sequence. 
;; (mapcar '1+ '(2 4 6)) -> (3 5 7)

;; lambda is the symbol for an anonymous function, a function without a name. 
;; Every time you use an anonymous function, you need to include its whole body.

(defun make-binding (var val) (cons var val))

(defparameter *new-variable-counter* 0)
(defparameter *variable-prefix* "?@")
(defun new-variable (var &optional (new-prefix nil))
; Create a new variable.  Assumes user never types variables of form ?X_9"
  (intern (format nil "~A~A_~D" (if (variable? var) "" "?")
                  (if new-prefix *variable-prefix* var) (incf *new-variable-counter*))))

(defun variables-in (exp)
; Return a list of all the variables in EXP."
  (unique-find-anywhere-if #'variable? exp))

(defun unique-find-anywhere-if (predicate tree &optional found-so-far)
  "Return a list of leaves of tree satisfying predicate,
  with duplicates removed."
  (if (atom tree)
      (if (funcall predicate tree)
          (adjoin tree found-so-far)
          found-so-far)
      (unique-find-anywhere-if
        predicate
        (first tree)
        (unique-find-anywhere-if predicate (rest tree)
                                 found-so-far))))

(defun find-anywhere-if (predicate tree)
  "Does predicate apply to any atom in the tree?"  
  (if (atom tree)
      (funcall predicate tree)
      (or (find-anywhere-if predicate (first tree))
          (find-anywhere-if predicate (rest tree)))))

(defun variables-in (exp)
  "Return a list of all the variables in EXP."
  (unique-find-anywhere-if #'variable? exp))

