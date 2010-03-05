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

; A change by Shaul
; Markovitch to
; avoid renamed
; variables having
; very long names
			 )
  "Replace all variables in x with new ones."
  
(sublis (mapcar #'(lambda (var) (make-binding var (new-variable var new-prefix)))
                  (variables-in x))
          x))

