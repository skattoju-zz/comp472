(defun generateAssociationList(inex)
(mapcar #'(lambda(x)(cons x (generateNewVariable x))) (findOldVariables inex)))

(defun findOldVariables(ex &optional varList)
  (if (atom ex)
    (if (isVariable ex)
      (adjoin ex varList)
    varList)
    (findOldVariables (first ex) (findOldVariables (rest ex) varList))))

(defun isVariable(x)
  (and (symbolp x) (equal (char (symbol-name x) 0) #\?)))

(defun generateNewVariable(var) 
  (intern (concatenate 'string (string (gensym "var_")) (string (symbol-name var)))))

(defun renameVariables(expression)
	(sublis (generateAssociationList expression) expression))
