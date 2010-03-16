;$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
;Funstion tests argument for being variable
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(defun IsVariable(inValue)
;	(format t "inValue=~d~%" inValue)
	;Check if argument is a symbol
	(if (symbolp inValue)
		(progn
			;Check if a first character of a symbol is "?"
			;Return result of comparison
			(string= (symbol-name inValue) "?" :end1 1)
		)
		(progn
			NIL
		)
	)
)
;----------------------------------------------------------------------------------------------------------------------------------------



;$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
;Funstion tests argument for being constant
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(defun IsConstant(inValue)
;	(format t "inValue=~d~%" inValue)
	;Check if argument is a symbol
	(if (symbolp inValue)
		(progn
			;Check if a first character of a symbol is not "?"
			;Return result of comparison
			(not (string= (symbol-name inValue) "?" :end1 1))
		)
		(progn
			NIL
		)
	)
)
;----------------------------------------------------------------------------------------------------------------------------------------




;$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
;Function test if inVariable occurs in inTarget
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(defun IsOccurs(inVariable inTarget)
;	(format t "Variable=~d, Target=~d~%" inVariable inTarget)
	;Check if there are no more elements in inTarget
	(if (null inTarget)
		(progn
				;No occurance found -> retrun NIL
				NIL			
		)
		;Current inTarget is not empty
		(progn
			;Check if inTarget is a list
			(if (listp inTarget)
				;inTarget is list
				(progn
					;Test if first element of inTarget is equal to a symbol in inVariable - the one whos occuarnce is necessary to define
					(if (equal inVariable (car inTarget))
						;Symbol does occur -> return T
						T
						;Yet there is no symbol - continue with tail-recursion
						(IsOccurs inVariable (cdr inTarget))
					)					
				)
				;inTarget is not list
				(progn
					;Compare two symbols from input arguments
					(if (equal inVariable inTarget)
						;Equal -> return T
						T
						;Not equal -> return NIL
						NIL
					)					
				)
			)
		)
	)
)
;----------------------------------------------------------------------------------------------------------------------------------------




;$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
;Function performs partial substitution of a symbol specified in inSubsitute [old/new] in inTarget
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(defun ApplyPartSubstitution(inSubsitute inTarget &optional intResult intTargetStack intResultStack)
;	(format t "Substitute=~d, Target=~d, Result=~d, TargetStack=~d, Resultstack=~d~%" inSubsitute inTarget intResult intTargetStack intResultStack)
	;Terst if target list is exhausted
	(if (null inTarget)
		;List is already exhausted
		(progn
			;Check if target stack list used for processing nested constructs is empty
			(if (null intTargetStack)
				;Target stack list is empty
				(progn
					;Return result
					intResult
				)
				;Target stack list is not empty
				(progn
					;Current inTarget has been exhausted, however there is still elements on a stack
					;Construct resulting list by appending current result to a top element of a result stack list;
					;Remove top of a target stack list
					;Remove top of a result stack list
					;Tail-recourseviley iterate over a top of a target stack;					
					(ApplyPartSubstitution inSubsitute (car intTargetStack) (append (car intResultStack) (list intResult)) (delete (car intTargetStack) intTargetStack) (delete (car intResultStack) intResultStack))
				)
			)				
		)
		;Current target list is not exhausted
		(progn
			;Test if a current first element in target is a nested list
			(if (listp (car inTarget))
				;Current first element is a nested list
				(progn
					;Push the rest of a target (everything located after nested list) on a target stack
					;Push currently accumulated result on a result stack
					;Tail recourively iterate over nested list given empty list as an intial result holder
					(ApplyPartSubstitution inSubsitute (car inTarget) (list) (cons (cdr inTarget) intTargetStack) (cons intResult intResultStack))
				)
				;Current first element is scalar
				(progn
					;Test if current current element in target is equal to the one from substitution list
					(if (equal (car inSubsitute) (car inTarget))
						;Elements are equal						
						(progn
							;Fill result with substitute
							;Tail recursevely iterate over the rest of target
							(ApplyPartSubstitution inSubsitute (cdr inTarget) (append intResult (list (cadr inSubsitute))) intTargetStack intResultStack)
						)
						;Elements are not equal
						(progn							
							;Fill result with current target element
							;Tail recursevely iterate over the rest of target						
							(ApplyPartSubstitution inSubsitute (cdr inTarget) (append intResult (list (car inTarget))) intTargetStack intResultStack)
						)
					)
				)
			)
		)
	)	
)
;----------------------------------------------------------------------------------------------------------------------------------------




;$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
;Main Unify function implemented in accordance with unification algorythm
;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(defun Unify(inE1 inE2 &optional outUnResult (intE1 inE1) (intE2 inE2))
;	(format t "-----------------------------------------------~%")
;	(format t "E1=~d, E2=~d, Result=~d~%" inE1 inE2 outUnResult)
	;Check if both input arguments are empty lists
	(let ((intSigma1) (intSigma2) (intF1) (intF2))
		(if (or (and (null inE1) (null inE2)) (and (IsConstant inE1) (IsConstant inE2)))
			(progn
				;Both are empty or constants
;				(format t "E1&E2 - EMPTY | CONSTANTS~%")
				(if (equal inE1 inE2)
					NIL
					'FAIL
				)
			)
			(progn
				(if (IsVariable inE1)
					(progn
;						(format t "E1 - VARIABLE~%")
						(if (IsOccurs inE1 inE2)
							'FAIL
							(list inE1 inE2)
						)
					)
					(progn
						(if (IsVariable inE2)
							(progn
;								(format t "E2 - VARIABLE~%")
								(if (IsOccurs inE2 inE1)
									'FAIL
									(list inE2 inE1)
								)
							)
							(progn
								(if (or (null inE1) (null inE2))
									(progn
										'FAIL
									)
									(progn
										(setq intSigma1 (Unify (car inE1) (car inE2) outUnResult intE1 intE2))
;										(format t "Sigma1=~d~%" intSigma1)
										(if (eq intSigma1 'FAIL)
											(progn
												'FAIL
											)
											(progn
												(setq intF1 (ApplyPartSubstitution intSigma1 (cdr inE1)))
;												(format t "F1=~d~%" intF1)
												
												(setq intF2 (ApplyPartSubstitution intSigma1 (cdr inE2)))
;												(format t "F2=~d~%" intF2)
												
												(setq intSigma2 (Unify intF1 intF2 outUnResult intE1 intE2))
;												(format t "Sigma1=~d, Sigma2=~d~%" intSigma1 intSigma2)
												(if (eq intSigma2 'FAIL)
													'FAIL
													(progn
														(if (and (not (null intSigma1)) (not (null intSigma2)))
															(progn
																(cons intSigma1 intSigma2)
															)
															(progn
																(if (not (null intSigma1))
																	(progn
																		(list intSigma1)
																	)
																	(progn
																		(if (not (null intSigma2))
																			(progn
																				intSigma2
																			)
																			(progn
																				NIL
																			)
																		)
																	)
																)
															)
														)														
													)
												)
											)									
										)
									)
								)
							)
						)
					)
				)
			)
		)
	)
)
;----------------------------------------------------------------------------------------------------------------------------------------

