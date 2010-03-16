;; Siddhartha Kattoju and Jake Granger
;; Last Modified : 3.14.2010
;; COMP 472 Artificial Intelligence
;; Concordia University, Montreal, QC.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROBLEM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; To develop a Lisp program that implements a resolution-based prover for first-order logic. It must accept a set of clauses in CNF form.
;; and function with the following requirements:
;; 
;;     * Use the unification function (implemented in assignment 2)
;;     * A clause set has to be represented as a list of clauses using the prefix notation from assignment 1, e.g.,
;;       ((NOT A) ((F ?A C) ?B (G 1 3)) ((NOT (F C ?B)) (NOT (G 1 3))))
;;     * For ease of programming you should map the Lisp values T to the logical value T and the Lisp value NIL to the logical value F
;;     * Assume that the input set is syntactically correct and in CNF
;;     * Provide a function prove which
;;           o has 1 parameter: a list representing a clause set,
;;           o returns a list :
;;                 + 1. element represents the satisfiability status of the set of input clauses (either T or NIL)
;;                 + 2. element is a partially ordered list representing the proof tree (clause pair and its resolvent)
;;           o Your function prove must be designed in a way that it can accept sets containing an unlimited number of clauses of arbitrary size. Sentences containing 10-100 clauses must be processed within seconds or a few minutes.
;;     * The program must be
;;           o submitted to your lab instructor in source code and also demonstrated with LispWorks on the lab computers.
;;           o It must be well documented and demonstrated with at least 20 examples of sufficient complexity.
;;           o About 10% of the examples should be satisfiable, the other 90% should be unsatisfiable.
;;           o Your program must be accompanied by a report explaining your chosen approach.
;;           o The report has to contain a reasonable justification why your program is sound, complete, and terminating, and what members of your group contributed to what parts of the project by listing the implemented functions and giving a percentage.
;;     * The use of global variables is only permitted if they are used read-only, e.g., as global settings controlling the behaviour of your proof engine.
;;     * Your function prove ist not allowed to modify its input
;;     * There will be a competition for the fastest resolution-based prover. This will be judged with a set of benchmark problems. The winning group will get extra marks for their project.
;;     * Your program will be judged with reference to soundness, completeness, termination, efficiency (speed), program structure, documentation.
;;     * Your lab instructor will post a set of typical reference problem that you can use to test your system. Your final submission will be evaluated with a set of problems that are different but similar to the posted reference problems.
;; 
;; Tips for the design and implementation
;; 
;;     * Make sure by design that you try out all possible resolvents (completeness)
;;     * Implement a function that selects a suitable pair of clauses for resolution and unification
;;     * Do not try to compute all possible resolutions in a naive way because with 220 = 1048576 up to 240 = 1099511627776 possible combinations you will need a long time with your program
;;     * Remember the various heuristics for selecting clause pairs and controlling search
;;     * Keep in mind that you might have to backtrack depending on your chosen approach
;;     * Design backtracking in a way that commitments are automatically "undone"
;;     * Automatic undoing can be easily implemented via lists and recursion


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This lisp program is a First Order Logic Theorem Prover
;The input is in clause form and the output is either the
;steps of the proof or the claim that can't be proved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                                    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function makes a copy of a list L to Lcp
;using recursion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun copy (L)

       (let ( (Lcp Nil))
       (cond         
             ((null L) (setf Lcp Nil))
             ((atom L) (setf Lcp L))
             (t        (setf Lcp (cons (first L) (copy (rest L))))))))


;; (defun copy (originalList &optional copiedSoFar)
;; 
;; 	(if (null originalList)
;; 		(nil)
;; 		(if (atom originalList)
;; 			(append L copiedSoFar)
;; 			(copy( (first originalList) copy(rest original list)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Define the structure of a node which records one step of resolving
;that leads to the proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct Node 
   resolvent	;clause derived from resolution
   clause1	;clauses that were resolved		
   clause2
  subst)	;substitution list used by the resolution     



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function --> checks if a clause has been recorded.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun inrecord (clause)

   (let ((thenode nil))
       (do ((i (- (length record) 1) (setf i (- i 1))))
           ((= i -1)) ;; iterates over the recorded steps.

           (setf thenode (make-Node :resolvent (Node-resolvent (nth i record))
                                    :clause1   (Node-clause1 (nth i record))
                                    :clause2   (Node-clause2 (nth i record))
                                    :subst     (Node-subst (nth i record))))


           (if (equal clause (Node-resolvent thenode)) 
               (return-from inrecord  thenode))) ;; if a match is found
						 ;;returns matching clause

        nil)) ;;returns nil if no match is found.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function trace the record list and prints out every 
;step taken in the proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun trace-solution (record clause)

    (let ( (thenode Nil))
       (cond
            ( (setf thenode (inrecord clause))   
              ;if the clause is a resolvent, recurse its two clauses       
              (trace-solution record (Node-clause1 thenode))
              (trace-solution record (Node-clause2 thenode))
			  (setf step (+ step 1))
              (format T " ===step ~d ===: ~% ~s + ~s using ~s = ~s ~%"
                     step (Node-clause1 thenode) (Node-clause2 thenode)
                    (Node-subst thenode) (Node-resolvent thenode)))
            ;if the clause is an input, returns 'back
            (t 'back))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function tests whether two literals are complementary  
;i.e. one positive and one negative literal with the same predicate
;a positive literal is of the form (P t1 .. tn), and a negative 
;literal is of the form (not (P t1 .. tn)) where ti is a First Order term
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun complementary-lits (L1 L2)
	(cond
		((or (atom L1) (atom L2)) Nil)
		((eql 'not (car L1)) (eql (car (cadr L1))  (car L2)))
		((eql 'not (car L2)) (eql (car(cadr L2))  (car L1)))
		(t Nil)))                  
		
		
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function determines whether a logic variable "v" appears 
;anywhere within some arbitrary first order term "term"     
;a term is of the form (f t1 ..tm) where ti is itself a FO term
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;		
(Defun occurs (v term)
	(cond
		((null term) Nil)
		((atom term) (eql v term))
		((atom (car term))  (cond ((eql v (car term)) t)
		                          (t           (occurs v (cdr term)))))
		(t           (or (occurs v occurs(car term)) (occurs v (cdr term))))))                   
		
		

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function determines whether or not two literals are unifiable
;and if so returns the substitution list that unifies them.
;This functions assumes that the literals are complementary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun Unifiable (L1 L2)
	(cond
		((or (atom L1) (atom L2)) 'Fail)
;; if either literal is an atom => fail
		((eql 'not (car L1))  (Unify (cadr L1) L2))
		(t                  (Unify L1 (cadr L2)))))
;; if the car of L1 is NOT
;; => L2 must be the complement as this function is called only after checking
;; therefore unify cdr of one with the other
	
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function returns a substitution list if two literals are 
;unifiable. returns an 'fail is not unifiable. 
;Note that the substitution list is a list of "dotted pairs"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun Unify (L1 L2)    
    
  (prog (Subst s i)
	
	(cond
	 ((or (atom L1) (atom L2))              ; if L1 or L2 are atoms
	  (cond
	   ((eql L1 L2) (return Nil))     ; identical, substitution is nil
	   ((isVariable L1) 
	    (cond                             ; L1 is a logic variable
	     ((Occurs L1 L2) (return 'Fail))  ; L1 occurs in L2, can't unify
	     (t       (return (list (cons L1 L2)))))) ;otherwise,
					              ;L1 binding to L2
	   
	   ((isVariable L2)
	    (cond          ; ditto for L2     
	     ((Occurs L2 L1) (return 'Fail))
	     (t       (return (list (cons L2 L1))))))
	   (t                  (return 'Fail)))) ;otherwise, not unifiable  
	 
	 ((Not (eql (length L1) (length L2))) (return 'Fail)))
	
	(setq Subst Nil i -1)        ; i iterates from 0 to (length L1)-1
	
	
Step4  (setq i(+ 1 i))
	(cond ((= i (length L1)) (return Subst)))	; Termination of loop
	
	(setq S (Unify (nth i L1) (nth i L2)))  ; Unify the ith term
	(cond 
	 ((eql S 'Fail) (return 'Fail))
	 ((not (null S))   
	  (setf L1 (sublis S L1))   ;substitute L1 using S
	  (setf L2 (sublis S L2))   ;substitute L2 using S
	  (setq Subst (append S Subst))))  ;Add S to Subst
	(go Step4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function determines whether an atom is a variable
;We define the form of a variable as ?x
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun isVariable(x)
 (and (symbolp x) (eql (char (symbol-name x) 0) '#\?)))
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function resolve two clauses C1 and C2 having complementary and 
;unifiable literals L1 and L2 with substitution list Subst. 
;return the resolvent C 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun Resolve (C1 C2 index1 index2 Subst)
;;where index1 = position of literal L1 & index2 = position of literal L2

  (setf C nil)                         ;initialize the resolvent C

  (format t "possible resolution .. ~% ~s at position ~s and ~s at position ~s with substitution ~s ~%" C1 index1 C2 index2 Subst)
	
  (do ((i1 0 (setf i1 (+ 1 i1))))      ;apply the substitution to C1
      ((= i1 (length C1)))
	
	(format t "applying substitution ~s to ~b at position ~b ~%" Subst C1 i1)	
      (if (/= i1 index1)		;if not one the complementary term
	  (let ()
;;		(format t "i1 ~s <-- of C1 ~s , index ~s <-- literal 1 ~%" i1 C1 index1)     
		(setf (nth i1 C1) (sublis Subst (nth i1 C1))) 
		(format t "adding ~s to the back of the clause list" (nth i1 C1))
	       	(setf C (cons (nth i1 C1) C))))) ;adding result of substitution to resolvent


  (do ((i2 0 (setf i2 (+ 1 i2))))       ;apply the substitution to C2
      ((= i2 (length C2)))
	
	(format t "applying substitution ~s to ~a at position ~a ~%" Subst C2 i2)
      (if (/= i2 index2)
	  (let ()   
;;              (format t "i2 ~s <-- of C2 ~s , index ~s <-- literal 2 ~%" i2 C2 index2) 
		(setf (nth i2 C2) (sublis Subst (nth i2 C2)))
		(format t "adding ~s to the resolvent ~%" (nth i2 C2)) 
	        (setf C (cons (nth i2 C2) C)))))
  
  (format t "~s is the resolvent ~% ~%" C) C)       ; return the resolvent clause





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;The function checks whether or not there is a pair of literals
;in the two clauses that are unifiable. If not, return 'fail, otherwise
;resolve the two clauses
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun Check (C1 C2)
 
  (let ((i1 0) (i2 0) (L1 Nil) (L2 Nil))
 
    (setf resolvent 'unsolved)
    (do ((i1 0 (setf i1 (+ 1 i1))))  	; loop through C1
	((= i1 (length C1)))
 

	(if (Not (eq resolvent 'unsolved))   
	    (return resolvent))		;complementary and unifiable 
					;literals found	and resolved. 

					;Get out of the function

	(setf L1 (nth i1 C1))           ;nth returns i1th element of C1
	;for each literal in C1

	(do ((i2 0 (setf i2 (+ 1 i2)))) ;loop through C2
	    ((= i2 (length C2)))

	    (setf L2 (nth i2 C2)) 
	    (if (and (complementary-lits L1 L2) 
		     (Not (eql (setf Subst (Unifiable L1 L2)) 'Fail)))
	;; checks if L1 and L2 are complements && ;; check if L1 and L2 are unifiable
	;; if yes proceed with resolution
		
		(let ()
		  (setf C1cp (copy C1))
		  (setf C2cp (copy C2))

			;;To keep C1, C2 unchanged we make copies and then apply resolution.
		  (setf resolvent (Resolve C1cp C2cp i1 i2 Subst))
			;; Resolve is called with Clause1 Clause2 index1 index2 and the Substitution..
			;; where index1 = position of literal L1 & index2 = position of literal L2 
			;; Save the resolvent
			;; save the step by creating a new node in the proof-tree datastructure
		  (setf newnode (make-Node  :resolvent C
					    :clause1   C1
					    :clause2   C2
					    :subst     Subst))
			;; Add the new node to the list
		  (setf record (append record (list newnode)))
		  (return resolvent))
			;;return the resolvent.
	      )))

	;; if not resolvable, return value 'unsolved.
    resolvent))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This is the main procedure which proves the theorem by using
;resolution. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Defun Prover (Clauses)
       
  (let ((i1 0) (i2 0) (C1 Nil) (C2 Nil) )

;; il <--- iterates over the goal + clauses with goal as a parent.
;; i2 <--- iterates over the axioms
(format t "iterating from the back of the clause list ... ~%")
    ;choose the first clause from the end of the list      
    (do ((i1 (- (length Clauses) 1) (setf i1 (- i1 1))))
	((= i1 (- NumOfPre 1)))          
					;inner loop over Clauses for 
					;the choice of C1
	(format t "selected clause # ~s ... ~%" i1)
	(setf C1 (nth i1 Clauses))      ;C1 is from the set of newly
					;generated clauses 
					;choose the second clause from
					;the beginning of the list 
	(format t "looking for a possible resolutions with ~s ~%" (nth i1 Clauses))
	(do ((i2 0 (setf i2 (+ 1 i2)))) 
	    ((= i2 NumOfPre))
					; outer loop over Clauses for the
					; choice of C2
 
	    (setf C2 (nth i2 Clauses))  ;C2 is from the set of axioms

					;check the two clauses to see
					;whether we can resolve them
	(format t "trying to resolve clause ~s with ~s ~%" (nth i1 Clauses) (nth i2 Clauses)) 
	    (setf result (Check C1 C2))
					;if the newly derived resolvent 
					;is identical to someone already
					;in the Clauses, we just go to the
					;next clause without adding it
					;to Clauses and starts all over again 
	    (if (and (Not (eq 'unsolved result))
		     (Not (member result Clauses :test 'equal)))   
					;get out of the function
		(return-from Prover result))))
    (return-from prove 'Fail)))   ; no clause can resolve, can't prove. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Ordering Strategies 11destructive function.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(defvar 1strategy1 1)
;;
;;(defun orderingStrategy(premise strategy)
;;	(cond
;;		((= 1strategy1 1)
;;	;;shortest first.
;;	;;sort the premises in increasing order of
;;	;;their lengths
;;
;;		(setf premise 
;;		(sort premise '(lambda (cl1 cl2) (< (length cl1) (length cl2)))))
;; 
;;		)
;;		((= 1strategy1 2)

;;	)
;; )
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;extracts last clause from a given list of clauses.
;we assume this to be our goal incase a goal is not specified.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun extractGoal (clauses)
	(setf goal (nth (- (length clauses) 1) clauses))
	(return-from extractGoal goal)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;implements shortest first ordering strategy
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun reOrder (clauseList)
		(setf goal (nth (- (length clauseList) 1) clauseList))
		(setf clauseList (remove (nth (- (length clauseList) 1) clauseList) clauseList))
		(setf clauseList 
			(sort clauseList #'(lambda (cl1 cl2) (< (length cl1) (length cl2)))))
		(setf clauseList (append clauseList (list goal)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;This function drives the whole theorem prover
;premises is the set of inputs clauses(axioms)
;negconclusion is the negated conclusion 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun Prove (premise &optional negconclusion)            


;; append the negated conclusion clause to the premises             
	(if (equal nil negconclusion)
		(progn
			(setf negconclusion (extractGoal premise))
			(setf premise (remove (nth (- (length premise) 1) premise) premise))
			(format t "no negated goal supplied ~% assuming last clause ~s to be the negated goal ~%" negconclusion) 	
		)
	)

;; delete duplicates --->
 	(setf premise (remove-duplicates premise))
 	;(format t "~% removing duplicates ... ~% ~s ~%" premise)

;; shortest first ordering strategy
	(setf premise (reOrder premise))
	;(format t "~% sorting clasuses shortest first... ~% ~s ~%" premise)

;; add negated goal to the clause list
	(setf CL (append premise (list negconclusion)))
	;(format t "~% adding the negated goal to the list of clauses... ~% ~s ~%" premise)

;; prune --->
	
 
;; initialise proving engine
  (setf done 0)                    
  (setf NumOfPre (- (length CL) 1)) ;to remember the number of axioms input
  (setf record Nil)                 ;initialize the record list

(setf *gensym-counter* 0)
;;Main prove loop

(loop

	
	(format t "prove interation~s with clauses ~s ~%" (string (gensym ": ")) CL)
   	
	(if (/= *gensym-counter* 0)
		(setf CL (reOrder CL))
	)

	(setf done (Prover CL))
	
	(if (eq done 'Fail)
		(progn
		
		(format t "******* attempting to prove with clause list reveresed ******** ~%")
		
		(setf CL (reOrder CL))
		(setf CL (append CL (list negconclusion)))
		(setf CL (remove-duplicates CL))

		(format t "prove interation~s with clauses ~s ~%" (string (gensym "(reversed): ")) CL)
		(setf done (Prover (reverse CL)))))
	
  	(cond 
    	((eq done 'Fail)  ; terminate with failure to prove
     		(format t "The theorem can't be proved")
		(return (cons nil record))) 

    	((eq done Nil)  	  ;terminate with the proof
     		(print  "I found the proof") 
     		(setf step 0)
		(trace-solution record Nil)
		(format t " ---end of proof--- ~%")		
		(setf R (cons t record)) 
     		(return R))

    	(t	                                      ;no resolvents this iteration
     		(setf CL (append CL (list done)))))))    ;keep on doing on expanded CL

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TEST CASES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Defun ttest0 ()
  (Prove '(( ( ~ E ?x) ( V ?x) (S ?x (f ?x)))
		 ( ( ~ E ?u) ( V ?u) (C (f ?x)))
		 ( (P c))
		 ( (E c))
		 ( (Q c))
		 ( (W c))
		 ( (E c))		
		 ( (R c))
		 ( (~ S c ?y) (P ?y))
		 ( (~ P ?z) (~ V ?z)))
	       '( (~ p ?w) (~ C ?w))))

(Defun ttest1 ()
  (Prove '( ((A)) 
		  ((M))
		  ((~ A) (~ C) (D))
		  ((~ M) (C)))
	       '((~ D))))


(Defun ttest2 ()
  (Prove '( ((mother amity betsy))
		  ((~ daughter ?u ?w) (mother ?w ?u))
		  ((daughter cindy betsy))
		  ((~ mother ?x ?y) (~ mother ?y ?z) (grandmother ?x ?z)))
	       '((~ grandmother ?g cindy))))

(Defun ttest3 ()
  (Prove '( ((man marcus))
		  ((prompeian marcus))
		  ((~ prompeian ?x) (roman ?x))
		  ((ruler caesar))
		  ((~ roman ?x) (loyalto ?x caesar) (hate ?x caesar))
		  ((~ man ?x) (~ ruler ?y) (~ trytoassassinate ?x ?y) (~ loyalto ?x ?y))
	                ((trytoassassinate marcus caesar)))
	       '((~ hate marcus caesar))))

(Defun ttest4 ()
  (Prove '( ((B ?x) (~ C ?x) (D ?x) (~ E ?x))
                  ((C ?x) (~ E ?x))
                  ((C ?x) (~ F ?x))
                  ((G John))
                  ((E Helen))
                  ((G Helen))
                  ((~ D ?x) (A ?x))
                  ((~ G ?x) (~ B ?x))
                  ((H Helen)))
  '((~ A Helen) )))

(Defun ttest5 ()
	 (Prove '( ((dog d))
			 ((owns jack d))
			 ((cat tuna)) 
			 ((~ dog ?y) (~ owns ?x ?y) (animallover ?x))
			 ((~ animallover ?z) (~ animal ?w) (~ kills ?z ?w))
			 ((kills jack tuna) (kills curiosity tuna))
			 ((~ cat ?u) (animal ?u))
			)
	'((~ kills curiosity ?cat))))


(defun test0 ()

	(Prove '())

)

(defun test3 ()

	(Prove '(
		((A a)) 
		((~ A a)))
			)
)

(defun test2 ()

	(Prove '(((A a)) ((~ A b))))
)

(defun test1 ()

	(Prove '(((A ?x)) ((~ (A a)))))
)

(defun test4 ()

	(Prove '(((A a)) ((~ (A ?x)))))
)

(defun test5 ()

	(Prove '(((A ?x)) ((~ (A ?x)))))
)

(defun test5 ()

	(Prove '(((~ a) b) (a) ((~ b))))
)

(defun test6 ()

	(Prove '(((~ (A ?X)) (A (A ?X))) ((A a)) ((~ (A (A (A (A (A (A a))))))))))
)

(defun test7 ()

	(Prove '(((~ (A ?X)) (A (A ?X))) ((A a))))
)

(defun test8 ()

	(Prove '(((~ (A ?X)) (A (A ?X))) ((A a))  ((~ (B ?X)) (B (B ?X))) ((B b)) ((~ (A (A (A (A (A (A a))))))))))
)

(defun test9 ()

	(Prove '(((~ (A ?x)) (B ?x)) ((A ?y)) ((~ (B ?z)) (A ?z))))
)

(defun test10 ()

	(Prove '(((~ (A ?x)) (B ?x)) ((A ?y)) ((~ (B ?z)) (C ?z)) ((~ (C ?k)) (D ?k)) ((~ (D ?l)) (A ?l)) ))
)

(defun test11 ()

	(Prove '(((~ a) (~ b)) (a b)))
)

(defun test12 ()

	(Prove '(((~ a) (~ b)) (a b) ((~ a) b)  ((~ b) a)))
	
)	
	;test15 is unsat

(defun test13 ()
	(Prove '(
	((~ (b bf)))
		((b bm))
	((~ (b ba)))
	((o bf f))
		((o bm m))
		((o ba a))
		((~ (a ?x)) (~ (o ?x h)) (~ (o ?x l)))
		((s a f))
		((s a m))
		((s m h))
		((s m l))
		( (~ (s ?y ?z)) (~ (s ?x ?y)) (s ?x ?z))
		((b ?x) (a ?x))
		((~ (o ?x ?y)) (~ (s ?y ?z)) (o ?x ?z))
		;((~ (s ?y ?z)))
	))
)	
	
	;;;;  to get more test-cases, you might randomly remove clauses from a 
	;;;;  certain unsat-test-case to get another sat-test-case. 
	;;;;  ---> in a way like or is a game to find the Set-Of-Support???!!!
	
(defun test14 ()
	
	;test16 is unsat
	(Prove  
	'(((S ?x1) (M ?x1))
	((~ (M ?x2))  (~ (L ?x2 Rain)))
	((~ (S ?x3)) (L ?x3 Snow)) 
	((~ (L Tony ?x4))  (~ (L Ellen ?x4)))
	((L Tony  ?x5)  (L Ellen ?x5))
	((L Tony  Rain))
	((L Tony  Snow))
	((~ (M ?x7)) (S ?x7))))
	
)	

(defun test15 ()
	
	;test17 is  unsat
	(Prove 
	'(((lives  agatha))
	((lives  butler))
	((lives  charles))
	((killed agatha agatha) (killed butler agatha) (killed charles agatha)) 
	((~ (killed ?x ?y)) (hates ?x ?y))
	((~ (killed ?x ?y)) (~ (richer ?x ?y)))
	((~ (hates agatha ?x))   (~ (hates charles ?x))) 
	((hates agatha agatha))
	((hates agatha charles))
	((~ (lives ?x))  (~ (richer ?x agatha))  (hates butler ?x))
	((~ (hates agatha ?x)) (hates butler ?x))       
	((~ (hates ?x agatha))  (~ (hates ?x butler))   (~ (hates ?x charles)))
	((~ (killed agatha agatha))  (~ (killed butler agatha))  (~ (killed charles agatha)))))
)	
	
	;=========================================
	;test18 
	;unsat, 10 clauses
	;=========================================
(defun test16 ()

	(Prove
	'(
	((~ (T b)) (~ (T l)))
	((~ (T b)) (~ (T j)))
	((~ (T l)) (~ (T j)))
	((~ (T ?x)) (~ (H ?x)))
	((T b) (T l) (T j))
	((T l) (H l) (~ (T b)))
	((T j)  (~ (H l)) (T l))
	((T j)  (~ (H l)) (H l))
	((T j)  (~ (H l)) (~ (T b)))
	((T b)  (~ (T l)) (~ (H l)) (T ?x) (T j) )
	))
)	
	
	;=========================================
	;test19 
	;unsat, containing 1 function, 3 clauses
	;=========================================
(defun test17 ()

	(Prove '(
	((~ (P (e ?x ?y))) (~ (P ?x)) (P ?y))
	((P  (e (e ?x ?y) (e (e ?x ?z) (e ?z ?y)))))
	((~  (P (e (e a b) (e (e c b)  (e a c))))))))
	
)	
	;=========================================
	;test20 
	;sat, containing 2 functions, 3 clauses
	;=========================================
(defun test18 ()

	(Prove '(
	((~ (p ?y ?y)) (p a a)   (~ (s (f ?y) a)))
	((s a ?y)  (~ (s ?y (f ?y)))    (q (g ?y) (g ?y)))
	((q b ?y)   (~ (q ?y (g ?y)))    (s b b))))
	
)

(defun test19 ()

	(Prove '(
	((A b c))
	((~ (B ?x ?y)) (~ (A ?x ?y)) (B ?x ?y))
	))
)	

(defun test20 ()
	
	(Prove '(
	((A b c))
	((~ (B ?x ?y)) (~ (A ?x ?y)) (B ?y ?x))
	))
)	
	;=========================================
	;test7 
	;unsat, containing 0 functions, 6 clauses
	;=========================================
(defun test21 ()
	
	(Prove '(((~ (P ?x ?y)) (~ (P ?y ?z)) (P ?x ?z))
	((~ (Q ?x ?y)) (~ (Q ?y ?z)) (Q ?x ?z))
	((~ (Q ?x ?y)) (Q ?y ?x))
	((P ?x ?y) (Q ?x ?y))
	((~ (P a b)))
	((~ (Q c d)))))
)	
	
	;=========================================
	;test8 
	;unsat, containing 1 functions, 10 clauses
	;=========================================
(defun test22 ()

	(Prove 
	'(((~ (A ?x)) (B ?y) (~ (R ?x ?y)))
	((~ (B ?x)) (C ?y) (~ (S ?x ?y))) 
	((~ (C ?x)) (R ?x (f ?x)) )
	((~ (C ?x))  (D (f ?x))) 
	((~ (D ?x)) (~ (C ?y)) (~ (T ?x ?y)) )
	((~ (R ?x ?y)) (T ?y ?x))
	((~ (T ?x ?y)) (R ?y ?x))
	((A a))
	((T e a))
	((S e f))))
	
)
	
	;=========================================
	;test9 
	;unsat, containing 3 functions, 24 clauses
	;=========================================
(defun test23 ()

	(Prove
	'(( (c1 ?x) (~ (c0 ?x)))
	((c0 a))
	((~ (c2 ?x)) (c3 ?y) (~ (invr1 ?x ?y)))
	((~ (c4 ?x)) (c5 ?y) (~ (invr3 ?x ?y)))
	((~ (c5 ?x)) (c6 ?y) (~ (invr2 ?x ?y)))
	((~ (c6 ?x)) (~ (c5 ?y)) (~ (invr1 ?x ?y)))
	((~ (c2 ?x)) (r2 ?x (f ?x)) )
	((~ (c2 ?x)) (c3 (f ?x))) 
	((~ (c3 ?x)) (r3 ?x (g ?x)) )
	((~ (c3 ?x)) (c1 (g ?x))) 
	((~ (c3 ?x)) (c4 (g ?x))) 
	((~ (c1 ?x)) (c2 ?x))
	((~ (c1 ?x)) (c3 ?x))
	((~ (c1 ?x)) (c4 ?x))
	((~ (c1 ?x)) (c5 ?x))
	((~ (c1 ?x)) (c6 ?x))
	((~ (c1 ?x)) (r1 ?x (h ?x)) )
	((~ (c1 ?x)) (c2 (h ?x))) 
	((~ (r1 ?x ?y)) (invr1 ?y ?x))
	((~ (invr1 ?x ?y)) (r1 ?y ?x))
	((~ (r2 ?x ?y)) (invr2 ?y ?x))
	((~ (invr2 ?x ?y)) (r2 ?y ?x))
	((~ (r3 ?x ?y)) (invr3 ?y ?x))
	((~ (invr3 ?x ?y)) (r3 ?y ?x))))
	
)	
	;=========================================
	;test10 
	;unsat, 28 clauses
	;    1 function; 9 constants; 11 predicates     
	;=========================================
(defun test24 ()

	(Prove
	'(((h11 a11 a12))
	((h12 a12 a13))
	((h21 a21 a22))
	((h22 a22 a23))
	((h31 a31 a32))
	((h32 a32 a33))
	((v11 a11 a21))
	((v12 a21 a31))
	((~ (A ?x)) (~ (r ?x ?y)) (A ?y))
	((~ (h11 ?x ?y))  (h ?x ?y))
	((~ (h12 ?x ?y))  (h ?x ?y))
	((~ (h21 ?x ?y))  (h ?x ?y))
	((~ (h22 ?x ?y))  (h ?x ?y))
	((~ (h31 ?x ?y))  (h ?x ?y))
	((~ (h32 ?x ?y))  (h ?x ?y))
	((~ (v11 ?x ?y))  (v ?x ?y))
	((~ (v12 ?x ?y))  (v ?x ?y))
	((~ (v ?x ?y))  (r ?x ?y))
	((~ (h ?x ?y))  (r ?x ?y))
	((~ (A a13)) (~ (A a23)) (~ (A a33)) (B a33))
	((~ (B ?x)) (s ?x (f1 ?x)))
	((~ (B ?x)) (C (f1 ?x)))
	((~ (h ?x ?y)) (~ (s ?y ?z)) (s ?x ?z))
	((~ (v12 ?x ?y)) (~ (s ?y ?z)) (s a23 ?z))
	((~ (v11 ?x ?y)) (~ (s ?y ?z)) (s a13 ?z))
	((~ (s ?x ?y)) (~ (s ?y ?z)) (s ?x ?z))
	((~ (h11 ?x ?y)) (~ (v11 ?x ?z)) (~ (s ?x ?w)) (~ (C ?w))) 
	((A a11))
	))
)	

	; the following two tests are small.
	; they are for special purpose.
	; They check if a system has:
	; (1) minmal redudancy elimination
	; (2) factoring 
	;
	;=========================================
	;test11 
	;sat, 2 clauses,  1 function; 2 literals 
	;=========================================
(defun test25 ()

	(Prove
	'(((~ (p ?x)) (p (f ?x)))
	((p (f ?z)) (~ (p ?z)))))
	
)
	;=========================================
	;test12
	;unsat, 4 clauses, 1 function; 4 literals 
	;=========================================
(defun test27 ()

	(Prove
	'(((~ (p ?x)) (p (g ?x)))
	((p (g ?z)) (~ (p ?z)))
	((Q ?y) (Q ?x))
	((~ (Q ?y)) (~ (Q ?x)))))
)	

(defun test26 ()

	(Prove
		'(
		
		((owns bill a_bmw))
		((owns jack a_ferrari))
		(ferrari a_ferrari)
		(bmw a_bmw)
		((~ owns ?x ?y) (~  bmw ?y) (racing_car_fan ?x))
		((~ racing_car_fan ?x) (~ scratches ?x ?y) (~ car ?y))
		((~ bmw ?x) (car ?x))
		((~ ferrari ?x) (car ?x))
		((scratches joe a_ferrari)(scratches bill a_ferrari))
		((~ scratches bill a_ferrari)(~ scratches joe a_ferrari)) 
		((scratches ?x  a_ferrari))
		
		)
	)
)

(defun test29 ()

	(Prove
		'(
		
		((owns bill a_bmw))
		((owns jack a_ferrari))
		(ferrari a_ferrari)
		(bmw a_bmw)
		((not owns ?x ?y) (not  bmw ?y) (racing_car_fan ?x))
		((not racing_car_fan ?x) (not scratches ?x ?y) (not car ?y))
		((not bmw ?x) (car ?x))
		((not ferrari ?x) (car ?x))
		((scratches joe a_ferrari)(scratches bill a_ferrari))
		((not scratches bill a_ferrari)(not scratches joe a_ferrari)) 
		((scratches ?x  a_ferrari))
		
		)
	)
)

(defun test30 ()

	(Prove
		'(
		
		((owns bill a_bmw))
		((owns jack a_ferrari))
		(ferrari a_ferrari)
		(bmw a_bmw)
		((not(owns ?x ?y)) (not(bmw ?y)) (racing_car_fan ?x))
		((not(racing_car_fan ?x)) (not(scratches ?x ?y)) (not(car ?y)))
		((not(bmw ?x)) (car ?x))
		((not(ferrari ?x)) (car ?x))
		((scratches joe a_ferrari)(scratches bill a_ferrari))
		((not(scratches bill a_ferrari))(not(scratches joe a_ferrari))) 
		((scratches ?x  a_ferrari))
		
		)
	)
)

(defun test31 ()
;not satisfiable..
	(Prove
	'(((h11 a11 a12))
	((h12 a12 a13))
	((h21 a21 a22))
	((h22 a22 a23))
	((h31 a31 a32))
	((h32 a32 a33))
	((v11 a11 a21))
	((v12 a21 a31))
	((not (A ?x)) (not (r ?x ?y)) (A ?y))
	((not (h11 ?x ?y))  (h ?x ?y))
	((not (h12 ?x ?y))  (h ?x ?y))
	((not (h21 ?x ?y))  (h ?x ?y))
	((not (h22 ?x ?y))  (h ?x ?y))
	((not (h31 ?x ?y))  (h ?x ?y))
	((not (h32 ?x ?y))  (h ?x ?y))
	((not (v11 ?x ?y))  (v ?x ?y))
	((not (v12 ?x ?y))  (v ?x ?y))
	((not (v ?x ?y))  (r ?x ?y))
	((not (h ?x ?y))  (r ?x ?y))
	((not (A a13)) (not (A a23)) (not (A a33)) (B a33))
	((not (B ?x)) (s ?x (f1 ?x)))
	((not (B ?x)) (C (f1 ?x)))
	((not (h ?x ?y)) (not (s ?y ?z)) (s ?x ?z))
	((not (v12 ?x ?y)) (not (s ?y ?z)) (s a23 ?z))
	((not (v11 ?x ?y)) (not (s ?y ?z)) (s a13 ?z))
	((not (s ?x ?y)) (not (s ?y ?z)) (s ?x ?z))
	((not (h11 ?x ?y)) (not (v11 ?x ?z)) (not (s ?x ?w)) (not (C ?w))) 
	((A a11))
	))
)	
