(Defun Test0 ()
  (ProveDriver '(( ( ~ E ?x) ( V ?x) (S ?x (f ?x)))
		 ( ( ~ E ?u) ( V ?u) (C (f ?x)))
		 ( (P c))
		 ( (E c))
		 ( (~ S c ?y) (P ?y))
		 ( (~ P ?z) (~ V ?z)))
	       '( (~ p ?w) (~ C ?w))))



(Defun Test1 ()
  (ProveDriver '( ((A)) 
		  ((M))
		  ((~ A) (~ C) (D))
		  ((~ M) (C)))
	       '((~ D))))

(Defun Test2 ()
  (ProveDriver '( ((mother amity betsy))
		  ((~ daughter ?u ?w) (mother ?w ?u))
		  ((daughter cindy betsy))
		  ((~ mother ?x ?y) (~ mother ?y ?z) (grandmother ?x ?z)))
	       '((~ grandmother ?g cindy))))

(Defun Test3()
  (ProveDriver '( ((man marcus))
		  ((prompeian marcus))
		  ((~ prompeian ?x) (roman ?x))
		  ((ruler caesar))
		  ((~ roman ?x) (loyalto ?x caesar) (hate ?x caesar))
		  ((~ man ?x) (~ ruler ?y) (~ trytoassassinate ?x ?y) (~ loyalto ?x ?y))
	                ((trytoassassinate marcus caesar)))
	       '((~ hate marcus caesar))))

(Defun Test4()
  (ProveDriver '( ((B ?x) (~ C ?x) (D ?x))
                  ((C ?x) (~ E ?x))
                  ((C ?x) (~ F ?x))
                  ((G John))
                  ((E Helen))
                  ((G Helen))
                  ((~ D ?x) (A ?x))
                  ((~ G ?x) (~ B ?x))
                  ((H Helen)))
  '((~ A Helen) )))

(Defun Test5()
	 (ProveDriver '( ((dog d))
			 ((owns jack d))
			 ((~ dog ?x) (~ owns ?x ?y) (animallover ?x))
			 ((~ animallover ?z) (~ animal ?w) (~ kills ?z ?w))
			 ((kills jack tuna) (kills curiosity tuna))
			 ((cat tuna))
			 ((~ cat ?u) (animal ?u))) 
	'((~ curiosity kills cat))))









