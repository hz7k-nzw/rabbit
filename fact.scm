(define fact
  (lambda (n)
    (if (= n 0)
	1
	(* n (fact (- n 1))))))

(define fact-iter
  (lambda (n)
    (labels ((fact1 (lambda (m ans)
		      (if (= m 0)
			  ans
			  (fact1 (- m 1)
				 (* m ans))))))
      (fact1 n 1))))
