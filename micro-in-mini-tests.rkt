#lang racket
(require "micro-in-mini.rkt")
(require C311/mk)
(require C311/numbers)
(require rackunit)
(require rackunit/text-ui)

(define file-tests
  (test-suite "Test for micro-interpreter"
    (check-equal? (run* (q) (microo '((lambda (x) x) 'dog) '() q))
                  '(dog))
    (check-equal? (run* (q) (microo '(((lambda (x) (lambda (y) x)) 'cat) 'dog) '() q))
                  '(cat))
    (check-equal? (run 1 (q) (microo '(call/fresh (lambda (x) (== x '()))) '() q))
                  '((call/fresh-g (lambda (x) (== x '())) ())))
    (check-equal? (run 1 (q) (fresh (g) 
                               (microo '(call/fresh (lambda (x) (== x '()))) '() g)
                               (run-goalo g '() (build-num 0) q)))
                  '(((((())) 1))))
    (check-equal? (run 1 (q) (microo '(call/fresh (lambda (x) (== x 'dog))) '() q))
                  '((call/fresh-g (lambda (x) (== x 'dog)) ())))
    (check-equal? (run 1 (q) (fresh (g)
                               (microo '(call/fresh (lambda (x) (== x 'dog))) '() g)
                               (run-goalo g '() (build-num 0) q)))
                  '(((((() . dog)) 1))))
    (check-equal? (run 1 (q) (fresh (g)
                               (microo '(call/fresh (lambda (x) (disj (== x 'dog) (== x 'cat)))) '() g)
                               (run-goalo g '() (build-num 0) q)))
                  '(((((() . dog)) 1) (((() . cat)) 1))))
    
    (check-equal? (run 1 (q) (fresh (g)
                               (microo '(call/fresh (lambda (x) (conj (== x 'dog) (call/fresh (lambda (x)  (== x 'cat)))))) '() g)
                               (run-goalo g '() (build-num 0) q)))
                  '((((((1) . cat) (() . dog)) 0 1))))
    (check-equal? (run 1 (q) 
                       (fresh (g)  
                         (microo '(letrec
                                      ((top
                                        (lambda (x)
                                          (disj
                                           (== x 'dog)
                                           (call/fresh
                                            (lambda (d)
                                              (conj
                                               (== x (cons 'hot d))
                                               (top d))))))))
                                    (call/fresh (lambda (x) (top x)))) '() g)
                         (run-goalo g '() (build-num 0) q)))
                  '((th
                     top
                     (x
                      (reg (var))
                      (top
                       (rec
                        x
                        (disj
                         (== x 'dog)
                         (call/fresh (lambda (d) (conj (== x (cons 'hot d)) (top d))))))
                       ()))
                     x
                     ()
                     (1))))
    (check-equal? (run 1 (q) 
                       (fresh (g th)  
                         (microo '(letrec
                                      ((top
                                        (lambda (x)
                                          (disj
                                           (== x 'dog)
                                           (call/fresh
                                            (lambda (d)
                                              (conj
                                               (== x (cons 'hot d))
                                               (top d))))))))
                                    (call/fresh (lambda (x) (top x)))) '() g)
                         (run-goalo g '() (build-num 0) th)
                         (run-tho th q)))
                  '(((((() . dog)) 1)
                     th
                     mplus
                     (th
                      top
                      (d
                       (reg (var 1))
                       (x
                        (reg (var))
                        (x
                         (reg (var))
                         (top
                          (rec
                           x
                           (disj
                            (== x 'dog)
                            (call/fresh (lambda (d) (conj (== x (cons 'hot d)) (top d))))))
                          ()))))
                      d
                      ((() hot var 1))
                      (0 1))
                     ())))
    (check-equal? (run 1 (q) 
                       (fresh (g th d)  
                         (microo '(letrec
                                      ((top
                                        (lambda (x)
                                          (disj
                                           (== x 'dog)
                                           (call/fresh
                                            (lambda (d)
                                              (conj
                                               (== x (cons 'hot d))
                                               (top d))))))))
                                    (call/fresh (lambda (x) (top x)))) '() g)
                         (run-goalo g '() (build-num 0) th)
                         (run-tho th `(,q . ,d))))
                  '((((() . dog)) 1)))
    (check-equal? (run 1 (q)
                       (microo
                        '(letrec
                             ((top
                               (lambda (x)
                                 (call/fresh
                                  (lambda (l)
                                    (call/fresh
                                     (lambda (x-d)
                                       (conj
                                        (== x (cons l x-d))
                                        (call/fresh
                                         (lambda (l2)
                                           (call/fresh
                                            (lambda (out)
                                              (conj
                                               (== x-d (cons l2 out))
                                               (disj
                                                (conj (== '() l) (== l2 out))
                                                (call/fresh
                                                 (lambda (a)
                                                   (call/fresh
                                                    (lambda (d)
                                                      (conj
                                                       (== (cons a d) l)
                                                       (call/fresh
                                                        (lambda (res)
                                                          (conj
                                                           (== (cons a res) out)
                                                           (top (cons d (cons l2 res)))))))))))))))))))))))))
                           (call/fresh
                            (lambda (q)
                              (call/fresh
                               (lambda (l)
                                 (call/fresh
                                  (lambda (l2)
                                    (call/fresh
                                     (lambda (out)
                                       (conj
                                        (== (cons l (cons l2 out)) q)
                                        (top q)))))))))))
                        '() q))
                  '((call/fresh-g
                     (lambda (q)
                       (call/fresh
                        (lambda (l)
                          (call/fresh
                           (lambda (l2)
                             (call/fresh
                              (lambda (out) (conj (== (cons l (cons l2 out)) q) (top q)))))))))
                     (top
                      (rec
                       x
                       (call/fresh
                        (lambda (l)
                          (call/fresh
                           (lambda (x-d)
                             (conj
                              (== x (cons l x-d))
                              (call/fresh
                               (lambda (l2)
                                 (call/fresh
                                  (lambda (out)
                                    (conj
                                     (== x-d (cons l2 out))
                                     (disj
                                      (conj (== '() l) (== l2 out))
                                      (call/fresh
                                       (lambda (a)
                                         (call/fresh
                                          (lambda (d)
                                            (conj
                                             (== (cons a d) l)
                                             (call/fresh
                                              (lambda (res)
                                                (conj
                                                 (== (cons a res) out)
                                                 (top (cons d (cons l2 res)))))))))))))))))))))))
                      ()))))
    (check-equal? (run 1 (q) 
                       (fresh (g th d) 
                         (microo
                          '(letrec
                               ((top
                                 (lambda (x)
                                   (call/fresh
                                    (lambda (l)
                                      (call/fresh
                                       (lambda (x-d)
                                         (conj
                                          (== x (cons l x-d))
                                          (call/fresh
                                           (lambda (l2)
                                             (call/fresh
                                              (lambda (out)
                                                (conj
                                                 (== x-d (cons l2 out))
                                                 (disj
                                                  (conj (== '() l) (== l2 out))
                                                  (call/fresh
                                                   (lambda (a)
                                                     (call/fresh
                                                      (lambda (d)
                                                        (conj
                                                         (== (cons a d) l)
                                                         (call/fresh
                                                          (lambda (res)
                                                            (conj
                                                             (== (cons a res) out)
                                                             (top (cons d (cons l2 res)))))))))))))))))))))))))
                             (call/fresh
                              (lambda (q)
                                (call/fresh
                                 (lambda (l)
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== (cons l (cons l2 out)) q)
                                          (top q)))))))))))
                          '() g)
                         (run-goalo g '() (build-num 0) q)))
                  '((th
                     mplus
                     (th
                      top
                      (out
                       (reg (var 1 1))
                       (l2
                        (reg (var 0 1))
                        (l
                         (reg (var 1))
                         (q
                          (reg (var))
                          (top
                           (rec
                            x
                            (call/fresh
                             (lambda (l)
                               (call/fresh
                                (lambda (x-d)
                                  (conj
                                   (== x (cons l x-d))
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== x-d (cons l2 out))
                                          (disj
                                           (conj (== '() l) (== l2 out))
                                           (call/fresh
                                            (lambda (a)
                                              (call/fresh
                                               (lambda (d)
                                                 (conj
                                                  (== (cons a d) l)
                                                  (call/fresh
                                                   (lambda (res)
                                                     (conj
                                                      (== (cons a res) out)
                                                      (top
                                                       (cons d (cons l2 res)))))))))))))))))))))))
                           ())))))
                      q
                      ((() (var 1) (var 0 1) var 1 1))
                      (0 0 1))
                     ())))
    ;; this demonstrates an issue, methinks. Look for q used twice.
    (check-equal? (run 1 (q) 
                       (fresh (g th) 
                         (microo
                          '(letrec
                               ((top
                                 (lambda (x)
                                   (call/fresh
                                    (lambda (l)
                                      (call/fresh
                                       (lambda (x-d)
                                         (conj
                                          (== x (cons l x-d))
                                          (call/fresh
                                           (lambda (l2)
                                             (call/fresh
                                              (lambda (out)
                                                (conj
                                                 (== x-d (cons l2 out))
                                                 (disj
                                                  (conj (== '() l) (== l2 out))
                                                  (call/fresh
                                                   (lambda (a)
                                                     (call/fresh
                                                      (lambda (d)
                                                        (conj
                                                         (== (cons a d) l)
                                                         (call/fresh
                                                          (lambda (res)
                                                            (conj
                                                             (== (cons a res) out)
                                                             (top (cons d (cons l2 res)))))))))))))))))))))))))
                             (call/fresh
                              (lambda (q)
                                (call/fresh
                                 (lambda (l)
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== (cons l (cons l2 out)) q)
                                          (top q)))))))))))
                          '() g)
                         (run-goalo g '() (build-num 0) q)
                         (run-tho th q)))
                  '((th
                     mplus
                     (th
                      top
                      (out
                       (reg (var 1 1))
                       (l2
                        (reg (var 0 1))
                        (l
                         (reg (var 1))
                         (q
                          (reg (var))
                          (top
                           (rec
                            x
                            (call/fresh
                             (lambda (l)
                               (call/fresh
                                (lambda (x-d)
                                  (conj
                                   (== x (cons l x-d))
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== x-d (cons l2 out))
                                          (disj
                                           (conj (== '() l) (== l2 out))
                                           (call/fresh
                                            (lambda (a)
                                              (call/fresh
                                               (lambda (d)
                                                 (conj
                                                  (== (cons a d) l)
                                                  (call/fresh
                                                   (lambda (res)
                                                     (conj
                                                      (== (cons a res) out)
                                                      (top
                                                       (cons d (cons l2 res)))))))))))))))))))))))
                           ())))))
                      q
                      ((() (var 1) (var 0 1) var 1 1))
                      (0 0 1))
                     ())))
    (check-equal? (run 1 (q) 
                       (fresh (g th) 
                         (microo
                          '(letrec
                               ((top
                                 (lambda (x)
                                   (call/fresh
                                    (lambda (l)
                                      (call/fresh
                                       (lambda (x-d)
                                         (conj
                                          (== x (cons l x-d))
                                          (call/fresh
                                           (lambda (l2)
                                             (call/fresh
                                              (lambda (out)
                                                (conj
                                                 (== x-d (cons l2 out))
                                                 (disj
                                                  (conj (== '() l) (== l2 out))
                                                  (call/fresh
                                                   (lambda (a)
                                                     (call/fresh
                                                      (lambda (d)
                                                        (conj
                                                         (== (cons a d) l)
                                                         (call/fresh
                                                          (lambda (res)
                                                            (conj
                                                             (== (cons a res) out)
                                                             (top (cons d (cons l2 res)))))))))))))))))))))))))
                             (call/fresh
                              (lambda (q)
                                (call/fresh
                                 (lambda (l)
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== (cons l (cons l2 out)) q)
                                          (top q)))))))))))
                          '() g)
                         (run-goalo g '() (build-num 0) th)
                         (run-tho th q)))
                  '((((((0 1 1) var 1 1 1)
                       ((0 0 1))
                       ((1 1) var 1 1 1)
                       ((0 1) var 0 1 1)
                       ((1 0 1) (var 0 1) var 1 1)
                       ((1) var 0 0 1)
                       (() (var 1) (var 0 1) var 1 1))
                      0
                      0
                      0
                      1)
                     th
                     mplus
                     (th
                      mplus
                      (th
                       mplus
                       (th
                        mplus
                        (th
                         top
                         (res
                          (reg (var 0 1 0 1))
                          (d
                           (reg (var 1 0 0 1))
                           (a
                            (reg (var 0 0 0 1))
                            (out
                             (reg (var 1 1 1))
                             (l2
                              (reg (var 0 1 1))
                              (x-d
                               (reg (var 1 0 1))
                               (l
                                (reg (var 0 0 1))
                                (x
                                 (reg (var))
                                 (out
                                  (reg (var 1 1))
                                  (l2
                                   (reg (var 0 1))
                                   (l
                                    (reg (var 1))
                                    (q
                                     (reg (var))
                                     (top
                                      (rec
                                       x
                                       (call/fresh
                                        (lambda (l)
                                          (call/fresh
                                           (lambda (x-d)
                                             (conj
                                              (== x (cons l x-d))
                                              (call/fresh
                                               (lambda (l2)
                                                 (call/fresh
                                                  (lambda (out)
                                                    (conj
                                                     (== x-d (cons l2 out))
                                                     (disj
                                                      (conj (== '() l) (== l2 out))
                                                      (call/fresh
                                                       (lambda (a)
                                                         (call/fresh
                                                          (lambda (d)
                                                            (conj
                                                             (== (cons a d) l)
                                                             (call/fresh
                                                              (lambda (res)
                                                                (conj
                                                                 (== (cons a res) out)
                                                                 (top
                                                                  (cons
                                                                   d
                                                                   (cons
                                                                    l2
                                                                    res)))))))))))))))))))))))
                                      ())))))))))))))
                         (cons d (cons l2 res))
                         (((1 1 1) (var 0 0 0 1) var 0 1 0 1)
                          ((0 0 1) (var 0 0 0 1) var 1 0 0 1)
                          ((1 1) var 1 1 1)
                          ((0 1) var 0 1 1)
                          ((1 0 1) (var 0 1) var 1 1)
                          ((1) var 0 0 1)
                          (() (var 1) (var 0 1) var 1 1))
                         (1 1 0 1))
                        ())
                       ())
                      ())
                     ())))
    (check-equal? (run 1 (q) 
                       (fresh (g th d) 
                         (microo
                          '(letrec
                               ((top
                                 (lambda (x)
                                   (call/fresh
                                    (lambda (l)
                                      (call/fresh
                                       (lambda (x-d)
                                         (conj
                                          (== x (cons l x-d))
                                          (call/fresh
                                           (lambda (l2)
                                             (call/fresh
                                              (lambda (out)
                                                (conj
                                                 (== x-d (cons l2 out))
                                                 (disj
                                                  (conj (== '() l) (== l2 out))
                                                  (call/fresh
                                                   (lambda (a)
                                                     (call/fresh
                                                      (lambda (d)
                                                        (conj
                                                         (== (cons a d) l)
                                                         (call/fresh
                                                          (lambda (res)
                                                            (conj
                                                             (== (cons a res) out)
                                                             (top (cons d (cons l2 res)))))))))))))))))))))))))
                             (call/fresh
                              (lambda (q)
                                (call/fresh
                                 (lambda (l)
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== (cons l (cons l2 out)) q)
                                          (top q)))))))))))
                          '() g)
                         (run-goalo g '() (build-num 0) th)
                         (run-tho th `(,q . ,d))))
                  '(((((0 1 1) var 1 1 1)
                      ((0 0 1))
                      ((1 1) var 1 1 1)
                      ((0 1) var 0 1 1)
                      ((1 0 1) (var 0 1) var 1 1)
                      ((1) var 0 0 1)
                      (() (var 1) (var 0 1) var 1 1))
                     0
                     0
                     0
                     1)))
    (check-equal? (run 1 (q) 
                       (fresh (g th a th2 d) 
                         (microo
                          '(letrec
                               ((top
                                 (lambda (x)
                                   (call/fresh
                                    (lambda (l)
                                      (call/fresh
                                       (lambda (x-d)
                                         (conj
                                          (== x (cons l x-d))
                                          (call/fresh
                                           (lambda (l2)
                                             (call/fresh
                                              (lambda (out)
                                                (conj
                                                 (== x-d (cons l2 out))
                                                 (disj
                                                  (conj (== '() l) (== l2 out))
                                                  (call/fresh
                                                   (lambda (a)
                                                     (call/fresh
                                                      (lambda (d)
                                                        (conj
                                                         (== (cons a d) l)
                                                         (call/fresh
                                                          (lambda (res)
                                                            (conj
                                                             (== (cons a res) out)
                                                             (top (cons d (cons l2 res)))))))))))))))))))))))))
                             (call/fresh
                              (lambda (q)
                                (call/fresh
                                 (lambda (l)
                                   (call/fresh
                                    (lambda (l2)
                                      (call/fresh
                                       (lambda (out)
                                         (conj
                                          (== (cons l (cons l2 out)) q)
                                          (top q)))))))))))
                          '() g)
                         (run-goalo g '() (build-num 0) th)
                         (run-tho th `(,a . ,th2))
                         (run-tho th2 `(,q . ,d))))
                  '(((((1 0 1 1) var 0 1 1 1)
                      ((1 1 0 1))
                      ((0 1 0 1) var 0 1 1 1)
                      ((0 1 1) var 1 0 1 1)
                      ((0 0 1 1) (var 0 1 1) var 0 1 0 1)
                      ((1 0 0 1) var 1 1 0 1)
                      ((1 1 1) (var 0 0 0 1) var 0 1 0 1)
                      ((0 0 1) (var 0 0 0 1) var 1 0 0 1)
                      ((1 1) var 1 1 1)
                      ((0 1) var 0 1 1)
                      ((1 0 1) (var 0 1) var 1 1)
                      ((1) var 0 0 1)
                      (() (var 1) (var 0 1) var 1 1))
                     1
                     1
                     1
                     1)))))

(run-tests file-tests)

