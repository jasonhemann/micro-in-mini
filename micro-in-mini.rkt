#lang racket
(provide (all-defined-out))
(require C311/mk)
(require C311/numbers)

;; Jason Hemann and Dan Friedman
;; An implementation of a microKanren-like language in miniKanren.

;; Right now, this requires the C311 implementation of mK + relational
;; arithmetic suite. However, any implementation with ==, =/=, fresh,
;; conde, symbolo, and not-pairo will work.

;; Building this actually required writing an interpreter in order to
;; properly scope variables. Too, this implementation allows only a
;; single user-defined goal constructor.

;; Variables are tagged lists.
;; Goals are tagged lists.
;; Thunks are tagged lists.
;; Closures are tagged lists.
;; Basically, if you can think of it, it's a tagged list.

(define assoco
  (lambda (ud s o)
    (conde
      ((== s '()) (== #f o))
      ((fresh (a d)
         (== `(,a . ,d) s)
         (fresh (aa ad)
           (== `(,aa . ,ad) a)
           (conde
             ((== aa ud) (== a o))
             ((=/= aa ud) (assoco ud d o)))))))))

(define walko
  (lambda (u s o)
    (conde
      ((not-pairo u) (== u o))
      ((fresh (ua ud)
         (== `(,ua . ,ud) u)
         (conde
           ((== ua 'var)
            (fresh (pr)
              (conde
                ((== pr #f) (== u o) (assoco ud s pr))
                ((fresh (prd)
                   (== `(,ud . ,prd) pr)
                   (assoco ud s pr)
                   (walko prd s o))))))
           ((=/= ua 'var) (== u o))))))))

(define unifyo
  (lambda (u^ v^ s o)
    (fresh (u v)
      (walko u^ s u)
      (walko v^ s v)
      (conde
        ((fresh (ua ud)
           (== u `(,ua . ,ud))
           (conde
             ((== ua 'var)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== va 'var)
                      (conde
                        ((== ud vd) (== s o))
                        ((=/= ud vd) (== `((,ud . ,v) . ,s) o))))
                     ((=/= va 'var) (== `((,ud . ,v) . ,s) o)))))
                ((not-pairo v) (== `((,ud . ,v) . ,s) o))))
             ((=/= ua 'var)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== va 'var) (== `((,vd . ,u) . ,s) o))
                     ((=/= va 'var) 
                      (conde
                        ((fresh (s^)
                           (== s^ #f)
                           (== #f o)
                           (unifyo ua va s s^)))
                        ((fresh (s^)
                           (=/= s^ #f)
                           (unifyo ua va s s^)
                           (unifyo ud vd s^ o))))))))
                ((not-pairo v) (== #f o)))))))
        ((not-pairo u)
         (conde
           ((fresh (va vd)
              (== `(,va . ,vd) v)
              (conde
                ((== va 'var) (== o `((,vd . ,u) . ,s)))
                ((=/= va 'var) (== #f o)))))
           ((not-pairo v)
            (conde
              ((== u v) (== s o))
              ((=/= u v) (== #f o))))))))))

(define mpluso
  (lambda ($1 $2 o)
    (conde
      ((== '() $1) (== $2 o))
      ((fresh (a d)
         (== `(,a . ,d) $1)
         (conde
           ((== a 'th) (== `(th mplus ,$1 ,$2) o))
           ((=/= a 'th)
            (fresh ($res)
              (== `(,a . ,$res) o)
              (mpluso d $2 $res)))))))))

(define run-goalo
  (lambda (g s c o)
    (conde  
      [(fresh (u v env)
         (== g `(==-g ,u ,v ,env))
         (conde
           ((fresh (s^)
              (== s^ #f)
              (== o '())
              (fresh (u^ v^)
                (microo u env u^)
                (microo v env v^)
                (unifyo u^ v^ s s^))))
           ((fresh (s^)
              (== o `((,s^ . ,c)))
              (=/= s^ #f)
              (fresh (u^ v^)
                (microo u env u^)
                (microo v env v^)
                (unifyo u^ v^ s s^))))))]
      [(fresh (f env)
         (== g `(call/fresh-g ,f ,env))
         (fresh (x body env^)
           (microo f env `(closure ,x ,body ,env^))
           (fresh (g^ c+)
             (microo body `(,x (reg (var . ,c)) ,env^) g^)
             (pluso c (build-num 1) c+)
             (run-goalo g^ s c+ o))))]
      [(fresh (g1 g2 env)
         (== g `(conj-g ,g1 ,g2 ,env))
         (fresh (g1v g2v)
           (microo g1 env g1v)
           (microo g2 env g2v)
           (fresh ($)
             (run-goalo g1v s c $)
             (bindo $ g2v o))))]
      [(fresh (g1 g2 env)
         (== g `(disj-g ,g1 ,g2 ,env))
         (fresh (g1v g2v)
           (microo g1 env g1v)
           (microo g2 env g2v)
           (fresh ($1 $2)
             (run-goalo g1v s c $1)
             (run-goalo g2v s c $2)
             (mpluso $1 $2 o))))]
      [(fresh (rand env)
         (== g `(top-g ,rand ,env))
         (== `(th top ,env ,rand ,s ,c) o))])))

(define run-tho
  (lambda (th o)
    (fresh (d)
      (== th `(th . ,d))
      (conde 
        [(fresh ($ g)
           (== d `(bind ,$ ,g))
           (fresh ($v)
             (run-tho $ $v)
             (bindo $v g o)))]
        [(fresh ($1 $2)
           (== d `(mplus ,$1 ,$2))
           (fresh ($1v)
             (run-tho $1 $1v)
             (mpluso $2 $1v o)))]
        [(fresh (env rand s c)
           (== d `(top ,env ,rand ,s ,c))
           (fresh (x body env^ randv)
             (microo 'top env `(closure ,x ,body ,env^))
             (microo rand env randv)
             (fresh (g)
               (microo body `(,x (reg ,randv) ,env) g)
               (run-goalo g s c o))))]))))

(define microo
  (lambda (exp env o)
    (conde 
      ((symbolo exp) (apply-envo env exp o))
      ((== #t exp) (== #t o))
      ((== #f exp) (== #f o))
      ((fresh (f)
         (== exp `(call/fresh ,f))
         (== `(call/fresh-g ,f ,env) o)))
      ((fresh (pr)
         (== `(car ,pr) exp)
         (fresh (prva prvd)           
           (microo pr env `(,prva . ,prvd))           
           (== prva o))))
      ((fresh (pr)
         (== exp `(cdr ,pr))
         (fresh (prva prvd)           
           (microo pr env `(,prva . ,prvd))
           (== prvd o))))
      ((fresh (exp2)
         (== `(quote ,exp2) exp)
         (== exp2 o)))
      ((fresh (rand)
         (== `(top ,rand) exp)
         (== `(top-g ,rand ,env) o)))
      ((fresh (rator rand)
         (== `(,rator ,rand) exp)
         (=/= 'call/fresh rator)
         (=/= 'top rator)
         (=/= 'car rator)
         (=/= 'cdr rator)
         (=/= 'quote rator)
         (fresh (x body env^ randv)
           (microo rator env `(closure ,x ,body ,env^))
           (microo rand env randv)
           (microo body `(,x (reg ,randv) ,env^) o))))
      ((fresh (u v)
         (== `(== ,u ,v) exp)
         (== `(==-g ,u ,v ,env) o)))
      ((fresh (g1 g2)
         (== exp `(conj ,g1 ,g2))
         (== o `(conj-g ,g1 ,g2 ,env))))
      ((fresh (g1 g2)
         (== exp `(disj ,g1 ,g2))
         (== o `(disj-g ,g1 ,g2 ,env))))
      ((fresh (a d)
         (== exp `(cons ,a ,d))
         (fresh (av dv)
           (== `(,av . ,dv) o)
           (microo a env av)
           (microo d env dv))))
      ((fresh (x body)
         (== exp `(lambda (,x) ,body))
         (== o `(closure ,x ,body ,env))
         (symbolo x)))
      ((fresh (f x exp2 exp3)
         (== exp `(letrec ((,f (lambda (,x) ,exp2))) ,exp3))
         (symbolo f)
         (symbolo x)
         (microo exp3 `(,f (rec ,x ,exp2) ,env) o))))))

(define apply-envo
  (lambda (env y o)
    (fresh (f b env^)
      (== `(,f ,b ,env^) env)
      (conde
        ((== y f)
         (conde
           ((fresh (x exp2)
              (== `(rec ,x ,exp2) b)
              (microo `(lambda (,x) ,exp2) env o)))
           ((fresh (a)
              (== `(reg ,a) b)
              (== a o)))))
        ((=/= y f) (apply-envo env^ y o))))))

(define bindo
  (lambda ($ g o)
    (conde
      ((== '() $) (== '() o))
      ((fresh (a d)
         (== `(,a . ,d) $)
         (conde
           ((== 'th a) (== `(th bind ,$ ,g) o))
           ((fresh (aa da)
              (== `(,aa . ,da) a)
              (fresh ($1 $2)
                (run-goalo g aa da $1)
                (bindo d g $2)
                (mpluso $1 $2 o))))))))))
