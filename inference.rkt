#lang racket


(require racket/engine
         "mk2.rkt"
         "relational_basics.rkt"
         "normalize.rkt"
         "relational_NbE.rkt"
         (except-in "basics.rkt" fresh extend-env))
(provide solve solve-arg)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Solve-arg: takes a function type wrapped in a Πi,
; and the input type for that function, and generates the output type
; of an application on that argument
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (all-inner-Πi-args exp)
  (match exp
    [`(Πi ([,v ,τ]) ,e)
     (let-values ([(v-tys vars e) (all-inner-Πi-args e)])
       (values (cons `(,v . ,τ) v-tys) (cons v vars) e))]
    [else (values '() '() exp)]))

(define (restore-Πi new-exp old-exp arg fp)
  (match* (new-exp old-exp)
    [(_ (? (λ (x) (eqv? x fp)))) arg]
    [(_ (? symbol?)) new-exp]
    [(`(add1 ,n1) `(add1 ,n2))
     `(add1 ,(restore-Πi n1 n2 arg fp))]
    [(`(List ,e1) `(List ,e2))
     `(List ,(restore-Πi e1 e2 arg fp))]
    [(`(Pair ,A1 ,D1) `(Pair ,A2 ,D2))
     `(Pair ,(restore-Πi A1 A2 arg fp) ,(restore-Πi D1 D2 arg fp))]
    [(`(Vec ,E1 ,n1) `(Vec ,E2 ,n2))
     `(Vec ,(restore-Πi E1 E2 arg fp) ,(restore-Πi n1 n2 arg fp))]
    [(`(-> ,A1 ,B1) `(-> ,A2 ,B2))
     `(Π ([faux-var ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(`(Σ ([,x ,A1]) ,B1) `(Σ ([,y ,A2]) ,B2))
     `(Σ ([,x ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(`(Π ([,x ,A1]) ,B1) `(Π ([,y ,A2]) ,B2))
     `(Π ([,x ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(`(Πi ([,x ,A1]) ,B1) `(Πi ([,y ,A2]) ,B2))
     `(Πi ([,x ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(`(-> ,A1 ,B1) `(Π ([,x ,A2]) ,B2))
     `(Π ([faux-var ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(`(Π ([,x ,A1]) ,B1) `(-> ,A2 ,B2))
     `(Π ([,x ,(restore-Πi A1 A2 arg fp)]) ,(restore-Πi B1 B2 arg fp))]
    [(_ `(Πi ([,x ,A]) ,B))
     `(Πi ([,x ,(restore-Πi A A arg fp)])
          ,(restore-Πi new-exp B arg fp))]
    [(`(Either ,L1 ,R1) `(Either ,L2 ,R2))
     `(Either ,(restore-Πi L1 L2 arg fp)
              ,(restore-Πi R1 R2 arg fp))]
    ;; more non-type expressions
    [(`(the ,T1 ,e1) `(the ,T2 ,e2))
     `(the ,(restore-Πi T1 T2 arg fp)
           ,(restore-Πi e1 e2 arg fp))]
    [(_ `(the ,T2 ,e2))
     `(the ,(restore-Πi T2 T2 arg fp)
           ,(restore-Πi new-exp e2 arg fp))]
    [(`(λ (,x1) ,b1) `(λ (,x2) ,b2))
     `(λ (,x1) ,(restore-Πi b1 b2 arg fp))]
    ; Nat eliminators
    [(`(which-Nat ,t ,b ,s) `(which-Nat ,t1 ,b1 ,s1))
     `(which-Nat ,(restore-Πi t t1 arg fp)
                ,(restore-Πi b b1 arg fp)
                ,(restore-Πi s s1 arg fp))]
    [(`(iter-Nat ,t ,b ,s) `(iter-Nat ,t1 ,b1 ,s1))
     `(iter-Nat ,(restore-Πi t t1 arg fp)
                ,(restore-Πi b b1 arg fp)
                ,(restore-Πi s s1 arg fp))]
    [(`(rec-Nat ,t ,b ,s) `(rec-Nat ,t1 ,b1 ,s1))
     `(rec-Nat ,(restore-Πi t t1 arg fp)
                ,(restore-Πi b b1 arg fp)
                ,(restore-Πi s s1 arg fp))]
    [(`(ind-Nat ,t ,m ,b ,s) `(ind-Nat ,t1 ,m1 ,b1 ,s1))
     `(ind-Nat ,(restore-Πi t t1 arg fp)
               ,(restore-Πi m m1 arg fp)
               ,(restore-Πi b b1 arg fp)
               ,(restore-Πi s s1 arg fp))]
    ;; Lists
    [(`(:: ,a1 ,es1) `(:: ,a2 ,es2))
     `(:: ,(restore-Πi a1 a2 arg fp)
          ,(restore-Πi es1 es2 arg fp))]
    [(`(rec-List ,t ,b ,s) `(rec-List ,t1 ,b1 ,s1))
     `(rec-List ,(restore-Πi t t1 arg fp)
                ,(restore-Πi b b1 arg fp)
                ,(restore-Πi s s1 arg fp))]
    [(`(ind-List ,t ,m ,b ,s) `(ind-List ,t1 ,m1 ,b1 ,s1))
     `(ind-List ,(restore-Πi t t1 arg fp)
                ,(restore-Πi m m1 arg fp)
                ,(restore-Πi b b1 arg fp)
                ,(restore-Πi s s1 arg fp))]
    ;; Vectors
    [(`(vec:: ,a1 ,d1) `(vec:: ,a2 ,d2))
     `(vec:: ,(restore-Πi a1 a2 arg fp)
             ,(restore-Πi d1 d2 arg fp))]
    [(`(head ,v1) `(head ,v2)) `(head ,(restore-Πi v1 v2 arg fp))]
    [(`(tail ,v1) `(tail ,v2)) `(tail ,(restore-Πi v1 v2 arg fp))]
    [(`(ind-Vec ,j ,t ,m ,b ,s) `(ind-Vec ,j1 ,t1 ,m1 ,b1 ,s1))
     `(ind-Vec ,(restore-Πi j j1 arg fp)
               ,(restore-Πi t t1 arg fp)
               ,(restore-Πi m m1 arg fp)
               ,(restore-Πi b b1 arg fp)
               ,(restore-Πi s s1 arg fp))]
    ;; Either
    [(`(left ,e1) `(left ,e2))
     `(left ,(restore-Πi e1 e2 arg fp))]
    [(`(right ,e1) `(right ,e2))
     `(right ,(restore-Πi e1 e2 arg fp))]
    [(`(ind-Either ,t1 ,bl1 ,br1) `(ind-Either ,t2 ,bl2 ,br2))
     `(ind-Either ,(restore-Πi t1 t2 arg fp)
                  ,(restore-Πi bl1 bl2 arg fp)
                  ,(restore-Πi br1 br2 arg fp))]
    ;; Equality
    [(`(= ,X1 ,f1 ,t1) `(= ,X2 ,f2 ,t2))
     `(= ,(restore-Πi X1 X2 arg fp)
         ,(restore-Πi f1 f2 arg fp)
         ,(restore-Πi t1 t2 arg fp))]
    [(`(same ,e1) `(same ,e2))
     `(same ,(restore-Πi e1 e2 arg fp))]
    [(`(symm ,t1) `(symm ,t2))
     `(symm ,(restore-Πi t1 t2 arg fp))]
    [(`(cong ,t1 ,f1) `(cong ,t2 ,f2))
     `(cong ,(restore-Πi t1 t2 arg fp)
            ,(restore-Πi f1 f2 arg fp))]
    [(`(trans ,t1a ,t1b) `(trans ,t2a ,t2b))
     `(trans ,(restore-Πi t1a t2a arg fp)
            ,(restore-Πi t2a t2b arg fp))]
    [(`(ind-= ,t1 ,m1 ,b1) `(ind-= ,t2 ,m2 ,b2))
     `(cong ,(restore-Πi t1 t2 arg fp)
            ,(restore-Πi m1 m2 arg fp)
            ,(restore-Πi b1 b2 arg fp))]
    [(`(,rator1 ,rand1) `(,rator2 ,rand2))
     `(,(restore-Πi rator1 rator2 arg fp)
       ,(restore-Πi rand1 rand2 arg fp))]))

(defrel (make-varso vars ans)
  (condu
   [(== vars '()) (== ans '())]
   [(fresh (x xs a anso) (== vars `(,x . ,xs))
           (make-varso xs anso)
           (== ans `((,x ,a) . ,anso)))]))

;; a newer version, that also takes the argument and formal parameter, and does a substitution
(define (solve-arg τ-rator τ-arg arg)
  (define saved-vars #f)
  (define old #f)
  (define fp #f)
  (define search
    (match τ-rator
      [`(Πi ([,x ,A]) ,B)
       (let-values ([(v-tys vars B) (all-inner-Πi-args τ-rator)])
         (set! saved-vars v-tys)
         (set! old (match B
                     [`(-> ,A ,C) C]
                     [`(Π ([,x ,A]) ,C) (begin (set! fp x) C)]
                     [else #f]))
         (engine (λ (_) (run 1 (o vs)
                             (fresh (y)
                                    (make-varso vars vs)
                                    (unify-types vs 0 B
                                                 `(Π ([,y ,τ-arg]) ,o)
                                                 '() '() #t))))))]))
  (let ([inf (engine-run 5000 search)])
    (define (elim-fresh vars)
      (foldr (λ (v ans)
               (if (not (symbol? v)) (cons v ans)
                   (match (string->list (symbol->string v))
                     [`(#\_ #\. . ,whatever) (cons 'sole ans)]
                     [_ (cons v ans)])))
             '()
             vars))
    (match (engine-result search)
      ['() #f]
      [#f #f]
      [`(((,τ-res ,τ-arg) . ,constrants))
       #:when (not (eqv? 'List τ-res))
       (cons (restore-Πi τ-res old arg fp)
             (elim-fresh (map (λ (x)
                                (restore-Πi x x arg fp))
                              (map cadr τ-arg))))]
      [`((,τ-res ,τ-arg))
       (cons (restore-Πi τ-res old arg fp)
             (elim-fresh (map (λ (x)
                                (restore-Πi x x arg fp))
                              (map cadr τ-arg))))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Solve: takes two types, one of which has an
; implicit argument, and unifies them, if possible
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (solve τ1 τ2)
  (define search
    (match* (τ1 τ2)
      [(`(Πi ([,x1 ,A1]) ,B1) `(Πi ([,x2 ,A2]) ,B2))
       (engine (λ (_) (run 1 (?) (unify-types '() 0 τ1 τ2 '() '()))))]
      [(`(Πi ([,x1 ,A1]) ,B1) _)
       (engine (λ (_) (run 1 (?) (fresh (v) (unify-types
                                             `((,x1 ,v)) 0 B1 τ2 '() '() #f)))))]
      [(_ _) (engine (λ (_) #f))]))
  (let ([inf (engine-run 5000 search)])
    (match (engine-result search)
      [#f #f]
      ['() #f]
      [`(,ans) ans])))

(defrel (unify-types vars lvl e1 e2 xs1 xs2 in-arg-mode?)
  (condu
   ;; Case 1 -- we have a variable we need to unify, and
   ;; the type it needs to be
   [(assvo e1 vars `(,e1 ,e2))]
   ;; Simple base cases
   [(== e1 'U) (== e2 'U)]
   [(== e1 'Atom) (== e2 'Atom)]
   [(fresh (s1) (== e1 `(quote ,s1)) (== e2 `(quote ,s1)))]
   [(== e1 'nil) (== e2 'nil)]
   [(== e1 'vecnil) (== e2 'vecnil)]
   ;; Trivial
   [(== e1 'Trivial) (== e2 'Trivial)]
   [(== e1 'sole) (== e2 'sole)]
   ;; Absurd
   [(== e1 'Absurd) (== e2 'Absurd)]
   [(fresh (t1 m1 t2 m2)
           (== e1 `(ind-Absurd ,t1 ,m1))
           (== e2 `(ind-Absurd ,t2 ,m2))
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl m1 m2 xs1 xs2 in-arg-mode?))]
   ;; Nats
   [(== e1 'Nat) (== e2 'Nat)]
   [(== e1 'zero) (== e2 'zero)]
   [(fresh (n1 n2) (== e1 `(add1 ,n1)) (== e2 `(add1 ,n2))
           (unify-types vars lvl n1 n2 xs1 xs2 in-arg-mode?))]
   [(fresh (target1 base1 step1 target2 base2 step2)
           (== e1 `(which-Nat ,target1 ,base1 ,step1))
           (== e2 `(which-Nat ,target2 ,base2 ,step2))
           (unify-types vars lvl target1 target2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl base1 base2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl base1 base2 xs1 xs2 in-arg-mode?))]
   [(fresh (target1 base1 step1 target2 base2 step2)
           (== e1 `(iter-Nat ,target1 ,base1 ,step1))
           (== e2 `(iter-Nat ,target2 ,base2 ,step2))
           (unify-types vars lvl target1 target2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl base1 base2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl step1 step2 xs1 xs2 in-arg-mode?))]
   [(fresh (target1 base1 step1 target2 base2 step2)
           (== e1 `(rec-Nat ,target1 ,base1 ,step1))
           (== e2 `(rec-Nat ,target2 ,base2 ,step2))
           (unify-types vars lvl target1 target2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl base1 base2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl step1 step2 xs1 xs2 in-arg-mode?))]
   [(fresh (target1 mot1 base1 step1 target2 mot2 base2 step2)
           (== e1 `(ind-Nat ,target1 ,mot1 ,base1 ,step1))
           (== e2 `(ind-Nat ,target2 ,mot1 ,base2 ,step2))
           (unify-types vars lvl target1 target2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl base1 base2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl step1 step2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl mot1 mot2 xs1 xs2 in-arg-mode?))]
   ;; Variables -- either they are the same De Bruijn index, or both unbound
   ;; and are the same symbol
   [(fresh (v1 v2)
           (symbolo e1)
           (symbolo e2)
           (condu
            [(fresh (index)
                    (== v1 `(,e1 . ,index))
                    (== v2 `(,e2 . ,index))
                    (assvo e1 xs1 v1)
                    (assvo e2 xs2 v2))]
            [(== e1 e2)]))]
   ;the
   [(fresh (T1 a1 T2 a2)
           (== e1 `(the ,T1 ,a1))
           (== e2 `(the ,T2 ,a2))
           (unify-types vars lvl T1 T2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?))]
   ;; Pi and Pii Types
   [(fresh (A1 B1)
           (== e1 `(-> ,A1 ,B1))
           (condu
            [(fresh (A2 B2) (== e2 `(-> ,A2 ,B2))
                    (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
                    (unify-types vars lvl B1 B2 xs1 xs2 in-arg-mode?))]
            [(fresh (x A2 B2) (== e2 `(Π ([,x ,A2]) ,B2))
                    (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
                    (unify-types vars lvl B1 B2 xs1 xs2 in-arg-mode?))]))]
   [(fresh (x1 A1 D1 xs1^ xs2^)
           (== e1 `(Π ([,x1 ,A1]) ,D1))
           (condu
            [(fresh (x2 A2 D2) (== e2 `(Π ([,x2 ,A2]) ,D2))
                    (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
                    (condu
                     [(== in-arg-mode? #f) (== xs1^ `((,x1 . ,lvl) . ,xs1))]
                     [(== in-arg-mode? #t) (== xs1^ `((faux-var . ,lvl) . ,xs1))])
                    (condu
                     [(== in-arg-mode? #t) (== x2 x1)]
                     [(== in-arg-mode? #f)])
                    (== xs2^ `((,x2 . ,lvl) . ,xs2))
                    (unify-types vars (add1 lvl) D1 D2 xs1^ xs2^ in-arg-mode?))]
            [(fresh (x2 A2 D2)
                    (== e2 `(-> ,A2 ,D2))
                    (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
                    (unify-types vars lvl D1 D2 xs1 xs2 in-arg-mode?))]))]
   ; when we encounter a Πi:
   ;-- the other expression could also be a Πi, in which case it's easy
   ;-- the other expression could be something else,
   ;   in which case we add unknown variables to our list
   [(fresh (x1 A1 D1)
           (== e1 `(Πi ([,x1 ,A1]) ,D1))
           (condu [(fresh (x2 A2 D2 xs1^ xs2^) (== e2 `(Πi ([,x2 ,A2]) ,D2))
                          (condu [(== in-arg-mode? #t) (== x1 x2)]
                                 [(== in-arg-mode? #f)])
                          (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
                          (== xs1^ `((,x1 . ,lvl) . ,xs1))
                          (== xs2^ `((,x2 . ,lvl) . ,xs2))
                          (unify-types vars (add1 lvl) D1 D2 xs1^ xs2^ in-arg-mode?))]
                  [(unify-types vars lvl D1 e2 xs1 xs2 in-arg-mode?)]))]
   [(fresh (x1 b1 x2 b2 xs1^ xs2^)
           (== e1 `(λ (,x1) ,b1))
           (== e2 `(λ (,x2) ,b2))
           (== xs1^ `((,x1 . ,lvl) . ,xs1))
           (condu
            [(== in-arg-mode? #t) (== x1 x2)]
            [(== in-arg-mode? #f)])
           (== xs2^ `((,x2 . ,lvl) . ,xs2))
           (unify-types vars (add1 lvl) b1 b2 xs1^ xs2^ in-arg-mode?))]
   ;; Sigma Types
   [(fresh (A1 D1 A2 D2)
           (== e1 `(Pair ,A1 ,D1))
           (== e2 `(Pair ,A2 ,D2))
           (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl D1 D2 xs1 xs2 in-arg-mode?))]
   [(fresh (x1 A1 D1 x2 A2 D2 xs1^ xs2^)
           (== e1 `(Σ ([,x1 ,A1]) ,D1))
           (== e2 `(Σ ([,x2 ,A2]) ,D2))
           (unify-types vars lvl A1 A2 xs1 xs2 in-arg-mode?)
           (== xs1^ `((,x1 . ,lvl) . ,xs1))
           (== xs2^ `((,x2 . ,lvl) . ,xs2))
           (unify-types vars (add1 lvl) D1 D2 xs1^ xs2^ in-arg-mode?))]
   [(fresh (a1 d1 a2 d2)
           (== e1 `(cons ,a1 ,d1))
           (== e2 `(cons ,a2 ,d2))
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl d1 d2 xs1 xs2 in-arg-mode?))]
   [(fresh (pr1 pr2)
           (== e1 `(car ,pr1))
           (== e2 `(car ,pr2))
           (unify-types vars lvl pr1 pr2 xs1 xs2 in-arg-mode?))]
   [(fresh (pr1 pr2)
           (== e1 `(cdr ,pr1))
           (== e2 `(cdr ,pr2))
           (unify-types vars lvl pr1 pr2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 d1)
           (== e1 `(car (cons ,a1 ,d1)))
           (unify-types vars lvl a1 e2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 d1)
           (== e1 `(cdr (cons ,a1 ,d1)))
           (unify-types vars lvl d1 e2 xs1 xs2 in-arg-mode?))]
   [(fresh (pr)
           (== e1 `(cons (car ,pr) (cdr ,pr)))
           (unify-types vars lvl pr e2 xs1 xs2 in-arg-mode?))]
   ;; Vectors
   [(fresh (E1 n1 E2 n2) (== e1 `(Vec ,E1 ,n1))
           (== e2 `(Vec ,E2 ,n2))
           (unify-types vars lvl E1 E2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl n1 n2 xs1 xs2 in-arg-mode?))]
   [(fresh (h1 t1 h2 t2) (== e1 `(vec:: ,h1 ,t1))
           (== e2 `(vec:: ,h2 ,t2))
           (unify-types vars lvl h1 h2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?))]
   [(fresh (v1 v2)
           (== e1 `(head ,v1))
           (== e2 `(head ,v2))
           (unify-types vars lvl v1 v2 xs1 xs2 in-arg-mode?))]
   [(fresh (v1 v2)
           (== e1 `(tail ,v1))
           (== e2 `(tail ,v2))
           (unify-types vars lvl v1 v2 xs1 xs2 in-arg-mode?))]
   [(fresh (j1 t1 m1 b1 s1 j2 t2 m2 b2 s2)
           (== e1 `(ind-Vec ,j1 ,t1 ,m1 ,b1 ,s1))
           (== e2 `(ind-Vec ,j2 ,t2 ,m2 ,b2 ,s2))
           (unify-types vars lvl j1 j2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl m1 m2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl b1 b2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl s1 s2 xs1 xs2 in-arg-mode?))]
   ;; Lists
   [(fresh (E1 E2)
           (== e1 `(List ,E1))
           (== e2 `(List ,E2))
           (unify-types vars lvl E1 E2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 d1 a2 d2) (== e1 `(:: ,a1 ,d1))
           (== e2 `(:: ,a2 ,d2))
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl d1 d2 xs1 xs2 in-arg-mode?))]
   [(fresh (t1 b1 s1 t2 b2 s2)
           (== e1 `(rec-List ,t1 ,b1 ,s1))
           (== e2 `(rec-List ,t2 ,b2 ,s2))
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl b1 b2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl s1 s2 xs1 xs2 in-arg-mode?))]
   [(fresh (t1 m1 b1 s1 t2 m2 b2 s2)
           (== e1 `(ind-List ,t1 ,m1 ,b1 ,s1))
           (== e2 `(ind-List ,t2 ,m2 ,b2 ,s2))
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl m1 m2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl b1 b2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl s1 s2 xs1 xs2 in-arg-mode?))]
   ;; Either
   [(fresh (P1 S1 P2 S2)
           (== e1 `(Either ,P1 ,S1))
           (== e2 `(Either ,P2 ,S2))
           (unify-types vars lvl P1 P2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl S1 S2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 a2)
           (== e1 `(left ,a1))
           (== e2 `(left ,a2))
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 a2)
           (== e1 `(right ,a1))
           (== e2 `(right ,a2))
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?))]
   [(fresh (t1 bl1 br1 t2 bl2 br2)
           (== e1 `(ind-Either ,t1 ,bl1 ,br1))
           (== e2 `(ind-Either ,t2 ,bl2 ,br2))
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl bl1 bl2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl br1 br2 xs1 xs2 in-arg-mode?))]
   ;; =
   [(fresh (X1 from1 to1 X2 from2 to2)
           (== e1 `(= ,X1 ,from1 ,to1))
           (== e2 `(= ,X2 ,from2 ,to2))
           (unify-types vars lvl X1 X2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl from1 from2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl to1 to2 xs1 xs2 in-arg-mode?))]
   [(fresh (a1 a2)
           (== e1 `(same ,a1))
           (== e2 `(same ,a2))
           (unify-types vars lvl a1 a2 xs1 xs2 in-arg-mode?))]
   [(fresh (eq1 eq2 f1 f2)
           (== e1 `(cong ,eq1 ,f1))
           (== e2 `(cong ,eq2 ,f2))
           (unify-types vars lvl eq1 eq2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl f1 f2 xs1 xs2 in-arg-mode?))]
   [(fresh (eq1a eq2a eq1b eq2b)
           (== e1 `(trans ,eq1a ,eq1b))
           (== e2 `(trans ,eq2a ,eq2b))
           (unify-types vars lvl eq1a eq2a xs1 xs2 in-arg-mode?)
           (unify-types vars lvl eq1b eq2b xs1 xs2 in-arg-mode?))]
   [(fresh (eq1 eq2 f1 f2)
           (== e1 `(symm ,eq1))
           (== e2 `(symm ,eq2))
           (unify-types vars lvl eq1 eq2 xs1 xs2 in-arg-mode?))]
   [(fresh (t1 m1 b1 t2 m2 b2)
           (== e1 `(ind-= ,t1 ,m1 ,b1))
           (== e1 `(ind-= ,t2 ,m2 ,b2))
           (unify-types vars lvl t1 t2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl m1 m2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl b1 b2 xs1 xs2 in-arg-mode?))]
   ;; Application
   [(fresh (rator1 rand1 rator2 rand2)
           (== e1 `(,rator1 ,rand1))
           (== e2 `(,rator2 ,rand2))
           (unify-types vars lvl rator1 rator2 xs1 xs2 in-arg-mode?)
           (unify-types vars lvl rand1 rand2 xs1 xs2 in-arg-mode?))]))


;; silly function to curry input type -- NOT being used, but i don't feel like deleting it
(define (curry exp)
  (match exp
    [(? symbol?) exp]
    [`(add1 ,n) `(add1 ,(curry n))]
    [`(List ,e) `(List ,(curry e))]
    [`(Vec ,e ,n) `(Vec ,(curry e) ,(curry n))]
    [`(-> ,A ,B) `(-> ,(curry A) ,(curry B))]
    [`(-> ,As ... ,B) (curry-> As (curry B))]
    [`(Π ([,x ,A]) ,B) `(Π ([,x ,(curry A)]) ,(curry B))]
    [`(Π ,args ,B) (curry-Π args (curry B))]
    [`(Πi ([,x ,A]) ,B) `(Πi ([,x ,(curry A)]) ,(curry B))]
    [`(Πi ,args ,B) (curry-Πi args (curry B))]))

(define (curry-> As B)
  (foldr (λ (A b) `(-> ,(curry A) ,b)) B As))
(define (curry-Π args B)
  (foldr (λ (A b)
           (match A [`(,x ,a) `(Π ([,x ,(curry A)]) ,b)]))
         B args))
(define (curry-Πi args B)
  (foldr (λ (A b)
           (match A [`(,x ,a) `(Πi ([,x ,(curry A)]) ,b)]))
         B args))


(define (apply-renaming r exp)
  (match exp
    [(? symbol?) (match (assv exp r)
                   [#f exp]
                   [`(,x . ,y) y])]
    [`(add1 ,n) `(add1 ,(apply-renaming r n))]
    [`(List ,e) `(List ,(apply-renaming r e))]
    [`(Vec ,e ,n) `(Vec ,(apply-renaming r e) ,(apply-renaming r n))]
    [`(-> ,A ,B) `(-> ,(apply-renaming r A) ,(apply-renaming r B))]
    [`(Π ([,x ,A]) ,B) `(Π ([,x ,(apply-renaming r A)]) ,(apply-renaming r B))]
    [`(Πi ([,x ,A]) ,B) `(Πi ([,(apply-renaming r x) ,(apply-renaming r A)]) ,(apply-renaming r B))]))