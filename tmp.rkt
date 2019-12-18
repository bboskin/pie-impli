PIi LINES FROM TYPECHECKER.RKT

(require/typed "inference.rkt"
               [solve (-> Core Core (U Core #f))]
               [solve-arg (-> Core Core Core (U (Listof Core) #f))])

;; is-type

;;;;;;;;;;;;;;;;;;;;;
      ;; Confirming that Πi is a type
      [`(Πi ((,(binder x-loc x) ,A)) ,B)
       (let ((y (fresh Γ x)))
         (go-on ([A-out (is-type Γ r A)]
                 [A-outv (go (val-in-ctx Γ A-out))]
                 [B-out (is-type (bind-free Γ y A-outv) (extend-renaming r x y) B)])
                (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                       (go `(Πi ((,y ,A-out)) ,B-out)))))]


;; synth
 ;;;;;;;;;;;;;;;;;;;;;;;;;;;
      ;; Synthesizing that Πi is a U
      [`(Πi ((,(binder x-loc x) ,A)) ,B)
       (let ([x^ (fresh Γ x)])
         (go-on ([A-out (check Γ r A 'UNIVERSE)]
                 [B-out (check (bind-free Γ x^
                                          (val-in-ctx Γ A-out))
                               (extend-renaming r x x^)
                               B
                               'UNIVERSE)])
                (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                       (go `(the U (Πi ((,x^ ,A-out)) ,B-out))))))]

;; rator rand of synth

[(PIi x A c)
                 (go-on ((`(the ,t-rand ,rand-out) (synth Γ r rand)))
                        (solve-app (src-loc rator) rator-t t-rand rator-out rand-out))]

;; rator rand ... of synth
[(PIi x A c)
                 (go-on ((`(the ,t-rand ,rand-out) (synth Γ r rand)))
                        (solve-app (src-loc rator) app0-t t-rand app0 rand-out))]


;; definitions above check
(: solve-app (-> Loc Core Core Core Core (Perhaps (List 'the Core Core))))
(define (solve-app loc τ-rator τ-rand rator rand)
  (let ([succeed? (solve-arg τ-rator τ-rand rand)])
    (match succeed?
      [#f (stop loc `("Could not resolve type: " ,τ-rator
                      "as a function expecting: " ,τ-rand))]
      [`(,τi . ,args-found)
       (go `(the ,τi (,(curry-app rator args-found) ,rand)))])))

(: curry-app (-> Core (U Null (Listof Core)) Core))
(define (curry-app rator rands)
  (match rands
    ['() rator]
    [`(,a . ,d) (curry-app `(,rator ,a) d)]))

;; check

;; new λi case
      [`(λi ,b)
       (match tv
         [(PIi y A c)
          (let ((x^ (fresh Γ y)))
            (go-on ((b-out (check (bind-free Γ x^ A)
                                  (extend-renaming r y x^)
                                  b
                                  (val-of-closure c (NEU A (N-var x^))))))
                   (begin ((pie-info-hook) (src-loc e) `(binding-site ,(read-back-type Γ A)))
                          (go `(λ (,x^) ,b-out)))))]
         [else (check Γ r b tv)])]

;; definition below check
(: solve-types (-> Loc Core Core (Perhaps Void)))
(define (solve-types loc τ1 τ2)
  (let ([succeed? (solve τ1 τ2)])
    (if (equal? #f succeed?)
        (stop loc
              `("Could not resolve expected type: " ,τ1 "with synthesized type: " ,τ2))
        (go (void)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FROM NORMALIZE.RKT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; New syntax for Πi
(define-syntax (Πi-type stx)
  (syntax-parse stx
    [(_ () ret) (syntax/loc stx ret)]
    [(_ ((x:id arg-t) b ...) ret)
     (syntax/loc stx
       (PIi 'x arg-t (HO-CLOS (λ (x) (Πi-type (b ...) ret)))))]))



;; clauses in val-of

[`(Πi ((,x ,A)) ,B)
     (let ([A-v (val-of ρ A)])
       (PIi x A-v (FO-CLOS ρ x B)))]

[`(λi ,b) (LAMi (val-of ρ b))]


;; clauses in read-back-type
;; new form for Πi
    [(PIi x A c)
     (let ((A-e (read-back-type Γ A))
           (x^ (fresh Γ x)))
       `(Πi ((,x^ ,A-e))
          ,(let ((Γ/x^ (bind-free Γ x^ A)))
             (read-back-type Γ/x^ (val-of-closure c (NEU A (N-var x^)))))))]

;; clauses in read-back
[((PIi x A c) (LAMi b))
     (let ([x^ (fresh Γ x)])
       `(λi ,(read-back
              (bind-free Γ x^ A)
              (val-of-closure c (NEU A (N-var x^)))
              b)))]
    [((PIi x A c) f)
     (let ((x^ (fresh Γ x)))
       `(λi ,(read-back
              (bind-free Γ x^ A)
              (val-of-closure c (NEU A (N-var x^)))
              (do-ap f (NEU A (N-var x^))))))]

