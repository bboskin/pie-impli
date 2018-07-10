#lang racket

(require "mk.rkt")
(require "relational_basics.rkt")

(provide normalizo)

;;;;;;;;;;;;;;;;;;;;;;
;; This file implements
;; Normalization by Evaluation as a relation,
;; to be used the inferencer
;;;;;;;;;;;;;;;;;;;;;;

(define (normalizo ρ τ exp o)
  (fresh (v new-τ)
         (valofo ρ exp v)
         (valofo ρ τ new-τ)
         (read-backo ρ new-τ v o)))

(define (valofo ρ exp v)
  (conde
   ; single-symbol cases
   [(symbolo exp)
    (conde [(varo exp) (conde
                        [(apply-ρ ρ exp v)]
                        [(fresh (τ) (apply-Γ ρ exp τ)
                                (== v `(NEU ,τ (VAR ,exp))))])]
           [(== exp 'Nat) (== v 'NAT)]
           [(== exp 'Atom) (== v 'ATOM)]
           [(== exp 'U) (== v 'UNIVERSE)]
           [(== exp 'zero) (== v 'ZERO)]
           [(== exp 'nil) (== v 'NIL)]
           [(== exp 'vecnil) (== v 'VECNIL)])]
   ; atoms
   [(fresh (s)
           (== exp `(quote ,s))
           (== v `(QUOTE ,s)))]
   ; nats
   [(fresh (n v^)
           (== exp `(add1 ,n))
           (== v `(ADD1 ,v^))
           (valofo ρ n v^))]
   ; λ and Π 
   [(fresh (x b)
           (== exp `(λ (,x) ,b))
           (== v `(LAM ,x (CLOS ,x ,b ,ρ))))]
   [(fresh (x A C v-A)
           (== exp `(Π ([,x ,A]) ,C))
           (== v `(PI ,x ,v-A (CLOS ,x ,C ,ρ)))
           (valofo ρ A v-A))]
   ; list-related
   [(fresh (T v-T)
           (== exp `(List ,T))
           (== v `(LIST ,v-T))
           (valofo ρ T v-T))]
   [(fresh (a d a-v d-v)
           (== exp `(:: ,a ,d))
           (== v `(LIST:: ,a-v ,d-v))
           (valofo ρ a a-v)
           (valofo ρ d d-v))]
   ; vector-related
   [(fresh (E n v-E v-n)
           (== exp `(Vec ,E ,n))
           (== v `(VEC ,v-E ,v-n))
           (valofo ρ E v-E)
           (valofo ρ n v-n))]
   [(fresh (vec vec-v)
           (== exp `(tail ,vec))
           (== v `(TAIL ,vec-v))
           (valofo ρ vec vec-v))]
   [(fresh (vec vec-v)
           (== exp `(head ,vec))
           (== v `(HEAD ,vec-v))
           (valofo ρ vec vec-v))]
   [(fresh (a d a-v d-v)
           (== exp `(vec:: ,a ,d))
           (== v `(VEC:: ,a-v ,d-v))
           (valofo ρ a a-v)
           (valofo ρ d d-v))]
   [(fresh (rator rand rator-v rand-v)
           (not-built-in rator)
           (== exp `(,rator ,rand))
           (== v `(N-App  ,rator-v ,rand-v))
           (valofo ρ rator rator-v)
           (valofo ρ rand rand-v))]
   ;; application
   [(fresh (rator rand rand-v rator-v)
           (not-built-in rator)
           (== exp `(,rator ,rand))
           (valofo ρ rand rand-v)
           (valofo ρ rator rator-v)
           (do-appo rator-v rand-v v)
           )]))

(define (valof-closuro clo α v)
  (conde
   [(fresh (x c ρ ρ^)
           (== clo `(CLOS ,x ,c ,ρ))
           (extend-ρ x α ρ ρ^)
           (valofo ρ^ c v))]
   ))

(define (read-backo Γ τ exp norm)
  (conde
   ;; types
   [(== τ 'UNIVERSE) (read-back-typo Γ exp norm)]
   ;; nat-related
   [(== τ 'NAT)
    (conde
     [(== exp 'ZERO) (== norm 'zero)]
     [(fresh (n norm^)
             (== exp `(ADD1 ,n))
             (== norm `(add1 ,norm^))
             (read-backo Γ 'NAT n norm^))])]
   ;; atom-related
   [(== τ 'ATOM)
    (fresh (s)
           (== exp `(QUOTE ,s))
           (== norm `(quote ,s)))]
   ;; list-related
   [(fresh (E a d)
           (== τ `(LIST ,E))
           (conde
            [(== exp 'NIL) (== norm 'nil)]
            [(== exp `(LIST:: ,a ,d))
             (fresh (norm-a norm-d)
                    (== norm `(:: ,norm-a ,norm-d))
                    (read-backo Γ E a norm-a)
                    (read-backo Γ τ d norm-d))]))]
   ;; vector-related
   [(fresh (E n)
           (== τ `(VEC ,E ,n))
           (conde
            [(== n 'ZERO) (== exp 'VECNIL) (== norm 'vecnil)]
            [(fresh (n-1 h t h-norm t-norm)
                    (== n `(ADD1 ,n-1))
                    (== exp `(VEC:: ,h ,t))
                    (== norm `(vec:: ,h-norm ,t-norm))
                    (read-backo Γ E h h-norm)
                    (read-backo Γ `(VEC ,E ,n-1) t t-norm))]))]
   ;; Π related
   [(fresh (x y c A B τ1 Γ^ exp^ exp-neu)
           (== τ `(PI ,x ,A ,B))
           (conde
            [(== exp `(LAM ,y ,c))]
            [(== y x)])
           (== norm `(λ (,y) ,exp-neu))
           (valof-closuro B `(NEU ,A (VAR ,y)) τ1)
           (extend-env y A Γ Γ^)
           (do-appo exp `(NEU ,A (VAR ,y)) exp^)
           (read-backo Γ^ τ1 exp^ exp-neu))]
   ;; neutrals
   [(fresh (ne A)
           (== exp `(NEU ,A ,ne))
           (read-back-neutralo Γ ne norm))]))

(define (do-appo v-rat v-ran o)
  (conde
   [(fresh (x c)
           (== v-rat `(LAM ,x ,c))
           (valof-closuro c v-ran o))]
   [(fresh (x A c ne)
           (== v-rat `(NEU (PI ,x ,A ,c) ,ne))
           (== o `(N-App ,ne ,v-ran)))]))


(define (read-back-typo Γ exp norm)
  (conde
   [(== exp 'UNIVERSE) (== norm 'U)]
   [(== exp 'NAT) (== norm 'Nat)]
   [(== exp 'ATOM) (== norm 'Atom)]
   [(fresh (T norm-T)
           (== exp `(LIST ,T))
           (== norm `(List ,norm-T))
           (read-back-typo Γ T norm-T))]
   [(fresh (E norm-E norm-n n)
           (== exp `(VEC ,E ,n))
           (== norm `(Vec ,norm-E ,norm-n))
           (read-backo Γ 'NAT n norm-n)
           (read-back-typo Γ E norm-E))]
   [(fresh (x A c Γ^ norm-A norm-C neu exp-C)
           (== exp `(PI ,x ,A ,c))
           (== norm `(Π ([,x ,norm-A]) ,exp-C))
           (read-back-typo Γ A norm-A)
           (extend-env x A Γ Γ^)
           (valof-closuro c `(NEU ,A (VAR ,x)) norm-C)
           (read-back-typo Γ^ norm-C exp-C))]
   [(fresh (ne)
           (== exp `(NEU UNIVERSE ,ne))
           (read-back-neutralo Γ ne norm))]))

(define (read-back-neutralo Γ ne norm)
  (conde
   [(== ne `(VAR ,norm))]
   [(fresh (rat A ran rat-v ran-v)
           (== ne `(N-App ,rat (THE ,A ,ran)))
           (== norm `(,rat-v ,ran-v))
           (read-back-neutralo Γ rat rat-v)
           (read-backo Γ A ran ran-v))]
   #;more-cases))

