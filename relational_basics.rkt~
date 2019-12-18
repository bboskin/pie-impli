#lang racket

(require "mk.rkt")

(require (except-in "basics.rkt" fresh extend-env))

(provide varo
         assvo
         membero
         built-ino
         not-built-in
         extend-env
         extend-ρ
         apply-Γ
         apply-ρ
         subst
         subst/ig
         src->exp
         stx->exp
         src?)

;;;;;;;;;;;;;;;;;
; This file provides helper relations to be used by the type inferencer and
; relational normalizer
(define (membero x ls)
  (condu
   [(fresh (d) (== ls `(,x . ,d)))]
   [(fresh (a d) (== ls `(,a . ,d))
           (membero x d))]))

(define (assvo x ls o)
  (condu
   [(== ls '()) (== o #f)]
   [(fresh (a d ls^)
           (== ls `((,a . ,d) . ,ls^))
           (condu
            [(== a x) (== o `(,a . ,d))]
            [(assvo x ls^ o)]))]))
;;;;;;;;;;;;;;;;
;; Relational Environment Suite
;; (handled in-house, using the given environment by typechecker,
;;  after using read-back)
;;;;;;;;;;;;;;;;

;; typical environment extension with a free (typed) variable
(define (extend-env x τ Γ new-Γ)
  (== new-Γ `((,x (free ,τ)) . ,Γ)))

(define (extend-ρ x v ρ new-ρ)
  (== new-ρ `((,x (val ,v)) . ,ρ)))

;; environment application
(define (apply-Γ Γ x τ)
  (fresh (y assoc Γ^)
         (== Γ `((,y ,assoc) . ,Γ^))
         (conde
          [(== y x) (conde
                     [(== assoc `(free ,τ))]
                     [(== assoc `(claim ,τ))]
                     [(fresh (v) (== assoc `(def ,τ ,v)))])]
          [(apply-Γ Γ^ x τ)])))

(define (apply-ρ ρ x v)
  (fresh (y assoc ρ^)
         (== ρ `((,y ,assoc) . ,ρ^))
         (conde
          [(== y x) (== assoc `(val ,v))]
          [(== y x) (fresh (τ) (== assoc `(def ,τ ,v)))]
          [(apply-ρ ρ^ x v)])))

(define (subst/ig x v exp new)
  (fresh (b)
           (== exp `(λ (,x) ,b))
           (subst x v b new)))

(define (subst x v exp new)
  (conde
   [(== x exp) (== new v)]
   [(symbolo exp) (=/= x exp) (== new exp)]
   [(fresh (n new-n)
           (== exp `(add1 ,n))
           (== new `(add1 ,new-n))
           (subst x v n new-n))]
   [(fresh (E new-E)
           (== exp `(List ,E))
           (== new `(List ,new-E))
           (subst x v E new-E))]
   [(fresh (E n new-E new-n)
           (== exp `(Vec ,E ,n))
           (== new `(Vec ,new-E ,new-n))
           (subst x v E new-E)
           (subst x v n new-n))]
   [(fresh (y A B)
           (== exp `(Π ([,y ,A]) ,B))
           (conde
            [(== x y) (== new exp)]
            [(=/= x y) (fresh (new-A new-B)
                              (== new `(Π ([,y ,new-A]) ,new-B))
                              (subst x v A new-A)
                              (subst x v B new-B))]))]
   [(fresh (y A B)
           (== exp `(Πi ([,y ,A]) ,B))
           (conde
            [(== x y) (== new exp)]
            [(=/= x y) (fresh (new-A new-B)
                              (== new `(Πi ([,y ,new-A]) ,new-B))
                              (subst x v A new-A)
                              (subst x v B new-B))]))]
   [(fresh (y b)
           (== exp `(λ (,y) ,b))
           (conde
            [(== x y) (== new exp)]
            [(=/= x y) (fresh (new-b)
                              (== new `(λ (,y) ,new-b))
                              (subst x v b new-b))]))]))

(define (built-ino s)
  (symbolo s)
  (conde
   [(== s 'U)]
   [(== s 'Atom)]
   [(== s 'Nat)]
   [(== s 'zero)]
   [(== s 'nil)]
   [(== s 'vecnil)]))

(define (not-built-in s)
  (=/= s 'add1)
  (=/= s 'List)
  (=/= s 'quote)
  (=/= s 'head)
  (=/= s 'tail)
  (=/= s '::)
  (=/= s 'Π)
  (=/= s 'λ)
  (=/= s 'vec::))

(define (varo s)
  (symbolo s)
  (=/= s 'U)
  (=/= s 'Atom)
  (=/= s 'Nat)
  (=/= s 'zero)
  (=/= s 'nil)
  (=/= s 'vecnil))


;; conversion from src to Core

(define (src->exp s)
  (stx->exp (src-stx s)))

(define (stx->exp stx)
  (match stx
    [(? symbol?) stx]
    [`(quote ,s) `(quote ,s)]
    [`(the ,τ ,e) `(the ,(src->exp τ) ,(src->exp e))]
    [`(add1 ,n) `(add1 ,(src->exp n))]
    [`(which-Nat ,t ,b ,s) `(which-Nat ,(src->exp t) ,(src->exp b) ,(src->exp s))]
    [`(iter-Nat ,t ,b ,s) `(iter-Nat ,(src->exp t) ,(src->exp b) ,(src->exp s))]
    [`(rec-Nat ,t ,b ,s) `(rec-Nat ,(src->exp t) ,(src->exp b) ,(src->exp s))]
    [`(ind-Nat ,t ,m ,b ,s) `(ind-Nat ,(src->exp t) ,(src->exp m) ,(src->exp b) ,(src->exp s))]
    [`(Pair ,τ-a ,τ-d) `(Pair ,(src->exp τ-a) ,(src->exp τ-d))]
    [`(cons ,a ,d) `(cons ,(src->exp a) ,(src->exp d))]
    [`(car ,pr) `(car ,(src->exp pr))]
    [`(cdr ,pr) `(cdr ,(src->exp pr))]
    [`(-> ,as ... ,final) (foldr (λ (arg ex) `(-> ,(src->exp arg) ,ex)) (src->exp final) as)]
    [`(λ (,xs ...) ,b) (foldr (λ (x ex) `(λ (,(binder-var x)) ,ex)) (src->exp b) xs)]
    [`(Π ,prs ,b) (foldr (λ (pr ex) `(Π ([,(binder-var (car pr)) ,(src->exp (cadr pr))]) ,ex)) (src->exp b) prs)]
    [`(Πi ,prs ,b)  (foldr (λ (pr ex) `(Πi ([,(binder-var (car pr)) ,(src->exp (cadr pr))]) ,ex)) (src->exp b) prs)]
    [`(List ,τ) `(List ,(src->exp τ))]
    [`(:: ,a ,d) `(:: ,(src->exp a) ,(src->exp d))]
    [`(rec-List ,t ,b ,s) `(rec-List ,(src->exp t) ,(src->exp b) ,(src->exp s))]
    [`(ind-List ,t ,m ,b ,s) `(ind-List ,(src->exp t) ,(src->exp m) ,(src->exp b) ,(src->exp s))]
    [`(Vec ,τ ,n) `(Vec ,(src->exp τ) ,(src->exp n))]
    [`(vec:: ,a ,d) `(vec:: ,(src->exp a) ,(src->exp d))]
    [`(head ,v) `(head ,(src->exp v))]
    [`(tail ,v) `(tail ,(src->exp v))]
    [`(ind-Vec ,t ,m ,b ,s) `(ind-Vec ,(src->exp t) ,(src->exp m) ,(src->exp b) ,(src->exp s))]
    [`(,rat ,rans) `(,(src->exp rat) ,(src->exp rans))]
    [else (error "too fancy! (coming from check)")]))