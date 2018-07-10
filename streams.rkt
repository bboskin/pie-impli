#lang racket


(define car$
  (λ (ls)
    ((car ls))))

(define cdr$
  (λ (ls)
    ((cdr ls))))

(define con$
 (λ (a d)
   (cons (λ () a)
         (λ () d))))