#lang pie-impli

#|
This file implements proofs about the system of Integers, with standard + and *, (called I)
with a focus and aim to describe details of the system with varyious abstract algebras.

The most interesting algebra, I think,
(and which if nothing else is a great test program for Pie)
is that I is an Integral Domain,
which is to say is a commutative ring where 0 has no proper divisors.
(The 0-divisibility proof was a doosey! Its discovery has a nice story, I think, which I'm going to try to reflect.
|#

#|
This file is organized in a way that attempts to balance similar proofs
being put in the same sections, and definitions/proofs only being introduced
when necessary.

This way, to prevent excess computation while editing the file, just comment out everything below you!
I hope eventually to implement file sharing for Pie, and to re-organize the proofs in a more modular way.

There are 3 versions of this document, written in 3 different implementations of Pie.
 - #lang pie, the language of the Little Typer, which was implemented primarily by David and Dan
 - #lang pie-a-let-mode, a language which adds two features to the book's language, added by Andrew:
     - equational reasoning, with a form used with (equal S s1 #:by rule1->2 s2 ... sk) to create the (= S s1 sk)
     - let bindings
 - #lang pie-impli, a language which includes Andrew's equational reasoning (but I'll keep my left left lambda over using let!),
   and adds a new Pi form that takes implicit arguments.
   This work was done largely during my last semester at IU, as a research project together with Jeremy Siek.
   
    (no guarantees on what it will find, but it cleans up the Algebra work nicely :))

TODOs
   - eliminate all evidence of let from pie-impli
   - add a multi-file system
   - write up document in pie-a-let-mode using lets
   - write up document in pure pie
   - create pie-impli version that actually uses as many implicit arguments as possible
   - do we want to use which-Int?
Enjoy!
|#

#|starting simple...|#

(claim id (Π ([S U]) (-> S S)))
(define id (λ (S x) x))

#|Section 1: What is an Integer? And remind me, what was a Nat?

In this file, to differentiate with proofs and functions on Nats and Integers which we'd like to give similar names,
Lowercased words will be used for functions and proofs involving Nats, and
Capitals for Integers, as much as possible, when the distinction is obvious

|#

;; we can put signs on Nats and create Integers!

(claim Integer U)
(define Integer (Either Nat Nat))
(claim Sign U)
(define Sign (-> Nat Integer))
(claim Negative Sign)
(define Negative (λ (k) (left k)))
(claim Positive Sign)
(define Positive (λ (k) (right k)))

;; Zero is an Integer. There is only one Zero, and it's Positive. This is a choice. It's a good choice.
(claim Zero Integer)
(define Zero (Positive 0))

;; Here is how we write negative 1. You might not like it, but it's sound and worth it. Sometimes we have to make choices.
(claim Negative-One Integer)
(define Negative-One (Negative 0))

;; Here are some more Integers!
(claim One Integer)
(define One (Positive 1))
(claim Ten Integer)
(define Ten (Positive 10))
(claim Negative-Two Integer)
(define Negative-Two (Negative 1))
(claim Negative-Five Integer)
(define Negative-Five (Negative 4))

;; We are going to reason about Integers at least as much as we will reason about Nats.
;; let's give ourselves special eliminators for Integers.

;; we have which-Int, for times when we don't produce a dependent type
(claim which-Int
  (Π ([_ Integer]
      [S U])
    (-> (-> Nat S) (-> Nat S)
        S)))
(define which-Int
  (λ (t S l r)
    (ind-Either t
      (λ (_) S)
      (λ (neg) (l neg))
      (λ (pos) (r pos)))))

;; and we have ind-Int for when we do! It's equivalent to ind-Either, but practices good representation independence.
(claim ind-Int
  (Π ([k Integer]
      [mot (-> Integer U)])
    (-> (Π ([k Nat]) (mot (Negative k)))
        (Π ([k Nat]) (mot (Positive k)))
        (mot k))))
(define ind-Int
  (λ (t m l r)
    (ind-Either t m l r)))

;; A fun fact is that the Nats are ordered! They have successors.
;; The Integers have successors, too (and predecessors), but we don't need to care about that yet.
(claim succ (-> Nat Nat))
(define succ (λ (x) (add1 x)))

;; succ2 will be useful shortly! it's convenient to have it as a typed function, to avoid using 'the' expressions
(claim succ2 (-> Nat Nat))
(define succ2 (λ (x) (add1 (add1 x))))


;; There's a nice correspondance between the Integers and the Nats.
;; Proving this might give us a nice sanity check for the choices we made earlier.
;; If we use the familiar mapping from Integers to Nats where the Nats go to evens and Integers go to odds, we can show
;; this correspondance, and prove that the mappings are one-to-one.

;; Here's how we make a Nat from and Int
(claim Int->Nat (-> Integer Nat))
(define Int->Nat
  (λ (j)
    (which-Int j
      Nat
      (λ (neg)
        (iter-Nat neg 1 succ2))
      (λ (pos)
        (iter-Nat pos 0 succ2)))))

;; To get an Int back from a Nat, we need a correspondant to succ for Integers. 

(claim Succ (-> Integer Integer))
(define Succ
  (λ (k)
    (which-Int k
      Integer
      (λ (neg) (Positive (add1 neg)))
      (λ (pos) (Negative pos)))))

(claim Succ2 (-> Integer Integer))
(define Succ2 (λ (k) (Succ (Succ k))))

;; Now, we can define how to decode our Nat!
(claim Nat->Int (-> Nat Integer))
(define Nat->Int
  (λ (j)
    (iter-Nat j
      (Positive 0)
      Succ)))

;; We have a proposed one-to-one mapping, now, between Integers and Nats.
;; We can prove that it behaves how we want! We prove both directions

(claim Succ-succ-same-neg
  (Π ([k Nat])
    (= Nat (Int->Nat (Succ (Negative k)))
       (succ (Int->Nat (Negative k))))))
(define Succ-succ-same-neg
  (λ (neg)
    (ind-Nat neg
      (λ (neg)
        (= Nat
          (Int->Nat (Succ (Negative neg)))
          (succ (Int->Nat (Negative neg)))))
      (same 2)
      (λ (neg-1 IH)
        (cong IH succ2)))))
(claim Succ-succ-same-pos
  (Π ([k Nat])
    (= Nat (Int->Nat (Succ (Positive k)))
       (succ (Int->Nat (Positive k))))))
(define Succ-succ-same-pos
  (λ (neg)
    (ind-Nat neg
      (λ (neg)
        (= Nat
          (Int->Nat (Succ (Positive neg)))
          (succ (Int->Nat (Positive neg)))))
      (same 1)
      (λ (neg-1 IH)
        (cong IH succ2)))))

(claim Succ-succ-same
  (Π ([k Integer])
    (= Nat (Int->Nat (Succ k))
       (succ (Int->Nat k)))))
(define Succ-succ-same
  (λ (k)
    (ind-Int k
      (λ (k)
        (= Nat
          (Int->Nat (Succ k))
          (succ (Int->Nat k))))
      Succ-succ-same-neg
      Succ-succ-same-pos)))

(claim Nat->Int->Nat-same
  (Π ([k Nat])
    (= Nat (Int->Nat (Nat->Int k)) k)))
(define Nat->Int->Nat-same
  (λ (k)
    (ind-Nat k
      (λ (k) (= Nat (Int->Nat (Nat->Int k)) k))
      (same 0)
      (λ (k-1 IH)
        (equal Nat
          (Int->Nat (Succ (Nat->Int k-1)))
          #:by (Succ-succ-same (Nat->Int k-1))
          (add1 (Int->Nat (Nat->Int k-1)))
          #:by (cong IH succ)
          (add1 k-1))))))

(claim Int->Nat->Int-same
  (Π ([k Integer])
    (= Integer
       (Nat->Int (Int->Nat k))
       k)))
(define Int->Nat->Int-same
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Nat->Int (Int->Nat k)) k))
      (λ (neg)
        (ind-Nat neg
          (λ (neg)
            (= Integer
              (Nat->Int (Int->Nat (Negative neg)))
              (Negative neg)))
          (same (Negative 0))
          (λ (neg-1 IH)
            (cong IH Succ2))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos)
            (= Integer
              (Nat->Int (Int->Nat (Positive pos)))
              (Positive pos)))
          (same (Positive 0))
          (λ (pos-1 IH)
            (cong IH Succ2)))))))

;; So now we're starting to have a nice way to talk about the Integers in terms of Nats.
;; Besides ordering and a bijection, however, an important aspect of both of
;; these sets is equality.
;; We want to be able to say when an alleged claim of
;; Equality on Nats or Integers is Absurd.

;; here is code, as produced in the book, of a description of
;; the consequences of Nat equality.


#|
This table describes the output of use-Nat=

use-Nat=: (-> Nat Nat U)

            zero     (add1 j)
          ____________________
zero    | Trivial |   Absurd
(add1 k)| Absurd  | (= Nat k j

|#

;; Nat=-conseq tells us what to expect
(claim Nat=-conseq (-> Nat Nat U))
(define Nat=-conseq
  (λ (j k)
    (which-Nat j
               (which-Nat k
                          Trivial
                          (λ (_) Absurd))
               (λ (j-1)
                 (which-Nat k
                            Absurd
                            (λ (k-1) (= Nat j-1 k-1)))))))

;; Nat=-conseq GIVES us what we expect when
;; the value in question is literally the same number
(claim Nat=-conseq-same
  (Π ([k Nat])
    (Nat=-conseq k k)))
(define Nat=-conseq-same
  (λ (k)
    (ind-Nat k
      (λ (k) (Nat=-conseq k k))
      sole
      (λ (k-1 IH)
        (same k-1)))))

;; Now, if you tell me that k-j, I can create one for k and k,
;; and use your proof to replace one of the k's for a j.
(claim use-Nat=
  (Π ([j Nat]
      [k Nat])
    (-> (= Nat j k)
      (Nat=-conseq j k))))
(define use-Nat=
  (λ (j k j=k)
    (replace j=k
             (λ (?) (Nat=-conseq j ?))
             (Nat=-conseq-same j))))

;; here's how we can use it!
(check-same (Nat=-conseq 3 (succ 2))
  ((use-Nat= 3 3) (same 3)) (same 2))



#|
Can we make a system like this for Int? We'd like one that started like this
(claim Int=-conseq (-> Integer Integer U))
(define Int=-conseq
  (λ (j k) (which-Int j U ..)))

But, U is not a U, and we don't have a hierarchical universe. so we simply can't
go down that road without changing the logical system.
Is that gonna stop us? Of course not!

Using our isomorphism and a few new proofs about it, we can bootstrap
consequences of Integer equality from our work with Nat equality
|#

(claim Int=-conseq (-> Integer Integer U))
(define Int=-conseq
  (λ (k j) (Nat=-conseq (Int->Nat k) (Int->Nat j))))

(claim Int=-conseq-same
  (Π ([k Integer])
    (Int=-conseq k k)))
(define Int=-conseq-same
  (λ (k)
    (ind-Nat (Int->Nat k)
      (λ (n) (Nat=-conseq n n))
      sole
      (λ (n-1 _)
        (same n-1)))))

(claim use-Int=
  (Π ([k Integer]
      [j Integer])
    (-> (= Integer k j)
        (Int=-conseq k j))))
(define use-Int=
  (λ (k j j=k)
    (replace j=k
             (λ (?) (Int=-conseq k ?))
             (Int=-conseq-same k))))

;; One annoying thing about the way that we received Integer equality
;; is that when neutral terms involved, we may not be able to decide
;; integer equality because we don't what Nats they are. We can, however,
;; prove disequality in certain key cases.

;; For example, we can prove that all Negatives are nonzero

(claim Neg->Nat-is-Nonzero
  (Π ([k Nat])
    (-> (= Integer (Negative k) (Positive 0))
        Absurd)))
(define Neg->Nat-is-Nonzero
  (λ (k)
    (ind-Nat k
      (λ (k)
        (-> (= Integer (Negative k) (Positive 0))
          Absurd))
      (use-Int= (Negative 0) (Positive 0))
      (λ (k-1 _)
        (use-Int= (Negative (add1 k-1)) (Positive 0))))))

;; TODO prove that the negatives and the positives are disjoint

(claim Neg-Pos-Disjoint
  (Π ([k Nat]
      [j Nat])
    (-> (= Integer (Negative k) (Positive j))
        Absurd)))
(define Neg-Pos-Disjoint
  TODO)

;; TODO remove this everywhere?
;; here's the old style (kinda ugly) with its original name. try to get rid of it later?
(claim nat-of-negative-nonzero
  (Π ([k Nat])
    (Σ ([n Nat])
       (= Nat (Int->Nat (Negative k)) (add1 n)))))
(define nat-of-negative-nonzero
  (λ (k)
    (ind-Nat k
      (λ (k)
        (Σ ([n Nat])
          (= Nat (Int->Nat (Negative k)) (add1 n))))
      (cons 0 (same 1))
      (λ (k-1 IH)
        (cons (add1 (add1 (car IH)))
          (cong (cdr IH) succ2))))))


;; TODO add more and more proofs involving just equality here.

;; TODO minimize number of proofs needed and
;; edit later proofs based on any improvements.



#| What can we do to to Integers besides make them Nats? |#

;; We can negate integers! Don't forget that (Negative k)
;; means 0 - (k+1). Also don't forget that 0=-0

(claim Negate (-> Integer Integer))
(define Negate
  (λ (k)
    (which-Int k
      Integer
      (λ (neg) (Positive (add1 neg)))
      (λ (pos) (which-Nat pos
                 (Positive 0)
                 Negative)))))

;; as we'd hope, applying negation twice gets us back where we started.
(claim Neg-Neg-same
  (Π ([k Integer])
    (= Integer (Negate (Negate k)) k)))
(define Neg-Neg-same
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Negate (Negate k)) k))
      (λ (neg) (same (Negative neg)))
      (λ (pos)
        (ind-Nat pos
          (λ (p)
            (= Integer (Negate (Negate (Positive p))) (Positive p)))
          (same (Positive 0))
          (λ (pos-1 _)
            (same (Positive (add1 pos-1)))))))))


;; Another fun fact is that the only number who is its own negative is 0
(claim Neg=0->same
  (Π ([k Integer])
    (-> (= Integer (Negate k) (Positive 0))
        (= Integer k (Positive 0)))))

;; SIMPLIFIED using Neg->Nat-is-Nonzero
(define Neg=0->same
  (λ (k)
    (ind-Int k
      (λ (k)
        (-> (= Integer (Negate k) (Positive 0))
          (= Integer k (Positive 0))))
      (λ (neg p)
        (ind-Absurd (use-Int= (Positive (add1 neg)) (Positive 0) p)
          (= Integer (Negative neg) (Positive 0))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (-> (= Integer (Negate (Positive k)) (Positive 0))
              (= Integer (Positive k) (Positive 0))))
          (λ (_) (same (Positive 0)))
          (λ (pos-1 _ p)
            (ind-Absurd (Neg->Nat-is-Nonzero pos-1 p)
              (= Integer (Positive (add1 pos-1)) (Positive 0)))))))))

;; And while the function Succ was a little bit interesting,
;; we have a different notion more typically used for Integers, of
;; predecessor and successor. We're careful here to maintain that
;; there is only one 0.

;; Because the name Succ has been used above, and the relationship there is nice,
;; we will use Sub1 and Add1 for predecessor and successor

(claim Sub1 (-> Integer Integer))
(define Sub1
  (λ (k)
    (which-Int k
      Integer
      (λ (neg) (Negative (add1 neg)))
      (λ (pos) (which-Nat pos (Negative 0) Positive)))))

(claim Add1 (-> Integer Integer))
(define Add1
  (λ (k)
    (which-Int k
      Integer
      (λ (neg)
        (which-Nat neg (Positive 0)  Negative))
      (λ (pos) (Positive (add1 pos))))))

;; As we'd hope, adding and subtracting 1 are both inverses of each other.

(claim Add1-Sub1-same
  (Π ([k Integer])
    (= Integer (Add1 (Sub1 k)) k)))
(define Add1-Sub1-same
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Add1 (Sub1 k)) k))
      (λ (neg) (same (left neg)))
      (λ (pos)
        (ind-Nat pos
          (λ (pos)
            (= Integer
              (Add1 (Sub1 (Positive pos)))
              (Positive pos)))
          (same (right 0))
          (λ (pos-1 ans)
            (same (Positive (add1 pos-1)))))))))

(claim Sub1-Add1-same
  (Π ([k Integer])
    (= Integer (Sub1 (Add1 k)) k)))
(define Sub1-Add1-same
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Sub1 (Add1 k)) k))
      (λ (neg)
        (ind-Nat neg
          (λ (neg) (= Integer (Sub1 (Add1 (Negative neg))) (Negative neg)))
          (same (left 0))
          (λ (neg+1 _)
            (same (Negative (add1 neg+1))))))
      (λ (pos) (same (right pos))))))

;; finally, the three functions have a mutual relationship
;; under composition
(claim Neg-Add1=Sub1-Neg
  (Π ([k Integer])
    (= Integer (Negate (Add1 k))
       (Sub1 (Negate k)))))
(define Neg-Add1=Sub1-Neg
  (λ (k)
    (ind-Int k
      (λ (k)
        (= Integer (Negate (Add1 k))
          (Sub1 (Negate k))))
      (λ (neg)
        (ind-Nat neg
          (λ (neg)
            (= Integer (Negate (Add1 (Negative neg)))
              (Sub1 (Negate (Negative neg)))))
          (same (Positive 0))
          (λ (n-1 _)
            (same (Positive (add1 n-1))))))
      (λ (pos)
        (ind-Nat pos
          (λ (p)
            (= Integer (Negate (Add1 (Positive p)))
              (Sub1 (Negate (Positive p)))))
          (same (Negative 0))
          (λ (p-1 _)
            (same (Negative (add1 p-1)))))))))

(claim Neg-Sub1=Add1-Neg
  (Π ([k Integer])
    (= Integer (Negate (Sub1 k))
       (Add1 (Negate k)))))
(define Neg-Sub1=Add1-Neg
  (λ (k)
    (ind-Int k
      (λ (k)
        (= Integer (Negate (Sub1 k))
          (Add1 (Negate k))))
      (λ (neg)
        (ind-Nat neg
          (λ (n)
            (= Integer (Negate (Sub1 (Negative n)))
              (Add1 (Negate (Negative n)))))
          (same (Positive 2))
          (λ (n-1 IH)
            (same (Positive (add1 (add1 (add1 n-1))))))))
      (λ (pos)
        (ind-Nat pos
          (λ (p)
            (= Integer (Negate (Sub1 (Positive p)))
              (Add1 (Negate (Positive p)))))
          (same (Positive 1))
          (λ (p-1 IH)
            (equal Integer
              (Negate (Sub1 (Add1 (Positive p-1))))
              #:by (cong (Sub1-Add1-same (Positive p-1)) Negate)
              (Negate (Positive p-1))
              #:by (symm (Add1-Sub1-same (Negate (Positive p-1))))
              (Add1 (Sub1 (Negate (Positive p-1))))
              #:by (cong (symm (Neg-Add1=Sub1-Neg (Positive p-1))) Add1)
              (Add1 (Negate (Add1 (Positive p-1)))))))))))

;; having a very solid understanding about the Nats and Integers
;; as far as their respective orderings, and their mutual relationship,
;; we define addition and multiplication.
