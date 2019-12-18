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

;; and we have ind-Int for when we do! It's equivalent to ind-Int, but practices good representation independence.
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

;; SIMPLIFIED the crux of this a lot by using new proof Neg->Nat-is-Nonzero
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
;; we're ready to define addition!
;; Here we have it, on both the Nats and the Integers

(claim plus (-> Nat Nat Nat))
(define plus (λ (j k) (iter-Nat j k succ)))

(claim Plus (-> Integer Integer Integer))
(define Plus
  (λ (j k)
    (which-Int j
      Integer
      (λ (neg1) (iter-Nat neg1 (Sub1 k) Sub1))
      (λ (pos1) (iter-Nat pos1 k Add1)))))

;; having these two definitions, we now of course begin by
;; proving relationships between plus and Plus, also
;; providing for us some of the sign/value expectations from Plus
(claim Posj-Plus-Posk=j-plus-k
  (Π ([j Nat]
      [k Nat])
    (= Integer (Plus (Positive j) (Positive k))
       (Positive (plus j k)))))
(define Posj-Plus-Posk=j-plus-k
  (λ (j k)
    (ind-Nat j
      (λ (j)
        (= Integer (Plus (Positive j) (Positive k))
          (Positive (plus j k))))
      (same (Positive k))
      (λ (_ IH) (cong IH Add1)))))

;; the add1 just comes from the shifted def of Negative
(claim Negj-plus-Negk=Neg-add1-j-plus-k
  (Π ([j Nat]
      [k Nat])
    (= Integer (Plus (Negative j) (Negative k))
       (Negative (add1 (plus j k))))))
(define Negj-plus-Negk=Neg-add1-j-plus-k
  (λ (j k)
    (ind-Nat j
      (λ (j)
        (= Integer (Plus (Negative j) (Negative k))
          (Negative (add1 (plus j k)))))
      (same (Negative (add1 k)))
      (λ (_ IH) (cong IH Sub1)))))

;; TODO define + on encoded integers, and prove
;; expected result for Plus on mixed-signs.

#|Now, we will prove the basics about + on Nats, and
then see if we can use our isomorphism to prove it for Ints.

The basics are:
0 is an identity on left and right
associativity
commutativity


This might not get us where we need for Ints.
If not, we can define a function which is
Integer addition on encoded integers,
and prove the properties of that.

And if THAT doesn't work, we can try to prove it directly
(I have this in an other file, we'll be fine regardless)
 Let's see! :)

|#

(claim plus-0-l (Π ([k Nat]) (= Nat (plus 0 k) k)))
(define plus-0-l (λ (k) (same k)))
(claim plus-0-r (Π ([k Nat]) (= Nat (plus k 0) k)))
(define plus-0-r
  (λ (k)
    (ind-Nat k
      (λ (k) (= Nat (plus k 0) k))
      (same 0)
      (λ (k-1 IH) (cong IH succ)))))

(claim plus-assoc
  (Π ([j Nat]
      [k Nat]
      [l Nat])
    (= Nat (plus (plus j k) l)
       (plus j (plus k l)))))
(define plus-assoc
  (λ (j k l)
    (ind-Nat j
      (λ (j)
        (= Nat (plus (plus j k) l)
          (plus j (plus k l))))
      (same (plus k l))
      (λ (j-1 IH)
        (cong IH succ)))))

;; Lemma for plus-comm, and proof on other side just for completeness
(claim plus-add1-r
  (Π ([j Nat]
      [k Nat])
    (= Nat (add1 (plus j k)) (plus j (add1 k)))))
(define plus-add1-r
  (λ (j k)
    (ind-Nat j
      (λ (j) (= Nat (add1 (plus j k)) (plus j (add1 k))))
      (same (add1 k))
      (λ (j-1 IH)
        (cong IH succ)))))

(claim plus-add1-l
  (Π ([j Nat]
      [k Nat])
    (= Nat (add1 (plus j k)) (plus (add1 j) k))))
(define plus-add1-l
  (λ (j k) (same (add1 (plus j k)))))

(claim plus-comm
  (Π ([j Nat]
      [k Nat])
    (= Nat (plus j k) (plus k j))))
(define plus-comm
  (λ (j k)
    (ind-Nat j
      (λ (j) (= Nat (plus j k) (plus k j)))
      (symm (plus-0-r k))
      (λ (j-1 IH)
        (equal Nat
          (add1 (plus j-1 k))
          #:by (cong IH succ)
          (add1 (plus k j-1))
          #:by (plus-add1-r k j-1)
          (plus k (add1 j-1)))))))


;; Here are the proofs directly on the Integers.
;; Maybe later I'll have another set of
;; proofs that can be swapped out, that just came straight from the Nats'.

(claim +-sub1-l
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Plus (Sub1 k) j)
       (Sub1 (Plus k j)))))
(define +-sub1-l
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer
             (Plus (Sub1 k) j)
             (Sub1 (Plus k j)))))
      (λ (k j)
        (ind-Nat k
          (λ (k)
            (= Integer
              (Plus (Sub1 (Negative k)) j)
              (Sub1 (Plus (Negative k) j))))
          (same (Sub1 (Sub1 j)))
          (λ (k-1 ans) (cong ans Sub1))))
      (λ (k j)
        (ind-Nat k
          (λ (k)
            (= Integer
              (Plus (Sub1 (Positive k)) j)
              (Sub1 (Plus (Positive k) j))))
          (same (Sub1 j))
          (λ (k-1 ans)
            (symm (Sub1-Add1-same (Plus (Positive k-1) j)))))))))

(claim negate-plus-dist
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Plus k j)
       (Negate (Plus (Negate k) (Negate j))))))
(define negate-plus-dist
  (λ (k j)
    (ind-Int k
      (λ (k)
        (= Integer
          (Plus k j)
          (Negate (Plus (Negate k) (Negate j)))))
      (λ (neg)
        (ind-Nat neg
          (λ (neg)
            (= Integer
              (Plus (Negative neg) j)
              (Negate (Plus (Negate (Negative neg)) (Negate j)))))
          (equal Integer
            (Sub1 j)
            #:by (symm (Neg-Neg-same (Sub1 j)))
            (Negate (Negate (Sub1 j)))
            #:by (cong (Neg-Sub1=Add1-Neg j) Negate)
            (Negate (Add1 (Negate j))))
          (λ (neg-1 IH)
            (equal Integer
              (Sub1 (Plus (Negative neg-1) j))
              #:by (cong IH Sub1)
              (Sub1 (Negate (Plus (Negate (Negative neg-1)) (Negate j))))
              #:by (symm (Neg-Add1=Sub1-Neg (Plus (Negate (Negative neg-1)) (Negate j))))
              (Negate (Add1 (Plus (Negate (Negative neg-1)) (Negate j))))
              #:by (cong
                     (symm (Neg-Sub1=Add1-Neg (Negative neg-1)))
                     (the (-> Integer Integer)
                           (λ (k) (Negate (Plus k (Negate j))))))
              (Negate (Plus (Negate (Sub1 (Negative neg-1))) (Negate j)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos)
            (= Integer
              (Plus (Positive pos) j)
              (Negate (Plus (Negate (Positive pos)) (Negate j)))))
          (symm (Neg-Neg-same j))
          (λ (pos-1 IH)
            (equal Integer
              (Add1 (Plus (Positive pos-1) j))
              #:by (cong IH Add1)
              (Add1 (Negate (Plus (Negate (Positive pos-1)) (Negate j))))
              #:by (symm (Neg-Sub1=Add1-Neg (Plus (Negate (Positive pos-1)) (Negate j))))
              (Negate (Sub1 (Plus (Negate (Positive pos-1)) (Negate j))))
              #:by (symm (cong (+-sub1-l (Negate (Positive pos-1)) (Negate j))
                           Negate))
              (Negate (Plus (Sub1 (Negate (Positive pos-1))) (Negate j)))
              #:by (cong (symm (Neg-Add1=Sub1-Neg (Positive pos-1)))
                     (the (-> Integer Integer)
                       (λ (k)
                         (Negate (Plus k (Negate j))))))
              (Negate (Plus (Negate (Add1 (Positive pos-1))) (Negate j))))))))))

(claim +-zero-l
  (Π ([k Integer])
    (= Integer (Plus (Positive 0) k) k)))
(define +-zero-l
  (λ (k) (same k)))

(claim +-zero-r
  (Π ([k Integer])
    (= Integer (Plus k (Positive 0)) k)))
(define +-zero-r
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Plus k (Positive 0)) k))
      (λ (neg)
        (ind-Nat neg
          (λ (neg)
            (= Integer (Plus (Negative neg) (Positive 0))
                     (Negative neg)))
          (same (Negative 0))
          (λ (neg-1 ans)
            (cong ans Sub1))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos) (= Integer
                     (Plus (Positive pos) (Positive 0))
                     (Positive pos)))
          (same (Positive 0))
          (λ (_ ans)
            (cong ans Add1)))))))

;; Proof that + is associative

;; we don't need +-add1-r til commutativity but it goes here
(claim +-add1-r
  (Π ([k Integer]
      [j Integer])
    (= Integer (Plus k (Add1 j))
       (Add1 (Plus k j)))))
(define +-add1-r
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer (Plus k (Add1 j))
             (Add1 (Plus k j)))))
      (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer (Plus (Negative k) (Add1 j))
               (Add1 (Plus (Negative k) j))))
      (trans (Sub1-Add1-same j)
        (symm (Add1-Sub1-same j)))
      (λ (k-1 IH)
        (equal Integer
          (Sub1 (Plus (Negative k-1) (Add1 j)))
          #:by (cong IH Sub1)
          (Sub1 (Add1 (Plus (Negative k-1) j)))
          #:by (Sub1-Add1-same (Plus (Negative k-1) j))
          (Plus (Negative k-1) j)
          #:by (symm (Add1-Sub1-same (Plus (Negative k-1) j)))
          (Add1 (Plus (Negative (add1 k-1)) j))))))
      (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer (Plus (Positive k) (Add1 j))
       (Add1 (Plus (Positive k) j))))
      (same (Add1 j))
      (λ (k-1 IH)
        (cong IH Add1)))))))


(claim +-add1-l
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Plus (Add1 k) j)
       (Add1 (Plus k j)))))
(define +-add1-l
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer
             (Plus (Add1 k) j)
             (Add1 (Plus k j)))))
      (λ (k j)
        (ind-Nat k
          (λ (k)
            (= Integer
              (Plus (Add1 (Negative k)) j)
              (Add1 (Plus (Negative k) j))))
          (symm (Add1-Sub1-same j))
          (λ (k-1 ans)
            (symm (Add1-Sub1-same (Plus (Negative k-1) j))))))
      (λ (k)
        (ind-Nat k
          (λ (k)
            (Π ([j Integer])
              (= Integer
                 (Plus (Add1 (Positive k)) j)
                 (Add1 (Plus (Positive k) j)))))
          (λ (j) (same (Add1 j)))
          (λ (k-1 ans)
            (λ (j)
          (same (Add1 (Add1 (Plus (Positive k-1) j)))))))))))


(claim +-sub1-r-neg
  (Π ([k Nat]
      [j Integer])
    (= Integer (Plus (Negative k) (Sub1 j))
       (Sub1 (Plus (Negative k) j)))))

(claim +-sub1-r
  (Π ([k Integer]
      [j Integer])
    (= Integer (Plus k (Sub1 j))
       (Sub1 (Plus k j)))))
(define +-sub1-r
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer (Plus k (Sub1 j))
             (Sub1 (Plus k j)))))
      (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Plus (Negative k) (Sub1 j))
          (Sub1 (Plus (Negative k) j))))
      (same (Sub1 (Sub1 j)))
      (λ (k-1 ans)
        (cong ans Sub1))))
      (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Plus (Positive k) (Sub1 j))
          (Sub1 (Plus (Positive k) j))))
      (same (Sub1 j))
      (λ (k-1 ans)
        (equal Integer
          (Add1 (Plus (Positive k-1) (Sub1 j)))
          #:by (cong ans Add1)
          (Add1 (Sub1 (Plus (Positive k-1) j)))
          #:by (Add1-Sub1-same (Plus (Positive k-1) j))
          (Plus (Positive k-1) j)
          #:by (symm (Sub1-Add1-same (Plus (Positive k-1) j)))
          (Sub1 (Add1 (Plus (Positive k-1) j))))))))))

(claim +-assoc
  (Π ([k Integer]
      [j Integer]
      [l Integer])
    (= Integer (Plus k (Plus j l))
       (Plus (Plus k j) l))))

(define +-assoc
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer]
            [l Integer])
          (= Integer (Plus k (Plus j l))
             (Plus (Plus k j) l))))
        (λ (neg)
    (ind-Nat neg
      (λ (neg)
        (Π ([j Integer]
            [l Integer])
          (= Integer (Plus (Negative neg) (Plus j l))
             (Plus (Plus (Negative neg) j) l))))
      (λ (j l)
        (symm (+-sub1-l j l)))
      (λ (neg-1 ans)
        (λ (j l)
          (equal Integer
            (Sub1 (Plus (Negative neg-1) (Plus j l)))
            #:by (cong (ans j l) Sub1)
            (Sub1 (Plus (Plus (Negative neg-1) j) l))
            #:by (symm (+-sub1-l (Plus (Negative neg-1) j) l))
            (Plus (Sub1 (Plus (Negative neg-1) j)) l))))))
        (λ (pos)
    (ind-Nat pos
      (λ (pos)
        (Π ([j Integer]
            [l Integer])
          (= Integer (Plus (Positive pos) (Plus j l))
             (Plus (Plus (Positive pos) j) l))))
      (λ (j l) (same (Plus j l)))
      (λ (pos-1 ans)
        (λ (j l)
          (equal Integer
            (Add1 (Plus (Positive pos-1) (Plus j l)))
            #:by (cong (ans j l) Add1)
            (Add1 (Plus (Plus (Positive pos-1) j) l))
            #:by (symm (+-add1-l (Plus (Positive pos-1) j) l))
            (Plus (Add1 (Plus (Positive pos-1) j)) l)))))))))



;; proof that + is commutative

(claim +-comm
  (Π ([j Integer]
      [k Integer])
    (= Integer (Plus j k) (Plus k j))))

(define +-comm
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer (Plus k j) (Plus j k))))
      (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer (Plus (Negative k) j) (Plus j (Negative k))))
      (equal Integer
        (Sub1 j)
        #:by (symm (cong (+-zero-r j) Sub1))
        (Sub1 (Plus j (Positive 0)))
        #:by (symm (+-sub1-r j (Positive 0)))
        (Plus j (Negative 0)))
      (λ (k-1 ans)
        (equal Integer
          (Sub1 (Plus (Negative k-1) j))
          #:by (cong ans Sub1)
          (Sub1 (Plus j (Negative k-1)))
          #:by (symm (+-sub1-r j (Negative k-1)))
          (Plus j (Negative (add1 k-1)))))))
      (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer (Plus (Positive k) j) (Plus j (Positive k))))
      (symm (+-zero-r j))
      (λ (k-1 ans)
        (equal Integer
          (Add1 (Plus (Positive k-1) j))
          #:by (cong ans Add1)
          (Add1 (Plus j (Positive k-1)))
          #:by (symm (+-add1-r j (Positive k-1)))
          (Plus j (Positive (add1 k-1))))))))))


;; Here are some more proofs about things that the Nats can't talk about (yet) like
;; negativity and inverses!

(claim +-inv-same-negative-1
  (Π ([k Nat])
    (= Integer
       (Plus (Positive k) (Negative k))
       (Negative 0))))
(define +-inv-same-negative-1
  (λ (k)
    (ind-Nat k
      (λ (k) (= Integer
               (Plus (Positive k) (Negative k))
               (Negative 0)))
      (same (Negative 0))
      (λ (k-1 IH)
        (equal Integer
          (Add1 (Plus (Positive k-1) (Negative (add1 k-1))))
          #:by (cong (+-comm (Positive k-1) (Negative (add1 k-1))) Add1)
          (Add1 (Sub1 (Plus (Negative k-1) (Positive k-1))))
          #:by (Add1-Sub1-same (Plus (Negative k-1) (Positive k-1)))
          (Plus (Negative k-1) (Positive k-1))
          #:by (+-comm (Negative k-1) (Positive k-1))
          (Plus (Positive k-1) (Negative k-1))
          #:by IH
          (Negative 0))))))

(claim +-inv-r-0
  (Π ([k Integer])
    (= Integer (Plus k (Negate k)) (Positive 0))))
(define +-inv-r-0
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Plus k (Negate k)) (Positive 0)))
      (λ (neg)
        (equal Integer
          (Plus (Negative neg) (Positive (add1 neg)))
          #:by (+-comm (Negative neg) (Positive (add1 neg)))
          (Add1 (Plus (Positive neg) (Negative neg)))
          #:by (cong (+-inv-same-negative-1 neg) Add1)
          (Positive 0)))
      (λ (pos)
        (ind-Nat pos
          (λ (p)
            (= Integer
              (Plus (Positive p) (Negate (Positive p)))
              (Positive 0)))
          (same (Positive 0))
          (λ (pos-1 IH)
            (cong (+-inv-same-negative-1 pos-1) Add1)))))))

(claim +-inv-l-0
  (Π ([k Integer])
    (= Integer (Plus (Negate k) k) (Positive 0))))
(define +-inv-l-0
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Plus (Negate k) k) (Positive 0)))
      (λ (neg)
        (ind-Nat neg
          (λ (k) (= Integer (Plus (Negate (Negative k)) (Negative k)) (Positive 0)))
          (same (Positive 0))
          (λ (neg-1 _)
            (cong (+-inv-same-negative-1 (add1 neg-1)) Add1))))
      (λ (pos)
        (ind-Nat pos
          (λ (k) (= Integer (Plus (Negate (Positive k)) (Positive k)) (Positive 0)))
          (same (Positive 0))
          (λ (pos-1 _)
            (equal Integer
              (Plus (Negative pos-1) (Positive (add1 pos-1)))
              #:by (+-comm (Negative pos-1) (Positive (add1 pos-1)))
              (Add1 (Plus (Positive pos-1) (Negative pos-1)))
              #:by (cong (+-inv-same-negative-1 pos-1) Add1)
              (Positive 0))))))))

;;;;;; OKAY, time for *

(claim times (-> Nat Nat Nat))
(define times
  (λ (j k) (iter-Nat j zero (plus k))))

(claim Times (-> Integer Integer Integer))
(define Times
  (λ (j k)
    (which-Int j
      Integer
      (λ (neg)
        (iter-Nat neg
          (Negate k)
          (Plus (Negate k))))
      (λ (pos)
        (iter-Nat pos
          (Positive 0)
          (Plus k))))))

;; first, stuff with good ole nats

;; TODO define, as we want to with +, a function that works on encoded Ints and explore,
;; to get all the options
(claim Posj-Times-Posk=j-times-k
  (Π ([k Nat]
      [j Nat])
    (= Integer (Times (Positive k) (Positive j))
       (Positive (times k j)))))
(define Posj-Times-Posk=j-times-k
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Times (Positive k) (Positive j))
          (Positive (times k j))))
      (same (Positive 0))
      (λ (k-1 IH)
        (equal Integer
          (Plus (Positive j) (Times (Positive k-1) (Positive j)))
          #:by (cong IH (Plus (Positive j)))
          (Plus (Positive j) (Positive (times k-1 j)))
          #:by (Posj-Plus-Posk=j-plus-k j (times k-1 j))
          (Positive (plus j (times k-1 j))))))))

(claim Negj-Times-Negk=k+1-times-j+1
  (Π ([k Nat]
      [j Nat])
    (= Integer (Times (Negative k) (Negative j))
       (Positive (times (add1 k) (add1 j))))))
(define Negj-Times-Negk=k+1-times-j+1
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Times (Negative k) (Negative j))
       (Positive (times (add1 k) (add1 j)))))
      (cong (symm (plus-0-r (add1 j))) Positive)
      (λ (k-1 IH)
        (equal Integer
          (Plus (Positive (add1 j)) (Times (Negative k-1) (Negative j)))
          #:by (cong IH (Plus (Positive (add1 j))))
          (Plus (Positive (add1 j)) (Positive (times (add1 k-1) (add1 j))))
          #:by (Posj-Plus-Posk=j-plus-k (add1 j) (times (add1 k-1) (add1 j)))
          (Positive (times (add1 (add1 k-1)) (add1 j))))))))

(claim flip-is-negate
  (Π ([k Integer])
    (= Integer (Times k (Negative 0)) (Negate k))))
(define flip-is-negate
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Times k (Negative 0)) (Negate k)))
      (λ (neg)
        (ind-Nat neg
          (λ (neg) (= Integer (Times (Negative neg) (Negative 0)) (Negate (Negative neg))))
          (same (Positive 1))
          (λ (neg-1 IH)
            (cong IH Add1))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos) (= Integer (Times (Positive pos) (Negative 0)) (Negate (Positive pos))))
          (same (Positive 0))
          (λ (pos-1 IH)
            (equal Integer
              (Sub1 (Times (Positive pos-1) (Negative 0)))
              #:by (cong IH Sub1)
              (Sub1 (Negate (Positive pos-1)))
              #:by (symm (Neg-Add1=Sub1-Neg (Positive pos-1)))
              (Negate (Positive (add1 pos-1))))))))))

;; proof that multiplication has 1 as an identity

(claim *-1-id-l
  (Π ([k Integer])
    (= Integer (Times (Positive 1) k) k)))

(define *-1-id-l
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Times (Positive 1) k) k))
      (λ (neg)
        (ind-Nat neg
          (λ (k)
            (= Integer
              (Times (Positive 1) (Negative k))
              (Negative k)))
          (same (Negative 0))
          (λ (neg-1 ans)
            (cong ans (Plus (Negative 0))))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (= Integer
              (Times (Positive 1) (Positive k))
              (Positive k)))
          (same (Positive 0))
          (λ (pos-1 ans)
            (cong ans (Plus (Positive 1)))))))))

(claim *-1-id-r
  (Π ([k Integer])
    (= Integer (Times k (Positive 1)) k)))
(define *-1-id-r
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Times k (Positive 1)) k))
      (λ (neg)
        (ind-Nat neg
          (λ (n) (= Integer (Times (Negative n) (Positive 1)) (Negative n)))
          (same (Negative 0))
          (λ (n-1 IH)
            (cong IH (Plus (Negate (Positive 1)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (p) (= Integer (Times (Positive p) (Positive 1)) (Positive p)))
          (same (Positive 0))
          (λ (n-1 IH)
            (cong IH (Plus (Positive 1)))))))))


;; proof that would be above but needs info about *1 id
(claim add1-pos-times-neg-is-negative
  (Π ([k Nat]
      [j Nat])
    (Σ ([n Nat])
       (= Integer (Times (Positive (add1 k)) (Negative j))
          (Negative n)))))
(define add1-pos-times-neg-is-negative
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (Σ ([n Nat])
          (= Integer (Times (Positive (add1 k)) (Negative j))
             (Negative n))))
      (cons j (*-1-id-r (Negative j)))
      (λ (k-1 IH)
        (cons (add1 (plus j (car IH)))
          (equal Integer
            (Plus (Negative j) (Times (Positive (add1 k-1)) (Negative j)))
            #:by (cong (cdr IH) (Plus (Negative j)))
            (Plus (Negative j) (Negative (car IH)))
            #:by ( Negj-plus-Negk=Neg-add1-j-plus-k j (car IH))
            (Negative (add1 (plus j (car IH))))))))))

;; proof that * and add1, sub1 distribute on left and right


(claim *-sub1-dist-l
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Times (Sub1 k) j)
       (Plus (Negate j) (Times k j)))))
(define *-sub1-dist-l
  (λ (k j)
    (ind-Int k
      (λ (k)
        (= Integer
          (Times (Sub1 k) j)
          (Plus (Negate j) (Times k j))))
      (λ (neg)
        (ind-Nat neg
          (λ (k)
            (= Integer
              (Times (Sub1 (Negative k)) j)
              (Plus (Negate j) (Times (Negative k) j))))
          (same (Times (Negative 1) j))
          (λ (neg-1 IH)
            (same (Plus (Negate j) (Plus (Negate j) (Times (Negative neg-1) j)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (= Integer
              (Times (Sub1 (Positive k)) j)
              (Plus (Negate j) (Times (Positive k) j))))
          (symm (+-zero-r (Negate j)))
          (λ (pos-1 IH)
            (equal Integer
              (Times (Sub1 (Positive (add1 pos-1))) j)
              #:by (cong (Sub1-Add1-same (Positive pos-1))
                     (the (-> Integer Integer)
                       (λ (k) (Times k j))))
              (Times (Positive pos-1) j)
              #:by (cong (symm (+-inv-l-0 j)) (the (-> Integer Integer) (λ (k) (Plus k (Times (Positive pos-1) j)))))
              (Plus (Plus (Negate j) j) (Times (Positive pos-1) j))
              #:by (symm (+-assoc (Negate j) j (Times (Positive pos-1) j)))
              (Plus (Negate j) (Plus j (Times (Positive pos-1) j))))))))))

(claim *-sub1-dist-r
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Times k (Sub1 j))
       (Plus (Negate k) (Times k j)))))
(define *-sub1-dist-r
  (λ (k j)
    (ind-Int k
      (λ (k)
        (= Integer
          (Times k (Sub1 j))
          (Plus (Negate k) (Times k j))))
      (λ (neg)
        (ind-Nat neg
          (λ (k)
            (= Integer
              (Times (Negative k) (Sub1 j))
              (Plus (Negate (Negative k)) (Times (Negative k) j))))
          (Neg-Sub1=Add1-Neg j)
          (λ (neg-1 IH)
            (equal Integer
              (Plus (Negate (Sub1 j)) (Times (Negative neg-1) (Sub1 j)))
              #:by (cong IH (Plus (Negate (Sub1 j))))
              (Plus (Negate (Sub1 j)) (Plus (Negate (Negative neg-1)) (Times (Negative neg-1) j)))
              #:by (+-assoc (Negate (Sub1 j)) (Negate (Negative neg-1)) (Times (Negative neg-1) j))
              (Plus (Plus (Negate (Sub1 j)) (Positive (add1 neg-1))) (Times (Negative neg-1) j))
              #:by (cong (Neg-Sub1=Add1-Neg j)
                     (the (-> Integer Integer)
                       (λ (?)
                         (Plus
                           (Plus ? (Positive (add1 neg-1)))
                           (Times (Negative neg-1) j)))))
              (Plus (Plus (Add1 (Negate j)) (Positive (add1 neg-1))) (Times (Negative neg-1) j))
              #:by (cong (+-add1-l (Negate j) (Positive (add1 neg-1)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Negative neg-1) j)))))
              (Plus (Add1 (Plus (Negate j) (Positive (add1 neg-1)))) (Times (Negative neg-1) j))
              #:by (cong (+-comm (Negate j) (Positive (add1 neg-1)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Add1 ?) (Times (Negative neg-1) j)))))
              (Plus (Add1 (Plus (Positive (add1 neg-1)) (Negate j))) (Times (Negative neg-1) j))
              #:by (cong (symm (+-add1-l (Positive (add1 neg-1)) (Negate j)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Negative neg-1) j)))))
              (Plus (Plus (Positive (add1 (add1 neg-1))) (Negate j)) (Times (Negative neg-1) j))
              #:by (symm (+-assoc (Positive (add1 (add1 neg-1))) (Negate j) (Times (Negative neg-1) j)))
              (Plus (Positive (add1 (add1 neg-1))) (Plus (Negate j) (Times (Negative neg-1) j)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (= Integer
              (Times (Positive k) (Sub1 j))
              (Plus (Negate (Positive k)) (Times (Positive k) j))))
          (same (Positive 0))
          (λ (pos-1 IH)
            (equal Integer
              (Plus (Sub1 j) (Times (Positive pos-1) (Sub1 j)))
              #:by (cong IH (Plus (Sub1 j)))
              (Plus (Sub1 j) (Plus (Negate (Positive pos-1)) (Times (Positive pos-1) j)))
              #:by (+-assoc (Sub1 j) (Negate (Positive pos-1)) (Times (Positive pos-1) j))
              (Plus (Plus (Sub1 j) (Negate (Positive pos-1))) (Times (Positive pos-1) j))
              #:by (cong (+-sub1-l j (Negate (Positive pos-1)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Positive pos-1) j)))))
              (Plus (Sub1 (Plus j (Negate (Positive pos-1)))) (Times (Positive pos-1) j))
              #:by (cong (+-comm j (Negate (Positive pos-1)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Sub1 ?) (Times (Positive pos-1) j)))))
              (Plus (Sub1 (Plus (Negate (Positive pos-1)) j)) (Times (Positive pos-1) j))
              #:by (cong (symm (+-sub1-l (Negate (Positive pos-1)) j))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Positive pos-1) j)))))
              (Plus (Plus (Sub1 (Negate (Positive pos-1))) j) (Times (Positive pos-1) j))
              #:by (cong (symm (Neg-Add1=Sub1-Neg (Positive pos-1)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Plus ? j) (Times (Positive pos-1) j)))))
              (Plus (Plus (Negative pos-1) j) (Times (Positive pos-1) j))
              #:by (symm (+-assoc (Negative pos-1) j (Times (Positive pos-1) j)))
              (Plus (Negative pos-1) (Plus j (Times (Positive pos-1) j))))))))))

(claim *-add1-dist-l
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Times (Add1 k) j)
       (Plus j (Times k j)))))


#|
(k+1)*j=j+(k*j)
|#

(define *-add1-dist-l
  (λ (k j)
    (ind-Int k
      (λ (k)
        (= Integer
          (Times (Add1 k) j)
          (Plus j (Times k j))))
      (λ (neg)
        (ind-Nat neg
          (λ (k)
            (= Integer
              (Times (Add1 (Negative k)) j)
              (Plus j (Times (Negative k) j))))
          (symm (+-inv-r-0 j))
          (λ (neg-1 IH)
            (equal Integer
              (Times (Negative neg-1) j)
              #:by (cong (symm (+-inv-r-0 j)) (the (-> Integer Integer) (λ (k) (Plus k (Times (Negative neg-1) j)))))
              (Plus (Plus j (Negate j)) (Times (Negative neg-1) j))
              #:by (symm (+-assoc j (Negate j) (Times (Negative neg-1) j)))
              (Plus j (Plus (Negate j) (Times (Negative neg-1) j)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (= Integer
              (Times (Add1 (Positive k)) j)
              (Plus j (Times (Positive k) j))))
          (same (Plus j (Positive 0)))
          (λ (pos-1 IH)
            (same (Plus j (Plus j (Times (Positive pos-1) j))))))))))

(claim *-add1-dist-r
  (Π ([k Integer]
      [j Integer])
    (= Integer
       (Times k (Add1 j))
       (Plus k (Times k j)))))
(define *-add1-dist-r
  (λ (k j)
    (ind-Int k
      (λ (k)
        (= Integer
          (Times k (Add1 j))
          (Plus k (Times k j))))
      (λ (neg)
        (ind-Nat neg
          (λ (k)
            (= Integer
              (Times (Negative k) (Add1 j))
              (Plus (Negative k) (Times (Negative k) j))))
          (Neg-Add1=Sub1-Neg j)
          (λ (neg-1 IH)
            (equal Integer
              (Plus (Negate (Add1 j)) (Times (Negative neg-1) (Add1 j)))
              #:by (cong IH (Plus (Negate (Add1 j))))
              (Plus (Negate (Add1 j)) (Plus (Negative neg-1) (Times (Negative neg-1) j)))
              #:by (cong (Neg-Add1=Sub1-Neg j)
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Plus (Negative neg-1) (Times (Negative neg-1) j))))))
              (Plus (Sub1 (Negate j)) (Plus (Negative neg-1) (Times (Negative neg-1) j)))
              #:by (+-assoc (Sub1 (Negate j)) (Negative neg-1) (Times (Negative neg-1) j))
              (Plus (Plus (Sub1 (Negate j)) (Negative neg-1)) (Times (Negative neg-1) j))
              #:by (cong (+-sub1-l (Negate j) (Negative neg-1))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Negative neg-1) j)))))
              (Plus (Sub1 (Plus (Negate j) (Negative neg-1))) (Times (Negative neg-1) j))
              #:by (cong (+-comm (Negate j) (Negative neg-1))
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Sub1 ?) (Times (Negative neg-1) j)))))
              (Plus (Sub1 (Plus (Negative neg-1) (Negate j))) (Times (Negative neg-1) j))
              #:by (symm (+-assoc (Negative (add1 neg-1)) (Negate j) (Times (Negative neg-1) j)))
              (Plus (Negative (add1 neg-1)) (Plus (Negate j) (Times (Negative neg-1) j)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (k)
            (= Integer
              (Times (Positive k) (Add1 j))
              (Plus (Positive k) (Times (Positive k) j))))
          (same (Positive 0))
          (λ (pos-1 IH)
            (equal Integer
              (Plus (Add1 j) (Times (Positive pos-1) (Add1 j)))
              #:by (cong IH (Plus (Add1 j)))
              (Plus (Add1 j) (Plus (Positive pos-1) (Times (Positive pos-1) j)))
              #:by (+-add1-l j (Plus (Positive pos-1) (Times (Positive pos-1) j)))
              (Add1 (Plus j (Plus (Positive pos-1) (Times (Positive pos-1) j))))
              #:by (cong (+-assoc j (Positive pos-1) (Times (Positive pos-1) j)) Add1)
              (Add1 (Plus (Plus j (Positive pos-1)) (Times (Positive pos-1) j)))
              #:by (cong (+-comm j (Positive pos-1))
                     (the (-> Integer Integer)
                       (λ (?) (Add1 (Plus ? (Times (Positive pos-1) j))))))
              (Add1 (Plus (Plus (Positive pos-1) j) (Times (Positive pos-1) j)))
              #:by (cong (symm (+-assoc (Positive pos-1) j (Times (Positive pos-1) j))) Add1)
              (Add1 (Plus (Positive pos-1) (Plus j (Times (Positive pos-1) j)))))))))))


;; proof that k * 0 = 0

(claim *-0-l
  (Π ([k Integer])
    (= Integer (Times (Positive 0) k) (Positive 0))))
(define *-0-l
  (λ (k)
    (same (Positive 0))))

(claim *-0-r
  (Π ([k Integer])
    (= Integer (Times k (Positive 0)) (Positive 0))))
(define *-0-r
  (λ (k)
    (ind-Int k
      (λ (k) (= Integer (Times k (Positive 0)) (Positive 0)))
      (λ (neg)
        (ind-Nat neg
          (λ (neg) (= Integer (Times (Negative neg) (Positive 0)) (Positive 0)))
          (same (Positive 0))
          (λ (neg-1 IH)
            (cong IH (Plus (Positive 0))))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos) (= Integer (Times (Positive pos) (Positive 0)) (Positive 0)))
          (same (Positive 0))
          (λ (pos-1 IH)
            (cong IH (Plus (Positive 0)))))))))
;; proof that *  distributes

(claim *-dist-l
  (Π ([k Integer]
      [j Integer]
      [l Integer])
    (= Integer (Times (Plus k j) l)
       (Plus (Times k l) (Times j l)))))
(define *-dist-l
  (λ (k j l)
    (ind-Int k
      (λ (k)
        (= Integer (Times (Plus k j) l)
          (Plus (Times k l) (Times j l))))
      (λ (neg)
        (ind-Nat neg
          (λ (n)
            (= Integer (Times (Plus (Negative n) j) l)
              (Plus (Times (Negative n) l) (Times j l))))
          (*-sub1-dist-l j l)
          (λ (neg-1 IH)
            (equal Integer
              (Times (Plus (Sub1 (Negative neg-1)) j) l)
              #:by (cong (+-sub1-l (Negative neg-1) j) (the (-> Integer Integer) (λ (k) (Times k l))))
              (Times (Sub1 (Plus (Negative neg-1) j)) l)
              #:by (*-sub1-dist-l (Plus (Negative neg-1) j) l)
              (Plus (Negate l) (Times (Plus (Negative neg-1) j) l))
              #:by (cong IH (Plus (Negate l)))
              (Plus (Negate l) (Plus (Times (Negative neg-1) l) (Times j l)))
              #:by (+-assoc (Negate l) (Times (Negative neg-1) l) (Times j l))
              (Plus (Plus (Negate l) (Times (Negative neg-1) l)) (Times j l))))))
      (λ (pos)
        (ind-Nat pos
          (λ (n)
            (= Integer (Times (Plus (Positive n) j) l)
              (Plus (Times (Positive n) l) (Times j l))))
          (same (Times j l)) 
          (λ (pos-1 IH)
            (equal Integer
              (Times (Add1 (Plus (Positive pos-1) j)) l)
              #:by (*-add1-dist-l (Plus (Positive pos-1) j) l)
              (Plus l (Times (Plus (Positive pos-1) j) l))
              #:by (cong IH (Plus l))
              (Plus l (Plus (Times (Positive pos-1) l) (Times j l)))
              #:by (+-assoc l (Times (Positive pos-1) l) (Times j l))
              (Plus (Plus l (Times (Positive pos-1) l)) (Times j l)))))))))

(claim *-dist-r
  (Π ([k Integer]
      [j Integer]
      [l Integer])
    (= Integer (Times k (Plus j l))
       (Plus (Times k j) (Times k l)))))
(define *-dist-r
  (λ (k j l)
    (ind-Int k
      (λ (k)
        (= Integer (Times k (Plus j l))
          (Plus (Times k j) (Times k l))))
      (λ (neg)
        (ind-Nat neg
          (λ (neg)
            (= Integer (Times (Negative neg) (Plus j l))
              (Plus (Times (Negative neg) j) (Times (Negative neg) l))))
          (equal Integer
            (Negate (Plus j l))
            #:by (cong (symm (Neg-Neg-same j))
                   (the (-> Integer Integer)
                     (λ (k) (Negate (Plus k l)))))
            (Negate (Plus (Negate (Negate j)) l))
            #:by (cong (symm (Neg-Neg-same l))
                   (the (-> Integer Integer)
                     (λ (k) (Negate (Plus (Negate (Negate j)) k)))))
            (Negate (Plus (Negate (Negate j)) (Negate (Negate l))))
            #:by (symm (negate-plus-dist (Negate j) (Negate l)))
            (Plus (Negate j) (Negate l)))
          (λ (neg-1 IH)
            (equal Integer
              (Plus (Negate (Plus j l)) (Times (Negative neg-1) (Plus j l)))
              #:by (cong (negate-plus-dist j l)
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Negate ?) (Times (Negative neg-1) (Plus j l))))))
              (Plus (Negate (Negate (Plus (Negate j) (Negate l)))) (Times (Negative neg-1) (Plus j l)))
              #:by (cong (Neg-Neg-same (Plus (Negate j) (Negate l)))
                     (the (-> Integer Integer)
                       (λ (?) (Plus ? (Times (Negative neg-1) (Plus j l))))))
              (Plus (Plus (Negate j) (Negate l)) (Times (Negative neg-1) (Plus j l)))
              #:by (cong IH (Plus (Plus (Negate j) (Negate l))))
              (Plus (Plus (Negate j) (Negate l)) (Plus (Times (Negative neg-1) j) (Times (Negative neg-1) l)))
              #:by (symm (+-assoc (Negate j) (Negate l) (Plus (Times (Negative neg-1) j) (Times (Negative neg-1) l))))
              (Plus (Negate j) (Plus (Negate l) (Plus (Times (Negative neg-1) j) (Times (Negative neg-1) l))))
              #:by (cong (+-assoc (Negate l) (Times (Negative neg-1) j) (Times (Negative neg-1) l))
                     (Plus (Negate j)))
              (Plus (Negate j) (Plus (Plus (Negate l) (Times (Negative neg-1) j)) (Times (Negative neg-1) l)))
              #:by (cong (+-comm (Negate l) (Times (Negative neg-1) j))
                     (the (-> Integer Integer)
                       (λ (?) (Plus (Negate j) (Plus ? (Times (Negative neg-1) l))))))
              (Plus (Negate j) (Plus (Plus (Times (Negative neg-1) j) (Negate l)) (Times (Negative neg-1) l)))
              #:by (cong (symm (+-assoc (Times (Negative neg-1) j) (Negate l) (Times (Negative neg-1) l)))
                     (Plus (Negate j)))
              (Plus (Negate j) (Plus (Times (Negative neg-1) j) (Plus (Negate l) (Times (Negative neg-1) l))))
              #:by (+-assoc (Negate j) (Times (Negative neg-1) j) (Plus (Negate l) (Times (Negative neg-1) l)))
              (Plus (Plus (Negate j) (Times (Negative neg-1) j)) (Plus (Negate l) (Times (Negative neg-1) l)))))))
      (λ (pos)
        (ind-Nat pos
          (λ (pos)
            (= Integer (Times (Positive pos) (Plus j l))
              (Plus (Times (Positive pos) j) (Times (Positive pos) l))))
          (same (Positive 0))
          (λ (pos-1 IH)
            (equal Integer
              (Plus (Plus j l) (Times (Positive pos-1) (Plus j l)))
              #:by (cong IH (Plus (Plus j l)))
              (Plus (Plus j l) (Plus (Times (Positive pos-1) j) (Times (Positive pos-1) l)))
              #:by (symm (+-assoc j l (Plus (Times (Positive pos-1) j) (Times (Positive pos-1) l))))
              (Plus j (Plus l (Plus (Times (Positive pos-1) j) (Times (Positive pos-1) l))))
              #:by (cong (+-assoc l (Times (Positive pos-1) j) (Times (Positive pos-1) l)) (Plus j))
              (Plus j (Plus (Plus l (Times (Positive pos-1) j)) (Times (Positive pos-1) l)))
              #:by (cong (+-comm l (Times (Positive pos-1) j))
                     (the (-> Integer Integer)
                       (λ (?) (Plus j (Plus ? (Times (Positive pos-1) l))))))
              (Plus j (Plus (Plus (Times (Positive pos-1) j) l) (Times (Positive pos-1) l)))
              #:by (cong (symm (+-assoc (Times (Positive pos-1) j) l (Times (Positive pos-1) l))) (Plus j))
              (Plus j (Plus (Times (Positive pos-1) j) (Plus l (Times (Positive pos-1) l))))
              #:by (+-assoc j (Times (Positive pos-1) j) (Plus l (Times (Positive pos-1) l)))
              (Plus (Plus j (Times (Positive pos-1) j)) (Plus l (Times (Positive pos-1) l))))))))))


;; proof that * and Negate are commutative under composition

(claim Negate-Times-comp-l-neg
  (Π ([k Nat]
      [j Integer])
    (= Integer (Times (Negate (Negative k)) j)
       (Negate (Times (Negative k) j)))))
(define Negate-Times-comp-l-neg
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Times (Negate (Negative k)) j)
          (Negate (Times (Negative k) j))))
      (trans (*-1-id-l j)
        (symm (Neg-Neg-same j)))
      (λ (k-1 ans)
        (equal Integer
          (Plus j (Times (Negate (Negative k-1)) j))
          #:by (cong ans (Plus j))
          (Plus j (Negate (Times (Negative k-1) j)))
          #:by (negate-plus-dist j (Negate (Times (Negative k-1) j)))
          (Negate (Plus (Negate j) (Negate (Negate (Times (Negative k-1) j)))))
          #:by (cong (Neg-Neg-same (Times (Negative k-1) j))
                 (the (-> Integer Integer)
                   (λ (x) (Negate (Plus (Negate j) x)))))
          (Negate (Plus (Negate j) (Times (Negative k-1) j))))))))

(claim Negate-Times-comp-l-pos
  (Π ([k Nat]
      [j Integer])
    (= Integer
       (Times (Negate (Positive k)) j)
       (Negate (Times (Positive k) j)))))
(define Negate-Times-comp-l-pos
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (= Integer (Times (Negate (Positive k)) j)
          (Negate (Times (Positive k) j))))
      (same (Positive 0))
      (λ (k-1 IH)
        (equal Integer
          (Times (Negate (Positive (add1 k-1))) j)
          #:by (cong (Neg-Add1=Sub1-Neg (Positive k-1))
                 (the (-> Integer Integer) (λ (k) (Times k j))))
          (Times (Sub1 (Negate (Positive k-1))) j)
          #:by (*-sub1-dist-l (Negate (Positive k-1)) j)
          (Plus (Negate j) (Times (Negate (Positive k-1)) j))
          #:by (cong IH (Plus (Negate j)))
          (Plus (Negate j) (Negate (Times (Positive k-1) j)))
          #:by (negate-plus-dist (Negate j) (Negate (Times (Positive k-1) j)))
          (Negate (Plus (Negate (Negate j)) (Negate (Negate (Times (Positive k-1) j)))))
          #:by (cong (Neg-Neg-same j)
                 (the (-> Integer Integer)
                   (λ (?) (Negate (Plus ? (Negate (Negate (Times (Positive k-1) j))))))))
          (Negate (Plus j (Negate (Negate (Times (Positive k-1) j)))))
          #:by (cong (Neg-Neg-same (Times (Positive k-1) j))
                 (the (-> Integer Integer)
                   (λ (?) (Negate (Plus j ?)))))
          (Negate (Plus j (Times (Positive k-1) j))))))))

(claim Negate-Times-comp-l
  (Π ([k Integer]
      [j Integer])
    (= Integer (Times (Negate k) j)
       (Negate (Times k j)))))
(define Negate-Times-comp-l
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer (Times (Negate k) j)
             (Negate (Times k j)))))
      Negate-Times-comp-l-neg
      Negate-Times-comp-l-pos)))

(claim *-assoc-neg
  (Π ([k Nat]
      [j Integer]
      [l Integer])
    (= Integer
       (Times (Negative k) (Times j l))
       (Times (Times (Negative k) j) l))))

(define *-assoc-neg
  (λ (k j l)
    (ind-Nat k
      (λ (k)
        (= Integer
          (Times (Negative k) (Times j l))
          (Times (Times (Negative k) j) l)))
      (symm (Negate-Times-comp-l j l))
      (λ (k-1 IH)
        (equal Integer
          (Plus (Negate (Times j l)) (Times (Negative k-1) (Times j l)))
          #:by (cong (symm (Negate-Times-comp-l j l))
                 (the (-> Integer Integer) (λ (?) (Plus ? (Times (Negative k-1) (Times j l))))))
          (Plus (Times (Negate j) l) (Times (Negative k-1) (Times j l)))
          #:by (cong IH (Plus (Times (Negate j) l)))
          (Plus (Times (Negate j) l) (Times (Times (Negative k-1) j) l))
          #:by (symm (*-dist-l (Negate j) (Times (Negative k-1) j) l))
          (Times (Plus (Negate j) (Times (Negative k-1) j)) l))))))

(claim *-assoc-pos
  (Π ([k Nat]
      [j Integer]
      [l Integer])
    (= Integer
       (Times (Positive k) (Times j l))
       (Times (Times (Positive k) j) l))))
(define *-assoc-pos
  (λ (k j l)
    (ind-Nat k
      (λ (k)
        (= Integer
          (Times (Positive k) (Times j l))
          (Times (Times (Positive k) j) l)))
      (same (Positive 0))
      (λ (k-1 IH)
        (equal Integer
          (Plus (Times j l) (Times (Positive k-1) (Times j l)))
          #:by (cong IH (Plus (Times j l)))
          (Plus (Times j l) (Times (Times (Positive k-1) j) l))
          #:by (symm (*-dist-l j (Times (Positive k-1) j) l))
          (Times (Plus j (Times (Positive k-1) j)) l))))))

(claim *-assoc
  (Π ([j Integer]
      [k Integer]
      [l Integer])
    (= Integer (Times j (Times k l))
       (Times (Times j k) l))))
(define *-assoc
  (λ (k)
    (ind-Int k
      (λ (k) (Π ([j Integer]
                 [l Integer])
               (= Integer
                  (Times k (Times j l))
                  (Times (Times k j) l))))
      *-assoc-neg
      *-assoc-pos)))

;; proof that * is commutative

(claim *-comm-neg
  (Π ([k Nat]
      [j Integer])
    (= Integer
       (Times (Negative k) j)
       (Times j (Negative k)))))
(define *-comm-neg
  (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer
               (Times (Negative k) j)
               (Times j (Negative k))))
      (equal Integer
        (Times (Negative 0) j)
        #:by (symm (flip-is-negate j))
        (Times j (Negative 0)))
      (λ (k-1 IH)
        (equal Integer
          (Times (Negative (add1 k-1)) j)
          #:by (cong IH (Plus (Negate j)))
          (Plus (Negate j) (Times j (Negative k-1)))
          #:by (symm (*-sub1-dist-r j (Negative k-1)))
          (Times j (Negative (add1 k-1))))))))

(claim *-comm-pos
  (Π ([k Nat]
      [j Integer])
    (= Integer
       (Times (Positive k) j)
       (Times j (Positive k)))))
(define *-comm-pos
  (λ (k j)
    (ind-Nat k
      (λ (k) (= Integer
               (Times (Positive k) j)
               (Times j (Positive k))))
      (symm (*-0-r j))
      (λ (k-1 IH)
        (equal Integer
          (Plus j (Times (Positive k-1) j))
          #:by (cong IH (Plus j))
          (Plus j (Times j (Positive k-1)))
          #:by (symm (*-add1-dist-r j (Positive k-1)))
          (Times j (Positive (add1 k-1))))))))

(claim *-comm
  (Π ([k Integer]
      [j Integer])
    (= Integer (Times k j) (Times j k))))
(define *-comm
  (λ (k)
    (ind-Int k
      (λ (k)
        (Π ([j Integer])
          (= Integer (Times k j) (Times j k))))
      *-comm-neg
      *-comm-pos)))



;; TODO basics on just nat times

;; GROUP STUFF: Putting it all together


;; canonical kinds of proofs

(claim is-Assoc
  (Π ([S U])
    (-> (-> S S S) U)))
(define is-Assoc
  (λ (S f)
    (Π ([x S]
        [y S]
        [z S])
       (= S
          (f x (f y z))
          (f (f x y) z)))))

(claim is-Comm
  (Π ([S U])
    (-> (-> S S S) U)))
(define is-Comm
  (λ (S f)
    (Π ([x S]
        [y S])
       (= S
          (f x y)
          (f y x)))))

(claim has-Identity
  (Π ([S U])
    (-> (-> S S S) U)))
(define has-Identity
  (λ (S f)
    (Σ ([e S])
      (Π ([k S])
         (Pair (= S (f e k) k)
               (= S (f k e) k))))))

(claim has-Inverses
  (Π ([S U]
      [f (-> S S S)]
      [e (has-Identity S f)]) U))
(define has-Inverses
  (λ (S f e)
    (Π ([k S])
      (Σ ([k-inv S])
         (Pair
          (= S (f k k-inv) (car e))
          (= S (f k-inv k) (car e)))))))

(claim Distributes-Left
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Distributes-Left
  (λ (S + *)
    (Π ([x S] [y S] [z S])
      (= S
         (* (+ x y) z)
         (+ (* x z) (* y z))))))

(claim Distributes-Right
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Distributes-Right
  (λ (S + *)
    (Π ([x S] [y S] [z S])
      (= S
         (* x (+ y z))
         (+ (* x y) (* x z))))))

(claim No-Proper-Divisors
  (Π ([S U])
    (-> (-> S S S) S U)))
(define No-Proper-Divisors
  (λ (S * z)
    (Π ([x S]
        [y S])
      (-> (= S (* x y) z)
          (Either (= S x z) (= S y z))))))

;; Abstract Algebras
(claim Group
  (Π ([S U])
    (-> (-> S S S) U)))
(define Group
  (λ (S f)
    (Pair (is-Assoc S f)
      (Σ ([e (has-Identity S f)])
        (has-Inverses S f e)))))

(claim Abelian-Group
  (Π ([S U]) (-> (-> S S S) U)))
(define Abelian-Group
  (λ (S f)
    (Pair (Group S f)
      (is-Comm S f))))

(claim Ring
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Ring
  (λ (S + *)
    (Pair (Abelian-Group S +)
      (Pair (is-Assoc S *)
        (Pair (Distributes-Left S + *)
          (Distributes-Right S + *))))))

(claim Ring-With-Unit-Element
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Ring-With-Unit-Element
  (λ (S + *)
    (Pair (Ring S + *)
      (has-Identity S *))))

(claim Commutative-Ring
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Commutative-Ring
  (λ (S + *)
    (Pair (Ring S + *)
      (is-Comm S *))))


(claim Integral-Domain
  (Π ([S U])
    (-> (-> S S S) (-> S S S) U)))
(define Integral-Domain
  (λ (S + *)
    (Pair (Commutative-Ring S + *)
      (Σ ([z S])
        (No-Proper-Divisors S * z)))))



;; putting it all together
(claim +-Has-Identity
  (has-Identity Integer Plus))

(define +-Has-Identity
  (cons (Positive 0)
    (λ (k)
      (cons (+-zero-l k)
        (+-zero-r k)))))

(claim +-has-inverses
  (has-Inverses Integer Plus +-Has-Identity))
(define +-has-inverses
  (λ (k)
    (cons (Negate k)
      (cons (+-inv-r-0 k)
        (+-inv-l-0 k)))))
(claim IntegersFormAGroup
  (Group Integer Plus))
(define IntegersFormAGroup
  (cons +-assoc
    (cons +-Has-Identity
      +-has-inverses)))

(claim PlusIsAnAbelianGroup
  (Abelian-Group Integer Plus))
(define PlusIsAnAbelianGroup
  (cons IntegersFormAGroup
    +-comm))


(claim *-has-identity
  (has-Identity Integer Times))
(define *-has-identity
 (cons (Positive 1)
   (λ (k)
     (cons (*-1-id-l k)
       (*-1-id-r k)))))

(claim Integers-Form-A-Ring
  (Ring Integer Plus Times))
(define Integers-Form-A-Ring
  (cons PlusIsAnAbelianGroup
    (cons *-assoc
      (cons *-dist-l
        *-dist-r))))

(claim Integers-Form-A-Ring-With-Unit-Element
  (Ring-With-Unit-Element Integer Plus Times))
(define Integers-Form-A-Ring-With-Unit-Element
  (cons Integers-Form-A-Ring
    (cons (Positive 1)
      (λ (k)
        (cons (*-1-id-l k)
          (*-1-id-r k))))))

(claim Integers-Form-A-Commutative-Ring
  (Commutative-Ring Integer Plus Times))
(define Integers-Form-A-Commutative-Ring
  (cons Integers-Form-A-Ring
    *-comm))

;; here's the real shit I wanna get cleaned up

(claim Posk+1*Negj=0->Absurd
  (Π ([k Nat]
      [j Nat])
    (-> (= Integer (Times (Positive (add1 k)) (Negative j)) (Positive 0))
        Absurd)))
(define Posk+1*Negj=0->Absurd
  (λ (k j pf)
    ((the (Π ([pr1 (Σ ([n Nat]) (= Integer (Times (Positive (add1 k)) (Negative j))
                                   (Negative n)))])
            Absurd)
       (λ (pr1)
         ((the (-> (Σ ([n2 Nat]) (= Nat (Int->Nat (Negative (car pr1)))
                                 (add1 n2)))
                 Absurd)
            (λ (pr2)
              (use-Nat=
                (add1 (car pr2))
                0
                (trans
                  (symm (cdr pr2))
                  (cong (trans (symm (cdr pr1)) pf)
                    Int->Nat)))))
           (nat-of-negative-nonzero (car pr1)))))
      (add1-pos-times-neg-is-negative k j))))


(claim Posk+1*Posj+1=0->Absurd
  (Π ([k Nat]
      [j Nat])
    (-> (= Integer (Times (Positive (add1 k)) (Positive (add1 j))) (Positive 0))
        Absurd)))
(define Posk+1*Posj+1=0->Absurd
  (λ (k j pf)
    (use-Int=
      (Positive (times (add1 k) (add1 j)))
      (Positive 0)
      (equal Integer
        (Positive (times (add1 k) (add1 j)))
        #:by (symm (Posj-Times-Posk=j-times-k (add1 k) (add1 j)))
        (Times (Positive (add1 k)) (Positive (add1 j)))
        #:by pf
        (Positive 0)))))

(claim Negk*Negj=0->Absurd
  (Π ([k Nat]
      [j Nat])
    (-> (= Integer (Times (Negative k) (Negative j)) (Positive 0))
        Absurd)))
(define Negk*Negj=0->Absurd
  (λ (k j)
    (ind-Nat k
      (λ (k)
        (-> (= Integer (Times (Negative k) (Negative j)) (Positive 0))
          Absurd))
      (λ (pf) (use-Int= (Negate (Negative j)) (Positive 0) pf))
      (λ (k-1 IH pf)
        (use-Nat=
          (add1 (add1 (Int->Nat (Positive (plus j (times (add1 k-1) (add1 j)))))))
          0
          (equal Nat
            (add1 (add1 (Int->Nat (Positive (plus j (times (add1 k-1) (add1 j)))))))
            #:by (same (add1 (add1 (Int->Nat (Positive (plus j (times (add1 k-1) (add1 j))))))))
            (add1 (add1 (Int->Nat (Positive (plus j (times (add1 k-1) (add1 j)))))))
            #:by (cong (symm (Negj-Times-Negk=k+1-times-j+1 (add1 k-1) j)) Int->Nat)
            (Int->Nat (Times (Negative (add1 k-1)) (Negative j)))
            #:by (cong pf Int->Nat)
            0))))))


(claim negate=0->x=0
  (Π ([k Integer])
    (-> (= Integer (Negate k) (Positive 0))
        (= Integer k (Positive 0)))))
(define negate=0->x=0
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
          (λ (p) (same (Positive 0)))
          (λ (pos-1 IH p)
            ((the (-> (Σ ([n Nat]) (= Nat (Int->Nat (Negative pos-1)) (add1 n)))
                     (= Integer (Positive (add1 pos-1)) (Positive 0)))
              (λ (pf)
                (ind-Absurd (use-Nat= (add1 (car pf)) 0 (trans (symm (cdr pf)) (cong p Int->Nat)))
                  (= Integer (Positive (add1 pos-1)) (Positive 0)))))
              (nat-of-negative-nonzero pos-1))))))))


(claim Neg*x=0->x=0
  (Π ([k Nat]
      [x Integer])
    (-> (= Integer (Times (Negative k) x) (Positive 0))
        (Either
          (= Integer (Negative k) (Positive 0))
          (= Integer x (Positive 0))))))

(define Neg*x=0->x=0
  (λ (k)
    (ind-Nat k
      (λ (k)
        (Π ([x Integer])
          (-> (= Integer (Times (Negative k) x) (Positive 0))
            (Either
              (= Integer (Negative k) (Positive 0))
              (= Integer x (Positive 0))))))
      (λ (x -1*x=0)
        (right (negate=0->x=0 x -1*x=0)))
      (λ (k-1 IH x)
        (ind-Int x
          (λ (x)
            (-> (= Integer (Times (Negative (add1 k-1)) x) (Positive 0))
              (Either
                (= Integer (Negative (add1 k-1)) (Positive 0))
                (= Integer x (Positive 0)))))
          (λ (neg pf)
            (ind-Absurd (Negk*Negj=0->Absurd (add1 k-1) neg pf)
              (Either
                (= Integer (Negative (add1 k-1)) (Positive 0))
                (= Integer (Negative neg) (Positive 0)))))
          (λ (pos)
            (ind-Nat pos
              (λ (p)
                (-> (= Integer (Times (Negative (add1 k-1)) (Positive p)) (Positive 0))
                    (Either
                      (= Integer (Negative (add1 k-1)) (Positive 0))
                      (= Integer (Positive p) (Positive 0)))))
              (λ (k-1*0=0) (right (same (Positive 0))))
              (λ (p-1 IH pf)
                (ind-Absurd (Posk+1*Negj=0->Absurd p-1 (add1 k-1)
                              (trans (*-comm (Positive (add1 p-1)) (Negative (add1 k-1)))
                                pf))
                  (Either
                    (= Integer (Negative (add1 k-1)) (Positive 0))
                    (= Integer (Positive (add1 p-1)) (Positive 0))))))))))))

(claim Pos*x=0->x=0
  (Π ([k Nat]
      [x Integer])
    (-> (= Integer (Times (Positive k) x) (Positive 0))
        (Either
          (= Integer (Positive k) (Positive 0))
          (= Integer x (Positive 0))))))
(define Pos*x=0->x=0
  (λ (k)
    (ind-Nat k
      (λ (k)
        (Π ([x Integer])
          (-> (= Integer (Times (Positive k) x) (Positive 0))
            (Either
              (= Integer (Positive k) (Positive 0))
              (= Integer x (Positive 0))))))
      (λ (x 0*x=0)
        (left (same (Positive 0))))
      (λ (k-1 IH x)
        (ind-Int x
          (λ (x)
            (-> (= Integer (Times (Positive (add1 k-1)) x) (Positive 0))
              (Either
                (= Integer (Positive (add1 k-1)) (Positive 0))
                (= Integer x (Positive 0)))))
          (λ (neg pf)
            (ind-Absurd (Posk+1*Negj=0->Absurd k-1 neg pf)
              (Either
                (= Integer (Positive (add1 k-1)) (Positive 0))
                (= Integer (Negative neg) (Positive 0)))))
          (λ (pos)
            (ind-Nat pos
              (λ (p)
                (-> (= Integer (Times (Positive (add1 k-1)) (Positive p)) (Positive 0))
                    (Either
                      (= Integer (Positive (add1 k-1)) (Positive 0))
                      (= Integer (Positive p) (Positive 0)))))
              (λ (k-1*0=0) (right (same (Positive 0))))
              (λ (p-1 IH pf)
                (ind-Absurd (Posk+1*Posj+1=0->Absurd k-1 p-1 pf)
                  (Either
                    (= Integer (Positive (add1 k-1)) (Positive 0))
                    (= Integer (Positive (add1 p-1)) (Positive 0))))))))))))




(claim Zero-Has-No-Proper-Divisors
  (No-Proper-Divisors Integer Times (Positive 0)))
(define Zero-Has-No-Proper-Divisors
  (λ (x)
    (ind-Int x
      (λ (x)
        (Π ([y Integer])
          (-> (= Integer (Times x y) (Positive 0))
            (Either
              (= Integer x (Positive 0))
              (= Integer y (Positive 0))))))
      (λ (neg y x*y=0)
        (Neg*x=0->x=0 neg y x*y=0))
      (λ (pos y x*y=0)
        (Pos*x=0->x=0 pos y x*y=0)))))

(claim Integers-Form-An-Integral-Domain
  (Integral-Domain Integer Plus Times))

(define Integers-Form-An-Integral-Domain
  (cons Integers-Form-A-Commutative-Ring
    (cons Zero
      Zero-Has-No-Proper-Divisors)))

;; End of Document



;; general TODOs

;; TODO: show that Even/Odd and Positive/Negative are interchangeable across
;; I and N. What is Even/Oddness in I?

;; TODO: can we generalize what it means to go from a
;; property on Nats to a property on Integers?
