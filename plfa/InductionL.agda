-- Induction: Proof by Induction
module InductionL where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Properties of operators

-- Exercise operators (practice)

-- Give another example of a pair of operators that have an identity and are associative, commutative, and distribute over one another.
-- (You do not have to prove these properties.)

-- Union and intersection.
-- ⋂ \I
-- ⋃ \Un
-- ∅ \0

-- Identity
-- A ⋂ 𝕌 = A 𝕌 ⋂ A = A
-- A ⋃ ∅ = A ∅ ⋃ A = A

-- Commutativity
-- A ⋂ B = B ⋂ A
-- A U B = B U A

-- Associativity
-- (A ⋃ B) ⋂ C = (A ⋂ C) ⋃ (B ⋂ C)
-- (A ⋂ B) U C = (A ⋃ C) ⋂ (B ⋃ C)

-- Give an example of an operator that has an identity and is associative but is not commutative. (You do not have to prove these properties.)

-- power ^
-- a ^ 1 = a right identity
-- (a * b) ^ c = a ^ c * b ^ c
 
-- Associativity

-- (m + n) + p ≡ m + (n + p)
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = begin
      (3 + 4) + 5
    ≡⟨⟩
      7 + 5
    ≡⟨⟩
      12
    ≡⟨⟩
      3 + 9
    ≡⟨⟩
      3 + (4 + 5)
    ∎
    
-- Proof by induction

-- Our first proof: associativity

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p = 
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Induction as recursion

+-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
+-assoc-0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎

+-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
+-assoc-1 n p =
  begin
    (1 + n) + p
  ≡⟨⟩
    suc (0 + n) + p
  ≡⟨⟩
    suc ((0 + n) + p)
  ≡⟨ cong suc (+-assoc-0 n p) ⟩
    suc (0 + (n + p))
  ≡⟨⟩ 
    1 + (n + p)
  ∎
  
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩ 
    2 + (n + p)
  ∎

-- Our second proof: commutativity

-- The first lemma

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m -- \^r tab tab
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎

+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- The second lemma

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = 
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n = 
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- The proposition

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Our first corollary: rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
   ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎
  
-- Creation, one last time

-- Exercise finite-+-assoc (stretch)

-- In the beginning, we know nothing.

-- On the first day, we know zero.
-- 0 : ℕ
-- (0 + 0) + 0 = 0 + (0 + 0)

-- On the second day
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 = 0 + (0 + 0)

-- 0 0 1 (0 + 0) + 1 = 0 + (0 + 1)
-- 0 1 0
-- 0 1 1
-- 1 0 0
-- 1 0 1
-- 1 1 0
-- 1 1 1 (1 + 1) + 1 = 1 + (1 + 1)

-- On the third day
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 = 0 + (0 + 0)
-- 2 : ℕ    (0 + 0) + 1 = 0 + (0 + 1) ... (1 + 1) + 1 = 1 + (1 + 1)


-- Associativity with rewrite
+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

-- Commutativity with rewrite

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n  rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

-- Building proofs interactively

+-assoc'' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc'' zero n p = refl
+-assoc'' (suc m) n p rewrite +-assoc'' m n p = refl

-- Exercise +-swap (recommended)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm' m (n + p) | +-assoc'' n p m | +-comm' p m = refl

-- Exercise *-distrib-+ (recommended)

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p  rewrite *-distrib-+ m n p | +-assoc p (m * p)  (n * p) = refl

-- Exercise *-assoc (recommended)

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

-- Exercise *-comm (practice)

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-identity : ∀ (m : ℕ) → m * 1 ≡ m
*-identity zero = refl
*-identity (suc m) rewrite *-identity m = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zero m = refl
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

-- Exercise 0∸n≡0 (practice)

∸-zero : ∀ (n : ℕ) → zero ∸ n ≡ zero -- \.-
∸-zero zero = refl
∸-zero (suc n) = refl 

∸-identity : ∀ (n : ℕ) → n ∸ zero ≡ n -- \.-
∸-identity zero = refl
∸-identity (suc n) = refl 

∸-suc : ∀ (m n : ℕ) → suc m ∸ suc n ≡ m ∸ n
∸-suc m n = refl

-- Exercise ∸-+-assoc (practice)

-- a bad try: induction by m

-- ∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
-- ∸-+-assoc zero n p rewrite ∸-zero n | ∸-zero p | ∸-zero (n + p) = refl
-- ∸-+-assoc (suc m) n p = {!   !}

-- solution: induction by n then by m
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite ∸-zero (suc n) | ∸-zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- a bad try: induction by p
-- ∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
-- ∸-+-assoc m n zero rewrite +-comm n zero = refl
-- ∸-+-assoc m n (suc p) rewrite +-suc n p = {!   !}

--- Сделал три попытки индукции по m n или p пока ничего не дало

-- 0 - 0 - 0 = 0 - (0 + 0)
-- 1 - 0 - 0 = 1 - (0 + 0)
-- 1 - 1 - 0 = 1 - (1 + 0)
-- 1 - 0 - 1 = 1 - (0 + 1)
-- suc 1 - 1 - 1 = suc 1 - (1 + 1)
-- suc m ∸ n ∸ p ≡ suc m ∸ (n + p)
-- m ∸ n ∸ p ≡ m ∸ (n + p) ---- H
-- m ∸ suc n = m ∸ (n + 1) 

-- monus definition
-- _∸_ : ℕ → ℕ → ℕ --\.-
-- m ∸ zero = m
-- zero ∸ suc n = zero
-- suc m ∸ suc n = m ∸ n

-- Exercise +*^ (stretch)

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity' (m ^ p) = refl
^-distribˡ-+-* m (suc n) p  rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

-- induction by m - don;t know what to do
-- ^-distribˡ-+-*' : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
-- ^-distribˡ-+-*' zero n p = {!   !}
-- ^-distribˡ-+-*' (suc m) n p = {!   !}

-- definition of ^
-- _^_ : ℕ → ℕ → ℕ
-- m ^ zero = suc zero
-- m ^ (suc n) = m ⋆ (m ^ n)

-- *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
-- *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)  
  rewrite 
    ^-distribʳ-* m n p
  | *-assoc m n (m ^ p * n ^ p)
  | *-comm n (m ^ p * n ^ p)
  | *-assoc m  (m ^ p) (n * n ^ p)
  | *-assoc (m ^ p) (n ^ p) n
  | *-comm (n ^ p) n
  = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero
  rewrite *-zero n = refl
^-*-assoc m n (suc p)
  rewrite
    ^-*-assoc m n p
  | *-suc n p
  | ^-distribˡ-+-* m n (n * p)
  = refl

-- *-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
-- ^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)

-- Exercise Bin-laws (stretch)

-- I copied data Bin from Naturals.agda

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (b O)
  rewrite
    +-identityʳ (from b)
  | +-suc (from b + from b) zero
  | +-identityʳ (from b + from b)
  = refl
from-inc (b I)
  rewrite
    from-inc b
  | +-identityʳ (suc (from b))
  | +-identityʳ (from b)
  | +-suc (from b) (from b)
  | +-assoc (from b) (from b) 1
  | +-suc (from b) zero
  | +-identityʳ (from b)
  | +-suc (from b) (from b)
  = refl

-- +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m -- \^r tab tab
-- +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n)
  rewrite
    from-inc (to n)
  | from-to n
  = refl
  
to-from : ∀ (b : Bin) → from (to (from b)) ≡ from b
to-from ⟨⟩ = refl
to-from (b O)
  rewrite
    +-identityʳ (from b)
  | from-to (from b + from b)
   = refl
to-from (b I)
  rewrite
    from-to (from (b I))
  = refl
  
-- Standard library

import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

-- Unicode
-- This chapter uses the following unicode:

-- ∀  U+2200  FOR ALL (\forall, \all)
-- ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
-- ′  U+2032  PRIME (\')
-- ″  U+2033  DOUBLE PRIME (\')
-- ‴  U+2034  TRIPLE PRIME (\')
-- ⁗  U+2057  QUADRUPLE PRIME (\')
-- Similar to \r, the command \^r gives access to a variety of superscript rightward arrows, and also a superscript letter r. The command \' gives access to a range of primes (′ ″ ‴ ⁗).
