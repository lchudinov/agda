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
