module Naturals where

data ℕ : Set where -- \bN
  zero : ℕ
  suc  : ℕ -> ℕ
  
seven : ℕ
seven = (suc (suc (suc (suc (suc (suc (suc zero)))))))

-- zero : ℕ
-- suc zero : ℕ
-- suc (suc zero): ℕ
-- suc (suc (suc zero)): ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎
  
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎
  
_ : 2 + 3 ≡ 5
_ = refl


_ : 3 + 4 ≡ 7
_ = begin
      3 + 4
    ≡⟨⟩
      suc (2 + 4)
    ≡⟨⟩
      suc (suc (1 + 4))
    ≡⟨⟩
      suc (suc (suc (0 + 4)))
    ≡⟨⟩
      suc (suc (suc 4))
    ≡⟨⟩
      7
    ∎
    
_⋆_ : ℕ → ℕ → ℕ --\star
zero ⋆ n = zero
(suc m) ⋆ n = n + (m ⋆ n)

_ =
  begin
    2 ⋆ 3
  ≡⟨⟩
    3 + (1 ⋆ 3)
  ≡⟨⟩
    3 + (3 + (0 ⋆ 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎
  
_ =
  begin
    3 ⋆ 4
  ≡⟨⟩
    4 + (2 ⋆ 4)
  ≡⟨⟩
    4 + (4 + (1 ⋆ 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 ⋆ 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ (suc n) = m ⋆ (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 ⋆ (3 ^ 3)
  ≡⟨⟩
    3 ⋆ (3 ⋆ (3 ^ 2))
  ≡⟨⟩
    3 ⋆ (3 ⋆ (3 ⋆ (3 ^ 1)))
  ≡⟨⟩
    3 ⋆ (3 ⋆ (3 ⋆ (3 ⋆ (3 ^ 0))))
  ≡⟨⟩
    3 ⋆ (3 ⋆ (3 ⋆ (3 ⋆ 1)))
  ≡⟨⟩
    81
  ∎
  