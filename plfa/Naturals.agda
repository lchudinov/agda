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
  
-- Monus

_∸_ : ℕ → ℕ → ℕ --\.-
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎
  
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎
  
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Precedence

infixl 6 _+_ _∸_
infixl 7 _⋆_

-- Currying

-- The story of creation, revisited
-- The story of creation, finitely
-- Writing definitions interactively

-- C-c C-c case split
-- C-c C-, displays info about the hole
-- C-c C-r refine
-- C-c C-Space 

_++_ : ℕ → ℕ → ℕ
zero ++ n = n 
suc m ++ n = suc (m + n) 

-- More pragmas

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _⋆_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise Bin (stretch)
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
from (x O) = 2 ⋆ (from x)
from (x I) = 2 ⋆ (from x) + 1

_ = begin
  from (⟨⟩ I)
  ≡⟨⟩ 1
  ∎

_ = begin
  from (⟨⟩ I O)
  ≡⟨⟩ 2
  ∎
  
_ = begin
  from (⟨⟩ I I)
  ≡⟨⟩ 3
  ∎
  
_ = begin
  from (⟨⟩ I O O)
  ≡⟨⟩ 4
  ∎
  
_ = begin
  to 6
  ≡⟨⟩ ⟨⟩ I I O
  ∎
  
-- Standard library

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)


