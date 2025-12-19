module Naturals where

data 𝐍 : Set where
  zero : 𝐍
  suc  : 𝐍 -> 𝐍
  
seven : 𝐍
seven = (suc (suc (suc (suc (suc (suc (suc zero)))))))

-- zero : 𝐍
-- suc zero : 𝐍
-- suc (suc zero): 𝐍
-- suc (suc (suc zero)): 𝐍

{-# BUILTIN NATURAL 𝐍 #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : 𝐍 -> 𝐍 -> 𝐍
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
  

