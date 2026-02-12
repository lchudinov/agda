module RelationsL where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)  -- \^r tab tab tab

-- Defining relations

data _≤_ : ℕ → ℕ → Set where -- \<=

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n
  
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      --------
    → suc m ≤ suc n
    
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 1 ≤ 2
_ = s≤s z≤n

_ : 1 ≤ 1
_ = s≤s z≤n

-- _ : 1 ≤ 0
-- _ = s≤s z≤n


-- Implicit arguments
