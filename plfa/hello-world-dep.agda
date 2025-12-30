module hello-world-dep where
  
open import Data.Nat using (ℕ; zero; suc) --\bN

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n) --\all

infixr 5 _∷_

-- You can let Agda infer the type of an expression using the ‘Deduce type’ command (C-c C-d).
