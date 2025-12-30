module hello-world-proof where
  
open import Data.Nat using (ℕ; _+_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality using (refl; cong)

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

+-assoc-proof : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc-proof zero y z = refl
+-assoc-proof (suc x) y z = cong suc (+-assoc-proof x y z)


-- To get detailed information about a specific hole, put the cursor in it and press C-c C-,
-- To perform a case split on a variable, put the cursor inside the hole and press C-c C-c
-- With Refine C-c C-r it you can easily resolve the first hole +-assoc-proof zero y z = {!   !} by putting the cursor in it and pressing C-c C-r
-- We write cong suc in the second hole and press C-c C-r to refine the hole.

-- To finish the proof, now make a recursive call +-assoc-proof x y z.
-- Note that this has type x + (y + z) ≡ (x + y) + z, which is exactly what we need.
-- To complete the proof, type +-assoc-proof x y z into the hole and solve it with C-c C-space.
-- This replaces the hole with the given term and completes the proof.
