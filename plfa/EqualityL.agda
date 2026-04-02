-- Equality: Equality and equational reasoning

module EqualityL where

-- Equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  
infix 4 _≡_

-- Equality is an equivalence relation

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
-- sym e = {!   !} --  if in the hole we type `C-c C-c e` then Agda will instantiate `e` to all possible constructors, with one equation for each.
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl




