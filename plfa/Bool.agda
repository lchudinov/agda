-- https://www.youtube.com/watch?v=tRnsIWKqL34&list=PLjrvwaWr1SVHzlbdcWibCKs-fomm4uBrc&index=1&pp=iAQB
module Bool where

data 𝔹 : Set where --\bB
  true : 𝔹
  false : 𝔹

if_then_else_ : {A : Set} → 𝔹 → A → A → A  --\to
if true then a else b = a
if false then a else b = b

infixr 30 _∧_ --\and

_∧_ : 𝔹 → 𝔹 → 𝔹
true ∧ b = b
_ ∧ _ = false

infixr 20 _∨_ --\or

_∨_ : 𝔹 → 𝔹 → 𝔹
false ∨ b = b
_ ∨ _ = true

infix 40 ¬_ --\neg

¬_ : 𝔹 → 𝔹
¬ true = false
¬ false = true

infix 4 _≡_ --\==

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

DeMorgan-law₁ : (a b : 𝔹) → ¬ (a ∧ b) ≡ ¬ a ∨ ¬ b --\_1
DeMorgan-law₁ true b = refl
DeMorgan-law₁ false b = refl

DeMorgan-law₂ : (a b : 𝔹) → ¬ (a ∨ b) ≡ ¬ a ∧ ¬ b --\_2
DeMorgan-law₂ true b = refl
DeMorgan-law₂ false b = refl





