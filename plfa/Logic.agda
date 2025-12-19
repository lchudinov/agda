-- https://www.youtube.com/watch?v=s5NeZDnF79Q&list=PLjrvwaWr1SVHzlbdcWibCKs-fomm4uBrc&index=2&pp=iAQB

module Logic where

-- Единичный тип Top

data ⊤ : Set where --\top
  tt : ⊤
  
-- Пустой тип Bottom

data ⊥ : Set where --\bot

-- Ex Falso позволяет вывести из путого типа любое утверждение

⊥-elim : { A : Set } → ⊥ → A
⊥-elim = λ () --\lambda or \G1

-- Ex Falso 2

⊥→⊥ : ⊥ → ⊤
⊥→⊥ _ = tt

-- Функциональный тип

implies₁ : ⊤ → ⊤
implies₁ x = x

implies₂ : ⊥ → ⊥
implies₂ x = x

implies₃ : ⊥ → ⊤
implies₃ x = ⊥-elim x

implies₄ : ⊤ → ⊥
implies₄ x = {!   !}


proof₁ : {A : Set} → A → A
proof₁ a = a

!proof : {A B : Set} → A → B
!proof = {!   !}

proof₂ : {A B : Set} → A → (B → B)
proof₂ _ = λ x → x

proof₃ : {P Q R : Set} → (P → Q → R) → (P → Q) → P → R
proof₃ f g x = (f x) (g x)

axiom₁ : {A B : Set} → A → (B → A)
axiom₁ a = λ _ → a

axiom₂ : {A B C : Set} → (A → B) → ((B → C) → (A → C))
axiom₂ f g h = g (f h)

-- Pair type

data _×_ (A : Set) (B : Set) : Set where --\x
  <_,_> : A → B → (A × B)

infixr 4 <_,_>

axiom₃ : {A B : Set} → A → (B → A × B)
axiom₃ a b = < a , b >

axiom₄ : {A B : Set} → (A × B) → A
axiom₄ < a , b > = a

axiom₅ : {A B : Set} → (A × B) → B
axiom₅ < a , b > = b

-- Sum type

data _∣_ (A B : Set) : Set where --\|
  Left : A → A ∣ B
  Right : B → A ∣ B

axiom₆ : {A B : Set} → A → A ∣ B
axiom₆ = Left

axiom₇ : {A B : Set} → B → A ∣ B
axiom₇ = Right

axiom₈ : {A B C : Set} → (A → C) → ((B → C) → (A ∣ B → C))
axiom₈ f g (Left a) = f a
axiom₈ f g (Right b) = g b

¬ : Set → Set --\neg
¬ A = A → ⊥

axiom₉ : {A B : Set} → (A → B) → ((A → ¬ B) → ¬ A)
axiom₉ f g h = g h (f h)
-- (A → B) → (A → B → ⊥) → A → ⊥

axiom₁₀ : {A B : Set} → ¬ A → (A → B)
axiom₁₀ f a = ⊥-elim (f a)

axiom₁₁ : {A : Set}{P : A → Set} → ((a : A)  → P a) → (a₁ : A) → P a₁
axiom₁₁ f = f

data Σ (A : Set) (P : A → Set) : Set where --\Sigma
  ⟨_,_⟩ : (a : A) → P a → Σ A P --\< \>
  
∃ : (A : Set) → (P : A → Set) → Set --\ex
∃ A P = Σ A P

axiom₁₂ : (A : Set) → (P : A → Set) → Set
axiom₁₂ = ∃


-- Exercises

-- 1.

_⇔_ : Set → Set → Set --\<=>
A ⇔ B = (A → B) × (B → A)

-- -- 2.
-- ×-comm : {P Q : Set} → (P × Q) ⇔ (Q × P)
-- ×-comm =
--   < (λ < p , q > → < q , p >)
--   , (λ < q , p > → < p , q >)
--   >












