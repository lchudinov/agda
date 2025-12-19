{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical

infixr 5 _∷_

variable
  A : Set
  x : A
  
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A
  


 