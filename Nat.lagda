\begin{code}

{-# OPTIONS --prop --rewriting #-}

open import Logic
open import Equality

module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

NatDecEq : (n n' : ℕ) → (n ≡ n') ∨ ¬ (n ≡ n')
NatDecEq (zero  ) (zero  ) = left refl
NatDecEq (succ a) (zero  ) = right (λ ())
NatDecEq (zero  ) (succ b) = right (λ ())
NatDecEq (succ a) (succ b) with NatDecEq a b
...            | left refl = left refl
...            | right a≠b = right (λ {refl → a≠b refl})


\end{code}
