\begin{code}

{-# OPTIONS --prop #-}

open import Agda.Primitive

module Logic where

  infixr 4 _,_
  infixr 5 _∨_
  infixr 6 _∧_

  -- Unit type Prop
  data ⊤ : Prop where
    triv : ⊤

  -- Unit type Set
  data 𝟙 {l} : Set l where
    ★ : 𝟙

  -- Empty type Prop
  data ⊥ : Prop where

  ⊥-elim : ∀{l}{A : Set l} → ⊥ → A
  ⊥-elim ()

  -- Empty type Set
  data 𝟘 {l} : Set l where

  𝟘-elim : ∀{l}{l'}{A : Set l} → 𝟘 {l'} → A
  𝟘-elim ()

  -- Bool type
  data 𝟚 {l} : Set l where
    tt : 𝟚
    ff : 𝟚
  
  -- Negation
  ¬ : Prop → Prop
  ¬ A = A → ⊥

  -- Conjunction
  data _∧_ (A B : Prop) : Prop where
    _∧,_ : A → B → A ∧ B

  -- Disjunction
  data _∨_ (A B : Prop) : Prop where
    left  : A → A ∨ B
    right : B → A ∨ B

  -- Existential Quantifier

  record Σ {l}{l'} (A : Set l) (B : A → Set l') : Set (l ⊔ l') where
    constructor _,_
    field
      π₁ : A
      π₂ : B π₁
  open Σ public

  _×_ : ∀{l}{l'} (A : Set l) (B : Set l') → Set (l ⊔ l')
  A × B = Σ A (λ _ → B)

  data _⨄_ {l}{l'} (A : Set l) (B : Set l') : Set (l ⊔ l') where
    ι₁ : A → A ⨄ B
    ι₂ : B → A ⨄ B
       

\end{code}
