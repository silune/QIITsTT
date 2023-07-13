
\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat
open import TTSyntax

module TTInterp where

-- We can, as an example, define the Standard Model :

St : Model
St = record
   { Con   = Set
   ; Ty    = Set
   ; Sub   = λ Γ Δ → (Γ → Δ)
   ; Tm    = λ Γ A → (Γ → A)
   ; ○     = 𝟙
   ; _▷_   = _×_
   ; ι     = 𝟙
   ; _⇒_   = λ A B → (A → B)
   ; _∘_   = λ σ ρ → (λ γ → σ (ρ γ))
   ; id    = λ γ → γ
   ; ε     = λ _ → ★
   ; _‣_   = λ σ t → (λ δ → σ δ , t δ)
   ; p     = π₁
   ; _[_]  = λ t σ → (λ δ → t (σ δ))
   ; q     = π₂
   ; lam   = λ t → (λ γ → (λ a → t (γ , a)))
   ; _$_   = λ u v → (λ γ → (u γ) (v γ))
   ; β     = refl
   ; η     = refl
   ; [][]  = refl
   ; q[]   = refl
   ; lam[] = refl
   ; $[]   = refl
   ; t[id] = refl
   ; ass   = refl
   ; idl   = refl
   ; idr   = refl
   ; ○η    = λ {_}{σ} → funext λ x → ★-uniqueness (σ x) ★
   ; ▷β    = refl
   ; ▷η    = refl
   }

\end{code}
