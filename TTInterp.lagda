
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
  { Con = Set
  ; Ty = λ Γ → (Γ → Set)
  ; Sub = λ Γ Δ → (Γ → Δ)
  ; Tm = λ Γ A → ((γ : Γ) → A γ)
  -- Contexts are Σ types (of terms ?)
  ; ○ = 𝟙 
  ; _▷_ = λ Γ A → Σ Γ A
  -- Types Are usual types, we don't care about U and El
  ; U = λ _ → 𝟘
  ; El = λ ()
  ; _[_] = λ A σ δ → A (σ δ)
  ; Π = λ A B γ → ((a : A γ) → (B (γ , a)))
  -- Substitutions are functions between contexts
  ; ρ = pr₁
  ; ⟨_⟩ = λ u γ → (γ , u γ)
  ; _⁺ = λ σ → (λ {(δ , a)  → (σ δ) , a})
  -- Terms are functions from a context into a type over this context
  ; _⟦_⟧ = λ u σ → (λ γ → u (σ γ))
  ; q = pr₂
  ; lam = λ u → (λ γ → (λ x → u (γ , x)))
  ; app = λ u → (λ {(γ , a) → u γ a})
  -- equations are by refl
  ; Π[] = refl
  ; β = refl
  ; η = refl
  ; lam[] = refl
  ; U[] = refl
  ; El[] = refl
  ; q⟨⟩ = λ {refl → refl}
  ; q+ = λ {refl → refl}
  ; p⟨⟩ = λ {refl → refl}
  ; p+ = λ {refl → refl}
  }

\end{code}
