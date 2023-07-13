
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
   ; _▷_   = λ Γ A → Γ × A
   ; ι     = 𝟙
   ; _⇒_   = λ A B → (A → B)
   ; ρ     = pr₁
   ; ⟨_⟩    = λ u → (λ γ → γ , u γ)
   ; _⁺    = λ σ → (λ {(γ , u) → σ γ , u})
   ; _[_]  = λ u σ → (λ γ → u (σ γ))
   ; q     = pr₂
   ; lam   = λ t → (λ γ x → t (γ , x))
   ; _$_   = λ f x → (λ γ → f γ (x γ))
   ; β     = refl
   ; η     = refl
   ; lam[] = refl
   ; $[]   = refl
   ; q⟨⟩    = refl
   ; q+    = refl
   ; ρ⟨⟩    = refl
   ; ρ+    = refl
   }

\end{code}
