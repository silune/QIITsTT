
\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat

module TTSyntax where

-- Initlial model (syntax) for the type theory

module I where

  infixr 6 _[_]
  infixr 6 _⟦_⟧
  infixr 5 _▷_

  postulate
  
    -- There is 4 sorts :
    Con   : Set
    Ty    : Con → Set
    Sub   : Con → Con → Set
    Tm    : (Γ : Con) → Ty Γ → Set
    
    -- Contexts
    ○     : Con
    _▷_   : (Γ : Con) → Ty Γ → Con
    
    -- Types
    U     : {Γ : Con} → Ty Γ
    El    : {Γ : Con} → Tm Γ U → Ty Γ
    _[_]  : {Δ Γ : Con} → Ty Γ → Sub Δ Γ → Ty Δ
    Π     : {Γ : Con}→ (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
    
    -- Substitutions
    ρ     : {Γ : Con}{A : Ty Γ} → Sub (Γ ▷ A) Γ
    ⟨_⟩    : {Γ : Con}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▷ A)
    _⁺    : {Δ Γ : Con}{A : Ty Γ} → (σ : Sub Δ Γ) → Sub (Δ ▷ A [ σ ]) (Γ ▷ A)
    
    -- Terms
    _⟦_⟧  : {Δ Γ : Con}{A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
    q     : {Γ : Con}{A : Ty Γ} → Tm (Γ ▷ A) (A [ ρ ])
    lam   : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
    app   : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm Γ (Π A B) → Tm (Γ ▷ A) B

    -- then the equations
    Π[]   : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{σ : Sub Δ Γ} → Π A B [ σ ] ≡ Π (A [ σ ]) (B [ σ ⁺ ])
    β     : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B} → app (lam t) ≡ t
    η     : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
    -- some requires transport
    lam[] : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → transp⟨ Tm Δ ⟩ Π[] ((lam t) ⟦ σ ⟧) ≡ lam (t ⟦ σ ⁺ ⟧)
    U[]   : {Γ Δ : Con}{σ : Sub Δ Γ} → U [ σ ] ≡ U
    El[]  : {Γ Δ : Con}{a : Tm Γ U}{σ : Sub Δ Γ} → (El a) [ σ ] ≡ El (transp⟨ Tm Δ ⟩ U[] (a ⟦ σ ⟧))
    -- some even requires additional equalities
    q⟨⟩    : {Γ : Con}{A : Ty Γ}{u : Tm Γ A} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (q ⟦ ⟨ u ⟩ ⟧) ≡ u
    q+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (q ⟦ σ ⁺ ⟧) ≡ q
    p⟨⟩    : {Γ : Con}{A B : Ty Γ}{t : Tm Γ A}{u : Tm Γ B} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (t ⟦ ρ ⟧ ⟦ ⟨ u ⟩ ⟧) ≡ t
    p+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Γ A} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (t ⟦ ρ ⟧ ⟦ σ ⁺ ⟧) ≡ t ⟦ σ ⟧ ⟦ ρ ⟧
    
    

\end{code}
