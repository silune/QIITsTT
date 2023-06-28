
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
    _[_]  : {Γ Δ : Con} → Ty Γ → Sub Δ Γ → Ty Δ
    Π     : {Γ : Con}→ (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
    
    -- Substitutions
    ρ     : {Γ : Con}{A : Ty Γ} → Sub (Γ ▷ A) Γ
    ⟨_⟩    : {Γ : Con}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▷ A)
    _⁺    : {Γ Δ : Con}{A : Ty Γ} → (σ : Sub Δ Γ) → Sub (Δ ▷ A [ σ ]) (Γ ▷ A)
    
    -- Terms
    _⟦_⟧  : {Γ Δ : Con}{A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
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
    
--------------------------------------------------

-- We can now define the Model in a first time and its recursor :

record Model {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]
  infixr 6 _⟦_⟧
  infixr 5 _▷_

  field
  
    Con   : Set lc
    Ty    : Con → Set lty
    Sub   : Con → Con → Set ls
    Tm    : (Γ : Con) → Ty Γ → Set ltm
    
    ○     : Con
    _▷_   : (Γ : Con) → Ty Γ → Con
    
    U     : {Γ : Con} → Ty Γ
    El    : {Γ : Con} → Tm Γ U → Ty Γ
    _[_]  : {Γ Δ : Con} → Ty Γ → Sub Δ Γ → Ty Δ
    Π     : {Γ : Con}→ (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
    
    ρ     : {Γ : Con}{A : Ty Γ} → Sub (Γ ▷ A) Γ
    ⟨_⟩    : {Γ : Con}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▷ A)
    _⁺    :  {Γ Δ : Con}{A : Ty Γ} → (σ : Sub Δ Γ) → Sub (Δ ▷ A [ σ ]) (Γ ▷ A)
    
    _⟦_⟧  : {Γ Δ : Con}{A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
    q     : {Γ : Con}{A : Ty Γ} → Tm (Γ ▷ A) (A [ ρ ])
    lam   : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
    app   : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm Γ (Π A B) → Tm (Γ ▷ A) B

    Π[]   : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{σ : Sub Δ Γ} → Π A B [ σ ] ≡ Π (A [ σ ]) (B [ σ ⁺ ])
    β     : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B} → app (lam t) ≡ t
    η     : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
    lam[] : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → transp⟨ Tm Δ ⟩ Π[] ((lam t) ⟦ σ ⟧) ≡ lam (t ⟦ σ ⁺ ⟧)
    U[]   : {Γ Δ : Con}{σ : Sub Δ Γ} → U [ σ ] ≡ U
    El[]  : {Γ Δ : Con}{a : Tm Γ U}{σ : Sub Δ Γ} → (El a) [ σ ] ≡ El (transp⟨ Tm Δ ⟩ U[] (a ⟦ σ ⟧))
    q⟨⟩    : {Γ : Con}{A : Ty Γ}{u : Tm Γ A} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (q ⟦ ⟨ u ⟩ ⟧) ≡ u
    q+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (q ⟦ σ ⁺ ⟧) ≡ q
    p⟨⟩    : {Γ : Con}{A B : Ty Γ}{t : Tm Γ A}{u : Tm Γ B} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (t ⟦ ρ ⟧ ⟦ ⟨ u ⟩ ⟧) ≡ t
    p+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Γ A} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (t ⟦ ρ ⟧ ⟦ σ ⁺ ⟧) ≡ t ⟦ σ ⟧ ⟦ ρ ⟧

  postulate
    ⟦_⟧C   : I.Con → Con
    ⟦_⟧T   : {Γ : I.Con} → I.Ty Γ → Ty ⟦ Γ ⟧C
    ⟦_⟧S   : {Γ Δ : I.Con} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
    ⟦_⟧t   : {Γ : I.Con}{A : I.Ty Γ} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T
    
    ⟦○⟧C   : ⟦ I.○ ⟧C ≡ ○
    ⟦▷⟧C   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ Γ I.▷ A ⟧C ≡ ⟦ Γ ⟧C ▷ ⟦ A ⟧T
    {-# REWRITE ⟦○⟧C ⟦▷⟧C #-}

    ⟦U⟧T   : {Γ : I.Con} → ⟦ I.U {Γ} ⟧T ≡ U {⟦ Γ ⟧C}
    {-# REWRITE ⟦U⟧T #-}
    ⟦El⟧T  : {Γ : I.Con}{t : I.Tm Γ I.U} → ⟦ I.El t ⟧T ≡ El ⟦ t ⟧t
    ⟦[]⟧T  : {Δ Γ : I.Con}{A : I.Ty Γ}{σ : I.Sub Δ Γ} → ⟦ A I.[ σ ] ⟧T ≡ ⟦ A ⟧T [ ⟦ σ ⟧S ]
    ⟦Π⟧T   : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)} → ⟦ I.Π A B ⟧T ≡ Π ⟦ A ⟧T ⟦ B ⟧T
    {-# REWRITE ⟦El⟧T ⟦[]⟧T ⟦Π⟧T #-}

    ⟦ρ⟧S   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ I.ρ {Γ}{A} ⟧S ≡ ρ {⟦ Γ ⟧C}{⟦ A ⟧T}
    ⟦⟨⟩⟧S   : {Γ : I.Con}{A : I.Ty Γ}{u : I.Tm Γ A} → ⟦ I.⟨ u ⟩ ⟧S ≡ ⟨ ⟦ u ⟧t ⟩
    ⟦+⟧S   : {Γ Δ : I.Con}{A : I.Ty Γ}{σ : I.Sub Δ Γ} → ⟦ I._⁺ {_}{_}{A} σ ⟧S ≡ ⟦ σ ⟧S ⁺
    {-# REWRITE ⟦ρ⟧S ⟦⟨⟩⟧S ⟦+⟧S #-}

    ⟦⟦⟧⟧t  : {Γ Δ : I.Con}{A : I.Ty Γ}{t : I.Tm Γ A}{σ : I.Sub Δ Γ} → ⟦ t I.⟦ σ ⟧ ⟧t ≡ ⟦ t ⟧t ⟦ ⟦ σ ⟧S ⟧
    ⟦q⟧t   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ I.q {Γ}{A} ⟧t ≡ q
    ⟦lam⟧t : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)}{t : I.Tm (Γ I.▷ A) B} → ⟦ I.lam t ⟧t ≡ lam ⟦ t ⟧t
    ⟦app⟧t : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)}{t : I.Tm Γ (I.Π A B)} → ⟦ I.app t ⟧t ≡ app ⟦ t ⟧t
    {-# REWRITE ⟦⟦⟧⟧t ⟦q⟧t ⟦lam⟧t ⟦app⟧t #-}

\end{code}
