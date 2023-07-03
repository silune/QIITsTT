
\begin{code}

{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

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
    El    : {Γ : Con} → Ty (Γ ▷ U)
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
    U[]   : {Γ Δ : Con}{σ : Sub Δ Γ} → U [ σ ] ≡ U
    -- some requires transport
    lam[] : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → transp⟨ Tm Δ ⟩ Π[] ((lam t) ⟦ σ ⟧) ≡ lam (t ⟦ σ ⁺ ⟧)
    El[]  : {Γ Δ : Con}{σ : Sub Δ Γ} → transp⟨ (λ A → Ty (Δ ▷ A)) ⟩ U[] (El [ σ ⁺ ]) ≡ El
    -- some even requires additional equalities
    q⟨⟩    : {Γ : Con}{A : Ty Γ}{u : Tm Γ A} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (q ⟦ ⟨ u ⟩ ⟧) ≡ u
    q+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (q ⟦ σ ⁺ ⟧) ≡ q
    ρ⟨⟩    : {Γ : Con}{A B : Ty Γ}{t : Tm Γ A}{u : Tm Γ B} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (t ⟦ ρ ⟧ ⟦ ⟨ u ⟩ ⟧) ≡ t
    ρ+    : {Γ Δ : Con}{A B : Ty Γ}{σ : Sub Δ Γ}{t : Tm Γ A} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (B [ σ ])) ⟩ e (t ⟦ ρ ⟧ ⟦ σ ⁺ ⟧) ≡ t ⟦ σ ⟧ ⟦ ρ ⟧
    
--------------------------------------------------

-- We can now define the Dependent Model its recursor :

record DepModel {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]•
  infixr 6 _⟦_⟧•
  infixr 5 _▷•_

  field
  
    Con•   : I.Con → Set lc
    Ty•    : ∀{Γ} → Con• Γ → I.Ty Γ → Set lty
    Sub•   : ∀{Γ Δ} → Con• Δ → Con• Γ → I.Sub Δ Γ → Set ls
    Tm•    : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• Γ• A → I.Tm Γ A → Set ltm
    
    ○•     : Con• I.○
    _▷•_   : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• Γ• A → Con• (Γ I.▷ A) 
    
    U•     : ∀{Γ}{Γ• : Con• Γ} → Ty• Γ• I.U
    El•    : ∀{Γ}{Γ• : Con• Γ} → Ty• (Γ• ▷• U•) (I.El)
    _[_]•  : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A} → Ty• Γ• A → ∀{σ} → Sub• Δ• Γ• σ → Ty• Δ• (A I.[ σ ])
    Π•     : ∀{Γ}{Γ• : Con• Γ} → ∀{A} → (A• : Ty• Γ• A) → ∀{B} → (B• : Ty• (Γ• ▷• A•) B) → Ty• Γ• (I.Π A B)

    ρ•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A} → Sub• (Γ• ▷• A•) Γ• I.ρ
    ⟨_⟩•    : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A} → ∀{u} → Tm• Γ• A• u → Sub• Γ• (Γ• ▷• A•) I.⟨ u ⟩
    _⁺•    : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• Γ• A}{σ} → (σ• : Sub• Δ• Γ• σ) → Sub• (Δ• ▷• A• [ σ• ]•) (Γ• ▷• A•) (σ I.⁺)
    
    _⟦_⟧•  : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• Γ• A}{u} → Tm• Γ• A• u → ∀{σ} → (σ• : Sub• Δ• Γ• σ) →
             Tm• Δ• (A• [ σ• ]•) (u I.⟦ σ ⟧)
    q•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A} →
             Tm• (Γ• ▷• A•) (A• [ ρ• ]•) I.q
    lam•   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{u} → Tm• (Γ• ▷• A•) B• u →
             Tm• Γ• (Π• A• B•) (I.lam u)
    app•   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{u} → Tm• Γ• (Π• A• B•) u →
             Tm• (Γ• ▷• A•) B• (I.app u)

    Π[]•   : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Ty• Δ• ⟩ I.Π[] (Π• A• B• [ σ• ]•) ≡ Π• (A• [ σ• ]•) (B• [ σ• ⁺• ]•)
    β•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{t}{t• : Tm• (Γ• ▷• A•) B• t} →
             transp⟨ Tm• (Γ• ▷• A•) B• ⟩ I.β (app• (lam• t•)) ≡ t•
    η•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{t}{t• : Tm• Γ• (Π• A• B•) t} →
             transp⟨ Tm• Γ• (Π• A• B•) ⟩ I.η (lam• (app• t•)) ≡ t•
    U[]•   : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{σ}{σ• : Sub• Δ• Γ• σ} → transp⟨ Ty• Δ• ⟩ I.U[] (U• [ σ• ]•) ≡ U•
    lam[]• : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• Γ• A}{B}{B• : Ty• (Γ• ▷• A•) B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ (λ {(C , C• , t) → Tm• Δ• C• t}) ⟩ (I.Π[] ,= trans (transp× I.Π[]) (Π[]• ,×= I.lam[]))
             ((lam• t•) ⟦ σ• ⟧•) ≡ lam• (t• ⟦ σ• ⁺• ⟧•)
    El[]•  : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{a}{a• : Tm• Γ• U• a}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ (λ {(C , C• , B) → Ty• (Δ• ▷• C•) B}) ⟩ (I.U[] ,= trans (transp× I.U[]) (U[]• ,×= I.El[]))
             (El• [ σ• ⁺• ]•) ≡ El•
    q⟨⟩•    : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• Γ• A}{u}{u• : Tm• Γ• A• u}{e : A I.[ I.ρ ] I.[ I.⟨ u ⟩ ] ≡ A} →
             (e• : transp⟨ Ty• Γ• ⟩ e (A• [ ρ• ]• [ ⟨ u• ⟩• ]•) ≡ A•) →
             transp⟨ (λ {(C , C• , t) → Tm• Γ• C• t}) ⟩ (e ,= trans (transp× e) (e• ,×= (I.q⟨⟩ e))) 
             (q• ⟦ ⟨ u• ⟩• ⟧•) ≡ u•
    q+•    : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• Γ• A}{σ}{σ• : Sub• Δ• Γ• σ}{e : A I.[ I.ρ ] I.[ σ I.⁺ ] ≡ A I.[ σ ] I.[ I.ρ ]} →
             (e• : transp⟨ Ty• (Δ• ▷• A• [ σ• ]•) ⟩ e (A• [ ρ• ]• [ σ• ⁺• ]•) ≡ A• [ σ• ]• [ ρ• ]•) →
             transp⟨ (λ {(C , C• , t) → Tm• (Δ• ▷• A• [ σ• ]•) C• t}) ⟩ (e ,= trans (transp× e) (e• ,×= (I.q+ e)))
             (q• ⟦ σ• ⁺• ⟧•) ≡ q•
    ρ⟨⟩•    : ∀{Γ}{Γ• : Con• Γ}{A B}{A• : Ty• Γ• A}{B• : Ty• Γ• B}{t}{t• : Tm• Γ• A• t}{u}{u• : Tm• Γ• B• u}{e : A I.[ I.ρ ] I.[ I.⟨ u ⟩ ] ≡ A} →
             (e• : transp⟨ Ty• Γ• ⟩ e (A• [ ρ• ]• [ ⟨ u• ⟩• ]•) ≡ A•) →
             transp⟨ (λ {(C , C• , t) → Tm• Γ• C• t}) ⟩ (e ,= trans (transp× e) (e• ,×= (I.ρ⟨⟩ e)))
             (t• ⟦ ρ• ⟧• ⟦ ⟨ u• ⟩• ⟧•) ≡ t•
    ρ+•    : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A B}{A• : Ty• Γ• A}{B• : Ty• Γ• B}{σ}{σ• : Sub• Δ• Γ• σ}{t}{t• : Tm• Γ• A• t}
             {e : A I.[ I.ρ ] I.[ σ I.⁺ ] ≡ A I.[ σ ] I.[ I.ρ ]} →
             (e• : transp⟨ Ty• (Δ• ▷• B• [ σ• ]•) ⟩ e (A• [ ρ• ]• [ σ• ⁺• ]•) ≡ A• [ σ• ]• [ ρ• ]•) →
             transp⟨ (λ {(C , C• , t) → Tm• (Δ• ▷• B• [ σ• ]•) C• t}) ⟩ (e ,= trans (transp× e) (e• ,×= (I.ρ+ e))) 
             (t• ⟦ ρ• ⟧• ⟦ σ• ⁺• ⟧•) ≡ t• ⟦ σ• ⟧• ⟦ ρ• ⟧•

  postulate
    ⟦_⟧•C   : (Γ : I.Con) → Con• Γ
    ⟦_⟧•T   : {Γ : I.Con} → (A : I.Ty Γ) → Ty• ⟦ Γ ⟧•C A 
    ⟦_⟧•S   : {Γ Δ : I.Con} → (σ : I.Sub Δ Γ) → Sub• ⟦ Δ ⟧•C ⟦ Γ ⟧•C σ
    ⟦_⟧•t   : {Γ : I.Con}{A : I.Ty Γ} → (t : I.Tm Γ A) → Tm• ⟦ Γ ⟧•C ⟦ A ⟧•T t
    
    ⟦○⟧•C   : ⟦ I.○ ⟧•C ≡ ○•
    ⟦▷⟧•C   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ Γ I.▷ A ⟧•C ≡ ⟦ Γ ⟧•C ▷• ⟦ A ⟧•T
    {-# REWRITE ⟦○⟧•C ⟦▷⟧•C #-}

    ⟦U⟧•T   : {Γ : I.Con} → ⟦ I.U {Γ} ⟧•T ≡ U•
    {-# REWRITE ⟦U⟧•T #-}
    ⟦El⟧•T  : {Γ : I.Con} → ⟦ I.El {Γ} ⟧•T ≡ El•
    ⟦[]⟧•T  : {Δ Γ : I.Con}{A : I.Ty Γ}{σ : I.Sub Δ Γ} → ⟦ A I.[ σ ] ⟧•T ≡ ⟦ A ⟧•T [ ⟦ σ ⟧•S ]•
    ⟦Π⟧•T   : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)} → ⟦ I.Π A B ⟧•T ≡ Π• ⟦ A ⟧•T ⟦ B ⟧•T
    {-# REWRITE ⟦El⟧•T ⟦[]⟧•T ⟦Π⟧•T #-}

    ⟦ρ⟧•S   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ I.ρ {Γ}{A} ⟧•S ≡ ρ•
    ⟦⟨⟩⟧•S   : {Γ : I.Con}{A : I.Ty Γ}{u : I.Tm Γ A} → ⟦ I.⟨ u ⟩ ⟧•S ≡ ⟨ ⟦ u ⟧•t ⟩•
    ⟦+⟧•S   : {Γ Δ : I.Con}{A : I.Ty Γ}{σ : I.Sub Δ Γ} → ⟦ I._⁺ {_}{_}{A} σ ⟧•S ≡ ⟦ σ ⟧•S ⁺•
    {-# REWRITE ⟦ρ⟧•S ⟦⟨⟩⟧•S ⟦+⟧•S #-}

    ⟦⟦⟧⟧•t  : {Γ Δ : I.Con}{A : I.Ty Γ}{t : I.Tm Γ A}{σ : I.Sub Δ Γ} → ⟦ t I.⟦ σ ⟧ ⟧•t ≡ ⟦ t ⟧•t ⟦ ⟦ σ ⟧•S ⟧•
    ⟦q⟧•t   : {Γ : I.Con}{A : I.Ty Γ} → ⟦ I.q {Γ}{A} ⟧•t ≡ q•
    ⟦lam⟧•t : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)}{t : I.Tm (Γ I.▷ A) B} → ⟦ I.lam t ⟧•t ≡ lam• ⟦ t ⟧•t
    ⟦app⟧•t : {Γ : I.Con}{A : I.Ty Γ}{B : I.Ty (Γ I.▷ A)}{t : I.Tm Γ (I.Π A B)} → ⟦ I.app t ⟧•t ≡ app• ⟦ t ⟧•t
    {-# REWRITE ⟦⟦⟧⟧•t ⟦q⟧•t ⟦lam⟧•t ⟦app⟧•t #-}

-- Then we can derive the model from this, without postulating anything more

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
    El    : {Γ : Con} → Ty (Γ ▷ U)
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
    U[]   : {Γ Δ : Con}{σ : Sub Δ Γ} → U [ σ ] ≡ U
    lam[] : {Γ Δ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → transp⟨ Tm Δ ⟩ Π[] ((lam t) ⟦ σ ⟧) ≡ lam (t ⟦ σ ⁺ ⟧)
    El[]  : {Γ Δ : Con}{a : Tm Γ U}{σ : Sub Δ Γ} → transp⟨ (λ A → Ty (Δ ▷ A)) ⟩ U[] (El [ σ ⁺ ]) ≡ El
    q⟨⟩    : {Γ : Con}{A : Ty Γ}{u : Tm Γ A} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (q ⟦ ⟨ u ⟩ ⟧) ≡ u
    q+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (q ⟦ σ ⁺ ⟧) ≡ q
    ρ⟨⟩    : {Γ : Con}{A B : Ty Γ}{t : Tm Γ A}{u : Tm Γ B} → (e : A [ ρ ] [ ⟨ u ⟩ ] ≡ A) →
            transp⟨ Tm Γ ⟩ e (t ⟦ ρ ⟧ ⟦ ⟨ u ⟩ ⟧) ≡ t
    ρ+    : {Γ Δ : Con}{A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Γ A} → (e : A [ ρ ] [ σ ⁺ ] ≡ A [ σ ] [ ρ ]) →
            transp⟨ Tm (Δ ▷ (A [ σ ])) ⟩ e (t ⟦ ρ ⟧ ⟦ σ ⁺ ⟧) ≡ t ⟦ σ ⟧ ⟦ ρ ⟧

  DM : DepModel {lc} {ls} {lty} {ltm}
  DM = record
    { Con•   = λ _ → Con
    ; Ty•    = λ Γ _ → Ty Γ
    ; Sub•   = λ Γ Δ _ → Sub Γ Δ
    ; Tm•    = λ Γ A _ → Tm Γ A
    ; ○•     = ○
    ; _▷•_   = λ Γ A → Γ ▷ A
    ; U•     = U
    ; El•    = El
    ; _[_]•  = λ A σ → A [ σ ]
    ; Π•     = λ A B → Π A B
    ; ρ•     = ρ
    ; ⟨_⟩•    = ⟨_⟩
    ; _⁺•     = _⁺
    ; _⟦_⟧•  = λ t σ → t ⟦ σ ⟧
    ; q•     = q
    ; lam•   = lam
    ; app•   = app
    ; Π[]•   = λ {_}{_}{_}{_}{_}{A•}{_}{B•}{_}{σ•} → trans ((transpconst {_}{_}{_}{_}{_}{_}{I.Π[]})) Π[]
    ; β•     = λ {Γ}{_}{A}{_}{B}{_}{t}{t•} → trans ((transpconst {_}{_}{_}{_}{_}{t}{I.β {Γ}{A}{B}})) β
    ; η•     = λ {Γ}{_}{A}{_}{B}{_}{t}{t•} → trans ((transpconst {_}{_}{_}{_}{_}{t}{I.η {Γ}{A}{B}})) η
    ; U[]•   = λ {_}{_}{_}{_}{_}{σ•} → trans (transpconst {_}{_}{_}{_}{_}{_}{I.U[]}) U[]
    -- TODO !
    ; lam[]• = {!!}
    ; El[]•  = {!!}
    ; q⟨⟩•    = {!!}
    ; q+•    = {!!}
    ; ρ⟨⟩•    = {!!}
    ; ρ+•    = {!!}
    }
  module DM = DepModel DM

  ⟦_⟧C : I.Con → Con
  ⟦_⟧C = DM.⟦_⟧•C
  ⟦_⟧T : {Γ : I.Con} → I.Ty Γ → Ty ⟦ Γ ⟧C
  ⟦_⟧T = DM.⟦_⟧•T
  ⟦_⟧S : {Γ Δ : I.Con} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
  ⟦_⟧S = DM.⟦_⟧•S
  ⟦_⟧t : {Γ : I.Con}{A : I.Ty Γ} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦_⟧t = DM.⟦_⟧•t

\end{code}
