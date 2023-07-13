
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
  infixr 7 _$_
  infixr 5 _▷_

  postulate
  
    -- There is 4 sorts :
    Con   : Set
    Ty    : Set
    Sub   : Con → Con → Set
    Tm    : Con → Ty → Set
    
    -- Contexts
    ○     : Con
    _▷_   : Con → Ty → Con
    
    -- Types
    ι     : Ty
    _⇒_   : Ty → Ty → Ty
    
    -- Substitutions
    ρ     : {Γ : Con}{A : Ty} → Sub (Γ ▷ A) Γ
    ⟨_⟩    : {Γ : Con}{A : Ty} → Tm Γ A → Sub Γ (Γ ▷ A)
    _⁺    : {Γ Δ : Con}{A : Ty} → (σ : Sub Δ Γ) → Sub (Δ ▷ A) (Γ ▷ A)
    
    -- Terms
    _[_]  : {Γ Δ : Con}{A : Ty} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ A
    q     : {Γ : Con}{A : Ty} → Tm (Γ ▷ A) A
    lam   : {Γ : Con}{A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
    _$_   : {Γ : Con}{A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

    -- then the equations
    β     : {Γ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{u : Tm Γ A} → (lam t) $ u ≡ t [ ⟨ u ⟩ ]
    η     : {Γ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)} → lam ((t [ ρ ]) $ q) ≡ t
    lam[] : {Γ Δ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → (lam t) [ σ ] ≡ lam (t [ σ ⁺ ])
    $[]   : {Γ Δ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{σ : Sub Δ Γ} → (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
    q⟨⟩    : {Γ : Con}{A : Ty}{u : Tm Γ A} → q [ ⟨ u ⟩ ] ≡ u
    q+    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ Γ} → q [ σ ⁺ ] ≡ q {_}{A}
    ρ⟨⟩    : {Γ : Con}{A B : Ty}{t : Tm Γ A}{u : Tm Γ B} → (t [ ρ ] [ ⟨ u ⟩ ]) ≡ t
    ρ+    : {Γ Δ : Con}{A B : Ty}{σ : Sub Δ Γ}{t : Tm Γ A} → (t [ ρ {_}{B} ] [ σ ⁺ ]) ≡ t [ σ ] [ ρ ]
    
--------------------------------------------------

-- We can now define the Dependent Model its recursor :

record DepModel {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]•
  infixr 7 _$•_
  infixr 5 _▷•_

  field
  
    Con•   : I.Con → Set lc
    Ty•    : I.Ty → Set lty
    Sub•   : ∀{Γ Δ} → Con• Δ → Con• Γ → I.Sub Δ Γ → Set ls
    Tm•    : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → I.Tm Γ A → Set ltm
    
    ○•     : Con• I.○
    _▷•_   : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → Con• (Γ I.▷ A) 
  
    ρ•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A} → Sub• (Γ• ▷• A•) Γ• I.ρ
    ⟨_⟩•    : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A} → ∀{u} → Tm• Γ• A• u → Sub• Γ• (Γ• ▷• A•) I.⟨ u ⟩
    _⁺•    : ∀{Γ Δ}{Γ• : Con• Γ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ} → (σ• : Sub• Δ• Γ• σ) → Sub• (Δ• ▷• A•)  (Γ• ▷• A•) (σ I.⁺)

    ι•     : Ty• I.ι
    _⇒•_   : ∀{A}{B} → Ty• A → Ty• B → Ty• (A I.⇒ B)

    _[_]•  : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{u} → Tm• Γ• A• u → ∀{σ} → (σ• : Sub• Δ• Γ• σ) →
             Tm• Δ• A• (u I.[ σ ])
    q•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A} →
             Tm• (Γ• ▷• A•) A• I.q
    lam•   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t} → Tm• (Γ• ▷• A•) B• t →
             Tm• Γ• (A• ⇒• B•) (I.lam t)
    _$•_   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t} → Tm• Γ• (A• ⇒• B•) t → ∀{u} → Tm• Γ• A• u →
             Tm• Γ• B• (t I.$ u)

    β•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{u}{u• : Tm• Γ• A• u} →
             transp⟨ Tm• Γ• B• ⟩ I.β ((lam• t•) $• u•) ≡ t• [ ⟨ u• ⟩• ]•
    η•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• (A• ⇒• B•) t} →
             transp⟨ Tm• Γ• (A• ⇒• B•) ⟩ I.η (lam• ((t• [ ρ• ]•) $• q•)) ≡ t•
    lam[]• : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• (A• ⇒• B•) ⟩ I.lam[] ((lam• t•) [ σ• ]•) ≡ lam• (t• [ σ• ⁺• ]•)
    $[]•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• (A• ⇒• B•) t}
              {u}{u• : Tm• Γ• A• u}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• B• ⟩ I.$[] ((t• $• u•) [ σ• ]•) ≡ (t• [ σ• ]•) $• (u• [ σ• ]•)
    q⟨⟩•    : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{u}{u• : Tm• Γ• A• u} →
             transp⟨ Tm• Γ• A• ⟩ I.q⟨⟩ (q• [ ⟨ u• ⟩• ]•) ≡ u•
    q+•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• (Δ• ▷• A•) A• ⟩ I.q+ (q• [ σ• ⁺• ]•) ≡ q•
    ρ⟨⟩•    : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• A• t}{u}{u• : Tm• Γ• B• u} →
             transp⟨ Tm• Γ• A• ⟩ I.ρ⟨⟩ (t• [ ρ• ]• [ ⟨ u• ⟩• ]•) ≡ t•
    ρ+•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{σ}{σ• : Sub• Δ• Γ• σ}{t}{t• : Tm• Γ• A• t} →
             transp⟨ Tm• (Δ• ▷• B•) A• ⟩ I.ρ+ (t• [ ρ• ]• [ σ• ⁺• ]•) ≡ t• [ σ• ]• [ ρ• ]•
    
  postulate
    ⟦_⟧•C   : (Γ : I.Con) → Con• Γ
    ⟦_⟧•T   : (A : I.Ty) → Ty• A 
    ⟦_⟧•S   : {Γ Δ : I.Con} → (σ : I.Sub Δ Γ) → Sub• ⟦ Δ ⟧•C ⟦ Γ ⟧•C σ
    ⟦_⟧•t   : {Γ : I.Con}{A : I.Ty} → (t : I.Tm Γ A) → Tm• ⟦ Γ ⟧•C ⟦ A ⟧•T t
    
    ⟦○⟧•C   : ⟦ I.○ ⟧•C ≡ ○•
    ⟦▷⟧•C   : {Γ : I.Con}{A : I.Ty} → ⟦ Γ I.▷ A ⟧•C ≡ ⟦ Γ ⟧•C ▷• ⟦ A ⟧•T
    {-# REWRITE ⟦○⟧•C ⟦▷⟧•C #-}

    ⟦ι⟧•T   : ⟦ I.ι ⟧•T ≡ ι•
    ⟦⇒⟧•T   : {A B : I.Ty} → ⟦ A I.⇒ B ⟧•T ≡ ⟦ A ⟧•T ⇒• ⟦ B ⟧•T
    {-# REWRITE ⟦ι⟧•T ⟦⇒⟧•T #-}

    ⟦ρ⟧•S   : {Γ : I.Con}{A : I.Ty} → ⟦ I.ρ {Γ}{A} ⟧•S ≡ ρ•
    ⟦⟨⟩⟧•S   : {Γ : I.Con}{A : I.Ty}{u : I.Tm Γ A} → ⟦ I.⟨ u ⟩ ⟧•S ≡ ⟨ ⟦ u ⟧•t ⟩•
    ⟦+⟧•S   : {Γ Δ : I.Con}{A : I.Ty}{σ : I.Sub Δ Γ} → ⟦ I._⁺ {_}{_}{A} σ ⟧•S ≡ ⟦ σ ⟧•S ⁺•
    {-# REWRITE ⟦ρ⟧•S ⟦⟨⟩⟧•S ⟦+⟧•S #-}

    ⟦[]⟧•t  : {Γ Δ : I.Con}{A : I.Ty}{t : I.Tm Γ A}{σ : I.Sub Δ Γ} → ⟦ t I.[ σ ] ⟧•t ≡ ⟦ t ⟧•t [ ⟦ σ ⟧•S ]•
    ⟦q⟧•t   : {Γ : I.Con}{A : I.Ty} → ⟦ I.q {Γ}{A} ⟧•t ≡ q•
    ⟦lam⟧•t : {Γ : I.Con}{A B : I.Ty}{t : I.Tm (Γ I.▷ A) B} → ⟦ I.lam t ⟧•t ≡ lam• ⟦ t ⟧•t
    ⟦$⟧•t : {Γ : I.Con}{A B : I.Ty}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A} → ⟦ t I.$ u ⟧•t ≡ ⟦ t ⟧•t $• ⟦ u ⟧•t
    {-# REWRITE ⟦[]⟧•t ⟦q⟧•t ⟦lam⟧•t ⟦$⟧•t #-}

-- Then we can derive the model from this, without postulating anything more

record Model {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]
  infixr 7 _$_
  infixr 5 _▷_

  field
  
    Con   : Set lc
    Ty    : Set lty
    Sub   : Con → Con → Set ls
    Tm    : Con → Ty → Set ltm
    
    ○     : Con
    _▷_   : Con → Ty → Con
    
    ι     : Ty
    _⇒_   : Ty → Ty → Ty
    
    ρ     : {Γ : Con}{A : Ty} → Sub (Γ ▷ A) Γ
    ⟨_⟩    : {Γ : Con}{A : Ty} → Tm Γ A → Sub Γ (Γ ▷ A)
    _⁺    : {Γ Δ : Con}{A : Ty} → (σ : Sub Δ Γ) → Sub (Δ ▷ A) (Γ ▷ A)
    
    _[_]  : {Γ Δ : Con}{A : Ty} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ A
    q     : {Γ : Con}{A : Ty} → Tm (Γ ▷ A) A
    lam   : {Γ : Con}{A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
    _$_   : {Γ : Con}{A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

    β     : {Γ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{u : Tm Γ A} → (lam t) $ u ≡ t [ ⟨ u ⟩ ]
    η     : {Γ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)} → lam ((t [ ρ ]) $ q) ≡ t
    lam[] : {Γ Δ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → (lam t) [ σ ] ≡ lam (t [ σ ⁺ ])
    $[]   : {Γ Δ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{σ : Sub Δ Γ} → (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
    q⟨⟩    : {Γ : Con}{A : Ty}{u : Tm Γ A} → q [ ⟨ u ⟩ ] ≡ u
    q+    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ Γ} → q [ σ ⁺ ] ≡ q {_}{A}
    ρ⟨⟩    : {Γ : Con}{A B : Ty}{t : Tm Γ A}{u : Tm Γ B} → (t [ ρ ] [ ⟨ u ⟩ ]) ≡ t
    ρ+    : {Γ Δ : Con}{A B : Ty}{σ : Sub Δ Γ}{t : Tm Γ A} → (t [ ρ {_}{B} ] [ σ ⁺ ]) ≡ t [ σ ] [ ρ ]

  DM : DepModel {lc} {ls} {lty} {ltm}
  DM = record
     { Con•   = λ _ → Con
     ; Ty•    = λ _ → Ty
     ; Sub•   = λ Γ Δ _ → Sub Γ Δ
     ; Tm•    = λ Γ A _ → Tm Γ A
     ; ○•     = ○
     ; _▷•_   = λ Γ A → Γ ▷ A
     ; ρ•     = ρ
     ; ⟨_⟩•    = ⟨_⟩
     ; _⁺•    = _⁺
     ; ι•     = ι
     ; _⇒•_   = _⇒_
     ; _[_]•  = λ t σ → t [ σ ]
     ; q•     = q
     ; lam•   = lam
     ; _$•_   = λ t u → t $ u
     ; β•     = β
     ; η•     = η
     ; lam[]• = lam[]
     ; $[]•   = $[]
     ; q⟨⟩•    = q⟨⟩
     ; q+•    = q+
     ; ρ⟨⟩•    = ρ⟨⟩
     ; ρ+•    = ρ+
     }
  module DM = DepModel DM

  ⟦_⟧C : I.Con → Con
  ⟦_⟧C = DM.⟦_⟧•C
  ⟦_⟧T : I.Ty → Ty
  ⟦_⟧T = DM.⟦_⟧•T
  ⟦_⟧S : {Γ Δ : I.Con} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
  ⟦_⟧S = DM.⟦_⟧•S
  ⟦_⟧t : {Γ : I.Con}{A : I.Ty} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦_⟧t = DM.⟦_⟧•t

\end{code}
