
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
  infixr 6 _∘_
  infixr 5 _‣_

  -- we have 4 sorts, we have to postulate Sub and Tm for the equations
  
  data Ty : Set where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

  data Con : Set where
    ○   : Con
    _▷_ : Con → Ty → Con

  postulate Sub : Con → Con → Set
  postulate Tm  : Con → Ty → Set

  postulate
    
    -- Substitutions
    _∘_   : {Γ Δ Θ : Con} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    id    : {Γ : Con} → Sub Γ Γ
    ε     : {Γ : Con} → Sub Γ ○
    _‣_   : {Γ Δ : Con}{A : Ty} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▷ A)
    p     : {Γ : Con}{A : Ty} → Sub (Γ ▷ A) Γ
    
    -- Terms
    _[_]  : {Γ Δ : Con}{A : Ty} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ A
    q     : {Γ : Con}{A : Ty} → Tm (Γ ▷ A) A
    lam   : {Γ : Con}{A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
    _$_   : {Γ : Con}{A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

    -- the equations on terms :
    β     : {Γ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{u : Tm Γ A} → (lam t) $ u ≡ t [ id ‣ u ]
    η     : {Γ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)} → lam ((t [ p ]) $ q) ≡ t
    -- the eqautions on how to compute substitutions 
    [][]  : {Γ Δ Θ : Con}{A : Ty}{t : Tm Γ A}{σ : Sub Δ Γ}{ρ : Sub Θ Δ} → t [ σ ] [ ρ ] ≡ t [ σ ∘ ρ ]
    q[]   : {Γ Δ : Con}{A : Ty}{t : Tm Δ A}{σ : Sub Δ Γ} → q [ σ ‣ t ] ≡ t
    lam[] : {Γ Δ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → (lam t) [ σ ] ≡ lam (t [ σ ∘ p ‣ q ])
    $[]   : {Γ Δ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{σ : Sub Δ Γ} → (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
    t[id] : {Γ : Con}{A : Ty}{t : Tm Γ A} → t [ id ] ≡ t
    -- the equations on substitutions
    ass   : {Γ Δ Θ Ω : Con}{σ : Sub Δ Γ}{ρ : Sub Θ Δ}{γ : Sub Ω Θ} → σ ∘ (ρ ∘ γ) ≡ (σ ∘ ρ) ∘ γ
    idl   : {Γ Δ : Con}{σ : Sub Δ Γ} → id ∘ σ ≡ σ
    idr   : {Γ Δ : Con}{σ : Sub Δ Γ} → σ ∘ id ≡ σ
    ○η    : {Γ : Con}{σ : Sub Γ ○} → σ ≡ ε
    ▷β    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ Γ}{t : Tm Δ A} → p ∘ (σ ‣ t) ≡ σ
    ▷η    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ (Γ ▷ A)} → (p ∘ σ ‣ q [ σ ]) ≡ σ

  --Renaming
  data isVar : (Γ : Con) → (A : Ty) → Tm Γ A → Set where
    zero : ∀{Γ}{A} → isVar (Γ ▷ A) A q
    succ : ∀{Γ}{A B}{t : Tm Γ A} → isVar Γ A t → isVar (Γ ▷ B) A (t [ p ])

  data isRen : (Δ Γ : Con) → Sub Δ Γ → Set where
    εRen : ∀{Γ} → isRen Γ ○ ε
    ‣Ren : ∀{Δ Γ}{σ}{A}{t} → isRen Δ Γ σ → isVar Δ A t → isRen Δ (Γ ▷ A) (σ ‣ t) 

--------------------------------------------------

-- We can now define the Dependent Model its recursor :

record DepModel {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]•
  infixr 7 _$•_
  infixr 5 _▷•_
  infixr 6 _∘•_
  infixr 5 _‣•_

  open I

  field
  
    Con•   : Con → Set lc
    Ty•    : Ty → Set lty
    Sub•   : ∀{Δ} → Con• Δ → ∀{Γ} → Con• Γ → Sub Δ Γ → Set ls
    Tm•    : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → Tm Γ A → Set ltm
    
    ○•     : Con• ○
    _▷•_   : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → Con• (Γ ▷ A) 

    _∘•_   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{Θ}{Θ• : Con• Θ}{σ} → Sub• Δ• Γ• σ → ∀{ρ} → Sub• Θ• Δ• ρ → Sub• Θ• Γ• (σ ∘ ρ)
    id•    : ∀{Γ}{Γ• : Con• Γ} → Sub• Γ• Γ• id
    ε•     : ∀{Γ}{Γ• : Con• Γ} → Sub• Γ• ○• ε
    _‣•_   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ} → Sub• Δ• Γ• σ → ∀{t} → Tm• Δ• A• t → Sub• Δ• (Γ• ▷• A•) (σ ‣ t)
    p•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A} → Sub• (Γ• ▷• A•) Γ• p

    ι•     : Ty• I.ι
    _⇒•_   : ∀{A}{B} → Ty• A → Ty• B → Ty• (A I.⇒ B)

    _[_]•  : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{u} → Tm• Γ• A• u → ∀{σ} → (σ• : Sub• Δ• Γ• σ) →
             Tm• Δ• A• (u [ σ ])
    q•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A} →
             Tm• (Γ• ▷• A•) A• q
    lam•   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t} → Tm• (Γ• ▷• A•) B• t →
             Tm• Γ• (A• ⇒• B•) (lam t)
    _$•_   : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t} → Tm• Γ• (A• ⇒• B•) t → ∀{u} → Tm• Γ• A• u →
             Tm• Γ• B• (t $ u)

    β•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{u}{u• : Tm• Γ• A• u} →
             transp⟨ Tm• Γ• B• ⟩ β ((lam• t•) $• u•) ≡ t• [ id• ‣• u• ]•
    η•     : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• (A• ⇒• B•) t} →
             transp⟨ Tm• Γ• (A• ⇒• B•) ⟩ η (lam• ((t• [ p• ]•) $• q•)) ≡ t•
    [][]•  : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{Θ}{Θ• : Con• Θ}{A}{A• : Ty• A}{t}{t• : Tm• Γ• A• t}{σ}{σ• : Sub• Δ• Γ• σ}{ρ}{ρ• : Sub• Θ• Δ• ρ} →
             transp⟨ Tm• Θ• A• ⟩ [][] (t• [ σ• ]• [ ρ• ]•) ≡ t• [ σ• ∘• ρ• ]•
    q[]•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{t}{t• : Tm• Δ• A• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• A• ⟩ q[] (q• [ σ• ‣• t• ]•) ≡ t•
    lam[]• : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• (A• ⇒• B•) ⟩ lam[] ((lam• t•) [ σ• ]•) ≡ lam• (t• [ σ• ∘• p• ‣• q• ]•)
    $[]•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• (A• ⇒• B•) t}
             {u}{u• : Tm• Γ• A• u}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• B• ⟩ $[] ((t• $• u•) [ σ• ]•) ≡ (t• [ σ• ]•) $• (u• [ σ• ]•)
    t[id]• : ∀{Γ}{Γ• : Con• Γ}{A}{A• : Ty• A}{t}{t• : Tm• Γ• A• t} →
             transp⟨ Tm• Γ• A• ⟩ t[id] (t• [ id• ]•) ≡ t•
    ass•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{Θ}{Θ• : Con• Θ}{Ω}{Ω• : Con• Ω}
             {σ}{σ• : Sub• Δ• Γ• σ}{ρ}{ρ• : Sub• Θ• Δ• ρ}{γ}{γ• : Sub• Ω• Θ• γ} →
             transp⟨ Sub• Ω• Γ• ⟩ ass (σ• ∘• (ρ• ∘• γ•)) ≡ (σ• ∘• ρ•) ∘• γ•
    idl•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Sub• Δ• Γ• ⟩ idl (id• ∘• σ•) ≡ σ•
    idr•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Sub• Δ• Γ• ⟩ idr (σ• ∘• id•) ≡ σ•
    ○η•    : ∀{Γ}{Γ• : Con• Γ}{σ}{σ• : Sub• Γ• ○• σ} →
             transp⟨ Sub• Γ• ○• ⟩ ○η σ• ≡ ε•
    ▷β•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ}{σ• : Sub• Δ• Γ• σ}{t}{t• : Tm• Δ• A• t} →
             transp⟨ Sub• Δ• Γ• ⟩ ▷β (p• ∘• (σ• ‣• t•)) ≡ σ•
    ▷η•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ}{σ• : Sub• Δ• (Γ• ▷• A•) σ} →
             transp⟨ Sub• Δ• (Γ• ▷• A•) ⟩ ▷η (p• ∘• σ• ‣• q• [ σ• ]•) ≡ σ•

  -- then we have the induction principle :
 
  ⟦_⟧•C     : (Γ : I.Con) → Con• Γ
  ⟦_⟧•T     : (A : I.Ty) → Ty• A
  postulate
    ⟦_⟧•S   : {Γ Δ : I.Con} → (σ : I.Sub Δ Γ) → Sub• ⟦ Δ ⟧•C ⟦ Γ ⟧•C σ
    ⟦_⟧•t   : {Γ : I.Con}{A : I.Ty} → (t : I.Tm Γ A) → Tm• ⟦ Γ ⟧•C ⟦ A ⟧•T t
  
  ⟦ I.○ ⟧•C = ○•
  ⟦ Γ I.▷ A ⟧•C = ⟦ Γ ⟧•C ▷• ⟦ A ⟧•T

  ⟦ I.ι ⟧•T = ι•
  ⟦ A I.⇒ B ⟧•T = ⟦ A ⟧•T ⇒• ⟦ B ⟧•T

  postulate

    ⟦∘⟧•S   : {Γ Δ Θ : I.Con}{σ : I.Sub Δ Γ}{ρ : I.Sub Θ Δ} → ⟦ σ ∘ ρ ⟧•S ≡ ⟦ σ ⟧•S ∘• ⟦ ρ ⟧•S
    ⟦id⟧•S  : {Γ : I.Con} → ⟦ id {Γ} ⟧•S ≡ id•
    ⟦ε⟧•S   : {Γ : I.Con} → ⟦ ε {Γ} ⟧•S ≡ ε•
    ⟦‣⟧•S   : {Γ Δ : I.Con}{σ : I.Sub Δ Γ}{A : I.Ty}{t : I.Tm Δ A} → ⟦ σ ‣ t ⟧•S ≡ ⟦ σ ⟧•S ‣• ⟦ t ⟧•t
    ⟦p⟧•S   : {Γ : I.Con}{A : I.Ty} → ⟦ p {Γ}{A} ⟧•S ≡ p•
    {-# REWRITE ⟦∘⟧•S ⟦id⟧•S ⟦ε⟧•S ⟦‣⟧•S ⟦p⟧•S #-}
    
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
  infixr 6 _∘_
  infixr 5 _‣_

  field
  
    Con   : Set lc
    Ty    : Set lty
    Sub   : Con → Con → Set ls
    Tm    : Con → Ty → Set ltm
    
    ○     : Con
    _▷_   : Con → Ty → Con
    
    ι     : Ty
    _⇒_   : Ty → Ty → Ty
    
    _∘_   : {Γ Δ Θ : Con} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    id    : {Γ : Con} → Sub Γ Γ
    ε     : {Γ : Con} → Sub Γ ○
    _‣_   : {Γ Δ : Con}{A : Ty} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▷ A)
    p     : {Γ : Con}{A : Ty} → Sub (Γ ▷ A) Γ
    
    _[_]  : {Γ Δ : Con}{A : Ty} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ A
    q     : {Γ : Con}{A : Ty} → Tm (Γ ▷ A) A
    lam   : {Γ : Con}{A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
    _$_   : {Γ : Con}{A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

    β     : {Γ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{u : Tm Γ A} → (lam t) $ u ≡ t [ id ‣ u ]
    η     : {Γ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)} → lam ((t [ p ]) $ q) ≡ t
    [][]  : {Γ Δ Θ : Con}{A : Ty}{t : Tm Γ A}{σ : Sub Δ Γ}{ρ : Sub Θ Δ} → t [ σ ] [ ρ ] ≡ t [ σ ∘ ρ ]
    q[]   : {Γ Δ : Con}{A : Ty}{t : Tm Δ A}{σ : Sub Δ Γ} → q [ σ ‣ t ] ≡ t
    lam[] : {Γ Δ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B}{σ : Sub Δ Γ} → (lam t) [ σ ] ≡ lam (t [ σ ∘ p ‣ q ])
    $[]   : {Γ Δ : Con}{A B : Ty}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{σ : Sub Δ Γ} → (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
    t[id] : {Γ : Con}{A : Ty}{t : Tm Γ A} → t [ id ] ≡ t
    ass   : {Γ Δ Θ Ω : Con}{σ : Sub Δ Γ}{ρ : Sub Θ Δ}{γ : Sub Ω Θ} → σ ∘ (ρ ∘ γ) ≡ (σ ∘ ρ) ∘ γ
    idl   : {Γ Δ : Con}{σ : Sub Δ Γ} → id ∘ σ ≡ σ
    idr   : {Γ Δ : Con}{σ : Sub Δ Γ} → σ ∘ id ≡ σ
    ○η    : {Γ : Con}{σ : Sub Γ ○} → σ ≡ ε
    ▷β    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ Γ}{t : Tm Δ A} → p ∘ (σ ‣ t) ≡ σ
    ▷η    : {Γ Δ : Con}{A : Ty}{σ : Sub Δ (Γ ▷ A)} → (p ∘ σ ‣ q [ σ ]) ≡ σ

  DM : DepModel {lc} {ls} {lty} {ltm}
  DM = record
     { Con•   = λ _ → Con
     ; Ty•    = λ _ → Ty
     ; Sub•   = λ Δ Γ _ → Sub Δ Γ
     ; Tm•    = λ Γ A _ → Tm Γ A
     ; ○•     = ○
     ; _▷•_   = λ Γ A → Γ ▷ A
     ; _∘•_   = λ σ ρ → σ ∘ ρ
     ; id•    = id
     ; ε•     = ε
     ; _‣•_   = λ σ t → σ ‣ t
     ; p•     = p
     ; ι•     = ι
     ; _⇒•_   = _⇒_
     ; _[_]•  = λ t σ → t [ σ ]
     ; q•     = q
     ; lam•   = lam
     ; _$•_   = λ u v → u $ v
     ; β•     = β
     ; η•     = η
     ; [][]•  = [][]
     ; q[]•   = q[]
     ; lam[]• = lam[]
     ; $[]•   = $[]
     ; t[id]• = t[id]
     ; ass•   = ass 
     ; idl•   = idl
     ; idr•   = idr
     ; ○η•    = ○η
     ; ▷β•    = ▷β
     ; ▷η•    = ▷η
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


--Some properties on Renaming :

open I

subDist : ∀{Γ Δ Θ : Con}{A : Ty}{σ : Sub Δ Γ}{t : Tm Δ A}{ω : Sub Θ Δ} →
          (σ ‣ t) ∘ ω ≡ (σ ∘ ω) ‣ (t [ ω ])
subDist {Γ}{Δ}{Θ}{A}{σ}{t}{ω} = (sym ▷η) ■
                                (cong⟨ _‣ q [ (σ ‣ t) ∘ ω ] ⟩ ass) ■
                                (cong⟨ (λ x → (x ∘ ω) ‣ q [ (σ ‣ t) ∘ ω ]) ⟩ ▷β) ■
                                (cong⟨ (σ ∘ ω) ‣_ ⟩ (sym [][])) ■
                                (cong⟨ (λ x → (σ ∘ ω) ‣ x [ ω ]) ⟩ q[])

wkRen : ∀{Γ}{Δ}{σ}{A} →
        isRen Δ Γ σ → (isRen (Δ ▷ A) Γ (σ ∘ p))
wkRen {○}{Δ}{σ}{A} σR = transp⟨ isRen (Δ ▷ A) ○ ⟩ (sym ○η) εRen
wkRen {Γ ▷ B}{Δ}{σ}{A} (‣Ren σ* t*) = transp⟨ isRen (Δ ▷ A) (Γ ▷ B) ⟩ (sym subDist) (‣Ren (wkRen σ*) (succ t*))

pRen : ∀{Γ}{A} →
       isRen (Γ I.▷ A) Γ I.p
pRen {○}{A} = transp⟨ isRen (○ ▷ A) ○ ⟩ (sym ○η) εRen
pRen {Γ ▷ B}{A} = transp⟨ isRen ((Γ ▷ B) ▷ A) (Γ ▷ B) ⟩ ▷η (‣Ren (wkRen (pRen {Γ})) (succ zero))


\end{code}
