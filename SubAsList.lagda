\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat
open import TTSyntax

module SubAsList where

module NormalSub where

  open I

  -- let us interpret substitutions as lists of Terms :

  Sub* : Con → Con → Set
  Sub* Δ I.○ = 𝟙
  Sub* Δ (Γ I.▷ A) = Sub* Δ Γ × I.Tm Δ A

  -- then we can define the unquote function from Sub* to Sub

  ⌜_⌝ : ∀{Γ Δ} → Sub* Δ Γ → Sub Δ Γ
  ⌜_⌝ {○} ★ = ε
  ⌜_⌝ {Γ ▷ A} (σ , t) = ⌜ σ ⌝ ‣ t

  -- as well we have all the operators,
  -- where ε is ★ and _‣_ the Σ type constructor _,_

  _∘*_ : ∀{Γ Δ Θ} → Sub* Δ Γ → Sub* Θ Δ → Sub* Θ Γ
  id* : ∀{Γ} → Sub* Γ Γ
  wk : ∀{Γ Δ}{B} → Sub* Δ Γ → Sub* (Δ ▷ B) Γ
  p* : ∀{Γ}{A} → Sub* (Γ ▷ A) Γ
  
  p* = wk id*
  
  _∘*_ {I.○} ★ ρ = ★
  _∘*_ {Γ I.▷ A} (σ , t) ρ = (σ ∘* ρ) , t [ ⌜ ρ ⌝  ]

  wk {○} ★ = ★
  wk {Γ ▷ A} (σ , t) = wk σ , (t [ p ])

  id* {○} = ★
  id* {Γ ▷ A} = wk id* , q

  -- Then We need to show that the unquote function is morphism : 

  ⌜∘⌝ : ∀{Γ Δ Θ}{σ* : Sub* Δ Γ}{ρ* : Sub* Θ Δ} → ⌜ σ* ∘* ρ* ⌝ ≡ ⌜ σ* ⌝ ∘ ⌜ ρ* ⌝ 
  ⌜∘⌝ {○}{Δ}{Θ}{★}{ρ*} = (sym ○η)
  ⌜∘⌝ {Γ ▷ A}{Δ}{Θ}{σ , t}{ρ*} = (cong⟨ _‣ t [ ⌜ ρ* ⌝ ] ⟩ ⌜∘⌝) ■ (sym subDist)

  ⌜wk⌝ : ∀{Γ Δ}{B}{σ* : Sub* Δ Γ} → ⌜ wk {Γ}{Δ}{B} σ* ⌝ ≡ ⌜ σ* ⌝ ∘ p
  ⌜wk⌝ {○}{Δ}{B}{★} = sym ○η
  ⌜wk⌝ {Γ ▷ A}{Δ}{B}{σ , t} = (cong⟨ _‣ t [ p ] ⟩ ⌜wk⌝) ■ (sym subDist)

  ⌜id⌝ : ∀{Γ} → ⌜ id* ⌝ ≡ id {Γ}
  ⌜id⌝ {○} = (sym ○η)
  ⌜id⌝ {Γ ▷ A} = (cong⟨ _‣ q ⟩ ⌜wk⌝) ■
                 (cong⟨ (λ x → x ∘ p ‣ q) ⟩ ⌜id⌝) ■
                 (cong⟨ _‣ q ⟩ (idl ■ (sym idr))) ■
                 (cong⟨ p ∘ id ‣_ ⟩ (sym t[id])) ■
                 (▷η)

  ⌜p⌝ : ∀{Γ}{B} → ⌜ p* ⌝ ≡ p {Γ}{B} 
  ⌜p⌝ {○}{B} = sym ○η
  ⌜p⌝ {Γ ▷ A}{B} = (cong⟨ _‣ q [ p ] ⟩ ⌜wk⌝) ■ (cong⟨ (λ x → x ∘ p ‣ q [ p ]) ⟩ ⌜p⌝) ■ ▷η

  ⌜ε⌝ : ∀{Γ} → ⌜ ★ ⌝ ≡ ε {Γ}
  ⌜ε⌝ = refl

  ⌜‣⌝ : ∀{Γ Δ}{A}{σ : Sub* Δ Γ}{t : Tm Δ A} → ⌜ σ , t ⌝ ≡ ⌜ σ ⌝ ‣ t
  ⌜‣⌝ = refl

  -- and finally prove the equations on substitutions

  ass* : ∀{Γ Δ Θ Ω}{σ : Sub* Δ Γ}{ρ : Sub* Θ Δ}{γ : Sub* Ω Θ} → (σ ∘* (ρ ∘* γ)) ≡ ((σ ∘* ρ) ∘* γ)
  ass* {○}{Δ}{Θ}{Ω}{σ*}{ρ*}{γ*} = refl
  ass* {Γ ▷ A}{Δ}{Θ}{Ω}{σ* , t}{ρ*}{γ*} = ass* ,= ((cong⟨ t [_] ⟩ ⌜∘⌝) ■ (sym [][]))

  ▷β** : ∀{Θ Γ Δ}{A}{ρ : Sub* Γ Θ}{σ : Sub* Δ Γ}{u : Tm Δ A} → (wk ρ ∘* (σ , u)) ≡ ρ ∘* σ
  ▷β** {○}{Γ}{Δ}{A}{★}{σ}{u} = refl
  ▷β** {Θ ▷ B}{Γ}{Δ}{A}{ρ , t}{σ}{u} = ▷β** ,= ([][] ■ (cong⟨ t [_] ⟩ ▷β))

  idl* : ∀{Γ Δ}{σ : Sub* Δ Γ} → (id* ∘* σ) ≡ σ
  
  ▷β* : ∀{Γ Δ}{A}{σ : Sub* Δ Γ}{u : Tm Δ A} → (wk id* ∘* (σ , u)) ≡ σ
  ▷β* {Γ}{Δ}{A}{σ}{u} = ▷β** ■ idl*
  
  idl* {○}{Δ}{σ} = refl
  idl* {Γ ▷ A}{Δ}{σ , t} = ▷β* ,= q[]

  ▷η* : ∀{Γ Δ}{A}{σ : Sub* Δ (Γ ▷ A)} → ((p* ∘* σ) , q [ ⌜ σ ⌝ ]) ≡ σ
  ▷η* {Γ}{Δ}{A}{σ , t} = ▷β* ,= q[]

  idr* : ∀{Γ Δ}{σ : Sub* Δ Γ} → (σ ∘* id*) ≡ σ
  idr* {○}{Δ}{σ} = refl
  idr* {Γ ▷ A}{Δ}{σ , t} = idr* ,= ((cong⟨ t [_] ⟩ ⌜id⌝) ■ t[id])


S* : Model
S* = record
   { Con   = Con
   ; Ty    = Ty
   ; Sub   = Sub* 
   ; Tm    = Tm
   ; ○     = ○
   ; _▷_   = _▷_
   ; ι     = ι
   ; _⇒_   = _⇒_
   ; _∘_   = _∘*_
   ; id    = id*
   ; ε     = ★
   ; _‣_   = _,_
   ; p     = p*
   ; _[_]  = λ t σ → t [ ⌜ σ ⌝ ]
   ; q     = q
   ; lam   = lam
   ; _$_   = _$_
   ; β     = λ {Γ}{A}{B}{t}{u} →
             β ■ cong⟨ (λ x → t [ x ‣ u ]) ⟩ (sym ⌜id⌝)
   ; η     = λ {Γ}{A}{B}{t} →
             cong⟨ (λ x → lam ((t [ x ]) $ q)) ⟩ ⌜p⌝ ■ η
   ; [][]  = λ {Γ}{Δ}{Θ}{A}{t}{σ}{ρ} →
             [][] ■ cong⟨ t [_] ⟩ (sym ⌜∘⌝)
   ; q[]   = λ {Γ}{Δ}{A}{t}{σ} →
             q[]
   ; lam[] = λ {Γ}{Δ}{A}{B}{t}{σ} →
             lam[] ■ (cong⟨ (λ x → lam (t [ ⌜ σ ⌝ ∘ x ‣ q ])) ⟩ (sym ⌜p⌝)) ■ (cong⟨ (λ x → lam (t [ x ‣ q ])) ⟩ (sym ⌜∘⌝))
   ; $[]   = λ {Γ}{Δ}{A}{B}{t}{u}{σ} →
             $[]
   ; t[id] = λ {Γ}{A}{t} →
             (cong⟨ t [_] ⟩ ⌜id⌝) ■ t[id]
   ; ass   = ass*
   ; idl   = idl*
   ; idr   = idr*
   ; ○η    = refl
   ; ▷β    = ▷β*
   ; ▷η    = ▷η*
   } where open I ; open NormalSub
module S* = Model S*

-- then we need to prove this is a Syntax, only substitution are changed so we will juste show the following :

open NormalSub

-- we need a type and context conversion ??? why

compT : ∀{A} → S*.⟦ A ⟧T ≡ A
compT {I.ι} = refl
compT {A I.⇒ B} = (cong⟨ I._⇒ S*.⟦ B ⟧T ⟩ (compT {A})) ■ (cong⟨ A I.⇒_ ⟩ (compT {B}))

compC : ∀{Γ} → S*.⟦ Γ ⟧C ≡ Γ
compC {I.○} = refl
compC {Γ I.▷ A} = (cong⟨ I._▷ S*.⟦ A ⟧T ⟩ (compC {Γ})) ■ (cong⟨ Γ I.▷_ ⟩ (compT {A}))

transpt : ∀{Γ}{A} → I.Tm (S*.⟦ Γ ⟧C) (S*.⟦ A ⟧T) → I.Tm Γ A
transpt {Γ}{A} t = transp⟨ (λ x → I.Tm (π₁ x) (π₂ x)) ⟩ (compC {Γ} ,= compT {A}) t

compq : ∀{Γ}{A} → transpt (S*.⟦ I.q {Γ}{A} ⟧t) ≡ I.q {Γ}{A}
compq {Γ}{A} = sym (transp$ {_}{_}{_}{λ x → I.Tm ((π₁ x) I.▷ (π₂ x)) (π₂ x)} (λ x _ → I.q {π₁ x}{π₂ x}) (compC {Γ} ,= compT {A}) {S*.⟦ I.q {Γ}{A} ⟧t})

transpS : ∀{Γ Δ} → S*.Sub (S*.⟦ Δ ⟧C) (S*.⟦ Γ ⟧C) → S*.Sub Δ Γ
transpS {Γ}{Δ} = transp⟨ (λ x → Sub* (π₁ x) (π₂ x)) ⟩ (compC {Δ} ,= compC {Γ}) 

transp⌜⌝ : ∀{Γ}{Δ}{σ* : Sub* S*.⟦ Δ ⟧C S*.⟦ Γ ⟧C} → ⌜ transpS σ* ⌝ ≡ transp⟨ (λ x → I.Sub (π₁ x) (π₂ x)) ⟩ (compC {Δ} ,= compC {Γ}) ⌜ σ* ⌝
transp⌜⌝ {Γ}{Δ}{σ*} = transp$ (λ x (σ'* : Sub* (π₁ x) (π₂ x)) → ⌜ σ'* ⌝) (compC {Δ} ,= compC {Γ})

transp‣* : ∀{Γ}{Δ}{A}{σ* : Sub* S*.⟦ Δ ⟧C S*.⟦ Γ ⟧C}{t : I.Tm S*.⟦ Δ ⟧C S*.⟦ A ⟧T} → transpS {Γ I.▷ A}{Δ} (σ* , t) ≡ (transpS σ*) , (transpt t)
transp‣* {Γ}{Δ}{A}{σ*}{t} = transp× {_}{_}{_}{λ x → Sub* (π₁ x) (π₁ (π₂ x))}{_}{λ x → I.Tm (π₁ x) (π₂ (π₂ x))}{_}{_}{σ* , t} (compC {Δ} ,= compC {Γ} ,= compT {A})

transp∘* : ∀{Γ}{Δ}{Θ}{σ* : Sub* S*.⟦ Δ ⟧C S*.⟦ Γ ⟧C}{ρ* : Sub* S*.⟦ Θ ⟧C S*.⟦ Δ ⟧C} → transpS (σ* ∘* ρ*) ≡ (transpS σ*) ∘* (transpS ρ*)
transp∘* {Γ}{Δ}{Θ}{σ*}{ρ*} = (transp∘ (λ {Θ' Δ' Γ'} (ρ' : Sub* Θ' Δ') (σ' : Sub* Δ' Γ') → σ' ∘* ρ') (compC {Θ}) (compC {Δ}) (compC {Γ}))

transpid* : ∀{Γ} → transpS (id* {S*.⟦ Γ ⟧C}) ≡ id* {Γ}
transpid* {Γ} = (sym (transp$ {_}{_}{_}{λ x → Sub* x x}{_}{λ a → Sub* a a} (λ x _ → id* {x}) (compC {Γ}) {S*.⟦ I.id {Γ} ⟧S}))

compProof : DepModel
compProof = record
  { Con•   = λ _ → 𝟙 {lzero}
  ; Ty•    = λ _ → 𝟙 {lzero}
  ; Sub•   = λ {Δ} _ {Γ} _ σ → Lift (⌜ transpS S*.⟦ σ ⟧S ⌝ ≡ σ)
  ; Tm•    = λ {Γ} _ {A} _ t → Lift (transpt S*.⟦ t ⟧t ≡ t)
  ; ○•     = ★
  ; _▷•_   = λ _ _ → ★
  ; _∘•_   = λ {Γ}{_}{Δ}{_}{Θ}{_}{σ} compσ {ρ} compρ →
             ⟪ (cong⟨ ⌜_⌝ ⟩ transp∘*) ■
               (⌜∘⌝) ■
               (cong⟨ ⌜ transpS S*.⟦ σ ⟧S ⌝ I.∘_ ⟩ (unfold compρ)) ■
               (cong⟨ I._∘ ρ ⟩ (unfold compσ))  ⟫
  ; id•    = λ {Γ}{A} →
             ⟪ (transp$ (λ x (σ* : Sub* (π₁ x) (π₂ x)) → ⌜ σ* ⌝) (compC {Γ} ,= compC {Γ})) ■
               (cong⟨ transp⟨ (λ x → I.Sub (π₁ x) (π₂ x)) ⟩ (compC {Γ} ,= compC {Γ}) ⟩ ⌜id⌝) ■
               (sym (transp$ (λ Γ _ → I.id {Γ}) (compC {Γ}) {Γ})) ⟫
  ; ε•     = ⟪ refl ⟫
  ; _‣•_   = λ {Γ}{_}{Δ}{_}{A}{_}{σ} compσ {t} compt → 
             ⟪ (cong⟨ (λ x → ⌜ π₁ x ⌝ I.‣ (π₂ (transpS {Γ I.▷ A} S*.⟦ σ I.‣ t ⟧S))) ⟩ transp‣*) ■
               (cong⟨ I._‣ (π₂ (transpS {Γ I.▷ A} S*.⟦ σ I.‣ t ⟧S)) ⟩ (unfold compσ)) ■
               (cong⟨ (λ x → σ I.‣ (π₂ x)) ⟩ (transp‣* {Γ}{Δ}{A}{S*.⟦ σ ⟧S}{S*.⟦ t ⟧t})) ■
               (cong⟨ σ I.‣_ ⟩ (unfold compt)) ⟫
  ; p•     = λ {Γ}{_}{A} →
             ⟪ (transp⌜⌝) ■
               (cong⟨ transp⟨ (λ x → I.Sub (π₁ x) (π₂ x)) ⟩ (compC ,= compC) ⟩ ⌜p⌝) ■
               (sym (transp$ {_}{_}{_}{(λ x → I.Sub ((π₁ x) I.▷ (π₂ x)) (π₁ x))} (λ x _ → I.p {π₁ x}{π₂ x}) (compC {Γ} ,= compT {A}) {⌜ S*.⟦ I.p {Γ}{A} ⟧S ⌝}))  ⟫
  ; ι•     = ★
  ; _⇒•_   = λ _ _ → ★
  ; _[_]•  = λ {Γ}{_}{Δ}{_}{A}{_}{u} compu {σ} compσ →
             ⟪ (((sym (transp$₂ {_}{I.Con × (I.Con × I.Ty)}
                                {_}{λ x → I.Tm (π₁ x) (π₂ (π₂ x))}
                                {_}{λ x → I.Sub (π₁ (π₂ x)) (π₁ x)}
                                (λ _ → I._[_])
                                (compC {Γ} ,×= (compC {Δ} ,×= compT {A})))) ■
               (cong⟨ transp⟨ (λ x → I.Tm (π₁ x) (π₂ (π₂ x))) ⟩ (compC {Γ} ,×= (compC {Δ} ,×= compT {A})) S*.⟦ u ⟧t I.[_] ⟩ (sym transp⌜⌝))) ■
               (cong⟨ I._[ ⌜ transpS S*.⟦ σ ⟧S ⌝ ] ⟩ (unfold compu))) ■
               (cong⟨ u I.[_] ⟩ (unfold compσ)) ⟫
  ; q•     = ⟪ compq ⟫
  ; lam•   = λ {Γ}{_}{A}{_}{B}{_}{t} compt →
             ⟪ (sym (transp$ {_}{I.Con × (I.Ty × I.Ty)}
                             {_}{λ x → I.Tm ((π₁ x) I.▷ (π₁ (π₂ x))) (π₂ (π₂ x))}
                             (λ _ → I.lam)
                             (compC {Γ} ,×= (compT {A} ,×= compT {B})))) ■
               (cong⟨ I.lam ⟩ (unfold compt)) ⟫
  ; _$•_   = λ {Γ}{_}{A}{_}{B}{_}{t} compt {u} compu →
             ⟪ (sym (transp$₂ {_}{I.Con × (I.Ty × I.Ty)}
                              {_}{λ x → I.Tm (π₁ x) ((π₁ (π₂ x)) I.⇒ (π₂ (π₂ x)))}
                              (λ _ → I._$_)
                              (compC {Γ} ,×= (compT {A} ,×= compT {B})))) ■
               (cong⟨ I._$ (transpt S*.⟦ u ⟧t) ⟩ (unfold compt)) ■
               (cong⟨ t I.$_ ⟩ (unfold compu)) ⟫
               
  ; β• = refl ; η• = refl ; [][]• = refl ; q[]• = refl ; lam[]• = refl ; $[]• = refl ; t[id]• = refl
  ; ass• = refl ; idl• = refl ; idr• = refl ; ○η• = refl ; ▷β• = refl ; ▷η• = refl
  }
module compProof = DepModel compProof

compS : ∀{Γ}{Δ}{σ : I.Sub Δ Γ} → ⌜ transpS S*.⟦ σ ⟧S ⌝ ≡ σ
compS {Γ}{Δ}{σ} = unfold (compProof.⟦ σ ⟧•S)

compt : ∀{Γ}{A}{t : I.Tm Γ A} → transpt S*.⟦ t ⟧t ≡ t
compt {Γ}{A}{t} = unfold (compProof.⟦ t ⟧•t)

-- We can derive a new constructor for DepModel :

record DepModelS* {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]•
  infixr 7 _$•_
  infixr 5 _▷•_
  infixr 6 _∘•_
  infixr 5 _‣•_

  open S*

  field
  
    Con•   : Con → Set lc
    Ty•    : Ty → Set lty
    Sub•   : ∀{Δ} → Con• Δ → ∀{Γ} → Con• Γ → Sub Δ Γ → Set ls
    Tm•    : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → Tm Γ A → Set ltm
    
    ○•     : Con• ○
    _▷•_   : ∀{Γ} → (Γ• : Con• Γ) → ∀{A} → Ty• A → Con• (Γ ▷ A) 

    _∘•_   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{Θ}{Θ• : Con• Θ}{σ} → Sub• Δ• Γ• σ → ∀{ρ} → Sub• Θ• Δ• ρ → Sub• Θ• Γ• (σ ∘ ρ)
    id•    : ∀{Γ}{Γ• : Con• Γ} → Sub• Γ• Γ• id
    ε•     : ∀{Γ}{Γ• : Con• Γ} → Sub• Γ• ○• (ε {Γ})
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
             σ• ≡ ε•
    ▷β•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ}{σ• : Sub• Δ• Γ• σ}{t}{t• : Tm• Δ• A• t} →
             transp⟨ Sub• Δ• Γ• ⟩ ▷β (p• ∘• (σ• ‣• t•)) ≡ σ•
    ▷η•    : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{σ}{σ• : Sub• Δ• (Γ• ▷• A•) σ} →
             transp⟨ Sub• Δ• (Γ• ▷• A•) ⟩ ▷η (p• ∘• σ• ‣• q• [ σ• ]•) ≡ σ•

  DMeqS* : DepModel
  DMeqS* = record
         { Con•   = λ Γ → Con• S*.⟦ Γ ⟧C
         ; Ty•    = λ A → Ty• S*.⟦ A ⟧T
         ; Sub•   = λ Δ• Γ• σ → Sub• Δ• Γ• S*.⟦ σ ⟧S
         ; Tm•    = λ Γ• A• t → Tm• Γ• A• S*.⟦ t ⟧t
         ; ○•     = ○•
         ; _▷•_   = λ Γ• A• → Γ• ▷• A•
         ; _∘•_   = λ σ• ρ• → σ• ∘• ρ•
         ; id•    = id•
         ; ε•     = ε•
         ; _‣•_   = λ σ• t• → σ• ‣• t•
         ; p•     = p•
         ; ι•     = ι•
         ; _⇒•_   = _⇒•_
         ; _[_]•  = λ t• σ• → t• [ σ• ]•
         ; q•     = q•
         ; lam•   = lam•
         ; _$•_   = λ u• v• → u• $• v•
         ; β•     = β•
         ; η•     = η•
         ; [][]•  = [][]•
         ; q[]•   = q[]•
         ; lam[]• = lam[]•
         ; $[]•   = $[]•
         ; t[id]• = t[id]•
         ; ass•   = ass•
         ; idl•   = idl•
         ; idr•   = idr•
         ; ○η•    = ○η•
         ; ▷β•    = ▷β•
         ; ▷η•    = ▷η•
         }
  module DMeqS* = DepModel DMeqS*

  ⟦_⟧•C     : (Γ : Con) → Con• Γ
  ⟦_⟧•T     : (A : Ty) → Ty• A
  postulate
    ⟦_⟧•S   : {Γ Δ : Con} → (σ : Sub Δ Γ) → Sub• ⟦ Δ ⟧•C ⟦ Γ ⟧•C σ
    ⟦_⟧•t   : {Γ : Con}{A : Ty} → (t : Tm Γ A) → Tm• ⟦ Γ ⟧•C ⟦ A ⟧•T t

  ⟦ I.○ ⟧•C = ○•
  ⟦ Γ I.▷ A ⟧•C = ⟦ Γ ⟧•C ▷• ⟦ A ⟧•T
  
  ⟦ I.ι ⟧•T = ι•
  ⟦ A I.⇒ B ⟧•T = ⟦ A ⟧•T ⇒• ⟦ B ⟧•T

  postulate

    ⟦∘⟧•S   : {Γ Δ Θ : Con}{σ : Sub Δ Γ}{ρ : Sub Θ Δ} → ⟦ σ ∘ ρ ⟧•S ≡ ⟦ σ ⟧•S ∘• ⟦ ρ ⟧•S
    ⟦id⟧•S  : {Γ : Con} → ⟦ id {Γ} ⟧•S ≡ id•
    ⟦ε⟧•S   : {Γ : Con} → ⟦_⟧•S {I.○}{Γ} ★ ≡ ε•
    ⟦‣⟧•S   : {Γ Δ : Con}{σ : Sub Δ Γ}{A : Ty}{t : Tm Δ A} → ⟦ σ ‣ t ⟧•S ≡ ⟦ σ ⟧•S ‣• ⟦ t ⟧•t
    ⟦p⟧•S   : {Γ : Con}{A : Ty} → ⟦ p {Γ}{A} ⟧•S ≡ p•
    {-# REWRITE ⟦∘⟧•S ⟦id⟧•S ⟦ε⟧•S ⟦‣⟧•S ⟦p⟧•S #-}
    
    ⟦[]⟧•t  : {Γ Δ : Con}{A : Ty}{t : Tm Γ A}{σ : Sub Δ Γ} → ⟦ t [ σ ] ⟧•t ≡ ⟦ t ⟧•t [ ⟦ σ ⟧•S ]•
    ⟦q⟧•t   : {Γ : Con}{A : Ty} → ⟦ q {Γ}{A} ⟧•t ≡ q•
    ⟦lam⟧•t : {Γ : Con}{A B : Ty}{t : Tm (Γ ▷ A) B} → ⟦ lam t ⟧•t ≡ lam• ⟦ t ⟧•t
    ⟦$⟧•t : {Γ : Con}{A B : Ty}{t : Tm Γ (A I.⇒ B)}{u : Tm Γ A} → ⟦ t $ u ⟧•t ≡ ⟦ t ⟧•t $• ⟦ u ⟧•t
    {-# REWRITE ⟦[]⟧•t ⟦q⟧•t ⟦lam⟧•t ⟦$⟧•t #-}

open Model S*

-- for exemple, in this model this equation is definitional but will not be when strictifying more equations

ex : ∀{Γ Δ Θ}{A}{σ : Sub Δ Γ}{ρ : Sub Θ Δ}{t : Tm Δ A} → (σ , t) ∘ ρ ≡ (σ ∘ ρ , t [ ρ ])
ex = refl
