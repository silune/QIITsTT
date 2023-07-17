\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat
open import TTSyntax

module TTStrictifiedSyntax where

-- We can define a more Strict Syntax where most of the equations are definitional

S : DepModel
S = record
  { Con•   = λ _ → 𝟙
  ; Sub•   = λ _ _ _ → 𝟙
  ; Ty•    = λ _ → 𝟙
  ; Tm•    = λ {Γ} _ {A} _ t → Σ (∀{Δ} → (σ :  Sub Δ Γ) → Tm Δ A)
                                (λ t[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((t[ σ ]*) ≡ t [ σ ])))
                                
  ; ○•     = ★
  ; _▷•_   = λ _ _ → ★
  ; _∘•_   = λ _ _ → ★
  ; id•    = ★
  ; ε•     = ★
  ; _‣•_   = λ _ _ → ★
  ; p•     = ★
  ; ι•     = ★
  ; _⇒•_   = λ _ _ → ★
  
  ; _[_]•  = λ { {Γ}{_}{Δ}{_}{A}{_}{t} (t[_]* , t[_]*=) {σ} _ →
               (λ {Δ'} σ' → t[ σ ∘ σ' ]*) ,
               (λ {Δ'} σ' → ⟪ (unfold (t[ σ ∘ σ' ]*=)) ■ (sym [][]) ⟫)}
  ; q•     = λ { {Γ}{_}{A}{_} →
               (λ {Δ'} σ' → q [ σ' ]) ,
               (λ {Δ'} σ' → ⟪ refl ⟫)}
  ; lam•   = λ { {Γ}{_}{A}{_}{B}{_}{t} (t[_]* , t[_]*=) →
               (λ {Δ'} σ' → lam (t[ σ' ∘ p ‣ q ]*)) ,
               (λ {Δ'} σ' → ⟪ (cong⟨ lam ⟩ (unfold t[ σ' ∘ p ‣ q ]*=)) ■ (sym lam[]) ⟫)}
  ; _$•_   = λ { {Γ}{_}{A}{_}{B}{_}{t} (t[_]* , t[_]*=) {u} (u[_]* , u[_]*=) →
               (λ {Δ'} σ' → t[ σ' ]* $ u[ σ' ]*) ,
               (λ {Δ'} σ' → ⟪ (cong⟨ _$ u[ σ' ]* ⟩ (unfold t[ σ' ]*=)) ■ (cong⟨ (t [ σ' ])$_ ⟩ (unfold u[ σ' ]*=)) ■ (sym $[]) ⟫)}
  
  ; β•     =  λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=} →
               let β[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Γ) →
                             ⟪ (cong⟨ (lam t[ σ'' ∘ p ‣ q ]*) $_ ⟩ (unfold u[ σ'' ]*=)) ■
                               (cong⟨ (λ x → (lam x) $ (u [ σ'' ])) ⟩ (unfold t[ σ'' ∘ p ‣ q ]*=)) ■
                               (cong⟨ _$ (u [ σ'' ]) ⟩ (sym lam[])) ■
                               (sym $[]) ⟫)
               in
               (funexti λ Δ' →
                funext  λ σ' →
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (β {Γ}{A}{B}{t}{u})
                                         {(λ {Δ} (σ : Sub Δ Γ) → lam t[ σ ∘ p ‣ q ]* $ u[ σ ]*) , β[_]*=}) Δ') σ') ■
                (unfold β[ σ' ]*=) ■
                (cong⟨ _[ σ' ] ⟩ β) ■
                ([][]) ■
                (sym (unfold t[ (id ‣ u) ∘ σ' ]*=))) ,=
               (refl) }
  ; η•     = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=} →
             (funexti λ Δ' →
              funext  λ σ' →
              let η[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Γ) →
                            ⟪ (cong⟨ (λ x → lam (x $ (q [ σ'' ∘ p ‣ q ]))) ⟩ (unfold t[ p ∘ (σ'' ∘ p ‣ q) ]*=)) ■
                              (cong⟨ (λ x → lam (x $ (q [ σ'' ∘ p ‣ q ]))) ⟩ (sym [][])) ■
                              (cong⟨ lam ⟩ (sym $[])) ■
                              (sym lam[]) ⟫)
              in
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (η)
                                         {(λ {Δ} (σ : Sub Δ Γ) → lam ((t[ p ∘ (σ ∘ p ‣ q) ]*) $ (q [ σ ∘ p ‣ q ]))) , η[_]*=}) Δ') σ') ■
              (unfold η[ σ' ]*=) ■
              (cong⟨ _[ σ' ] ⟩ η) ■
              (sym (unfold t[ σ' ]*=))) ,=
             (refl)}
  ; [][]•  = λ { {Γ}{_}{Δ}{_}{Θ}{_}{A}{_}{t}{t[_]* , t[_]*=}{σ}{_}{ρ}{_} →
             ((funexti λ Δ' →
              funext  λ σ' →
              let [][_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Θ) →
                            ⟪ (unfold t[ σ ∘ ρ ∘ σ'' ]*=) ■
                              (sym [][]) ■
                              (sym [][]) ⟫)
              in
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''} (σ'' : Sub Δ'' Θ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         ([][])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Θ) → t[ σ ∘ ρ ∘ σ'' ]*) , [][_]*=}) Δ') σ') ■
              (cong⟨ t[_]* ⟩ ass))) ,=
             (refl)}
  ; q[]•   = λ { {Γ}{_}{Δ}{_}{A}{_}{t}{t[_]* , t[_]*=}{σ}{_} →
               (
             ((funexti λ Δ' →
              funext  λ σ' →
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''} (σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (q[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → q [ (σ ‣ t) ∘ σ'' ]) , (λ {Δ''} σ'' → ⟪ sym [][] ⟫)}) Δ') σ') ■
               (sym [][]) ■
               (cong⟨ _[ σ' ] ⟩ q[]) ■
               (sym (unfold t[ σ' ]*=))))) ,=
              (refl)}
  ; lam[]• = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{σ}{_} →
               (funexti λ Δ' →
                funext  λ σ' →
                let lam[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Δ) →
                               ⟪ (cong⟨ lam ⟩ (unfold t[ (σ ∘ σ'') ∘ p ‣ q ]*=)) ■
                                 (sym lam[]) ■
                                 (sym [][]) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (lam[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → lam t[ (σ ∘ σ'') ∘ p ‣ q ]*) , lam[_]*= }) Δ') σ') ■
                (unfold lam[ σ' ]*=) ■
                (cong⟨ _[ σ' ] ⟩ lam[]) ■
                (lam[]) ■
                (cong⟨ lam ⟩ [][]) ■
                (cong⟨ lam ⟩ (sym (unfold t[ (σ ∘ p ‣ q) ∘ (σ' ∘ p ‣ q) ]*=)))) ,=
               (refl)}
  ; $[]•   = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=}{σ}{_} →
               (funexti λ Δ' →
                funext  λ σ' →
                let $[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Δ) →
                             ⟪ (cong⟨ _$ u[ σ ∘ σ'' ]* ⟩ (unfold t[ σ ∘ σ'' ]*=)) ■
                               (cong⟨ (t [ σ ∘ σ'' ]) $_ ⟩ (unfold u[ σ ∘ σ'' ]*=)) ■
                               (sym $[]) ■
                               (sym [][]) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         ($[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → (t[ σ ∘ σ'' ]* $ u[ σ ∘ σ'' ]*)) , $[_]*= }) Δ') σ') ■
                refl) ,=
               (refl)}
  ; t[id]• = λ { {Γ}{_}{A}{_}{t}{t[_]* , t[_]*=} →
               ( (funexti λ Δ' →
                funext  λ σ' →
                let t[id][_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Γ) →
                               ⟪ (unfold t[ id ∘ σ'' ]*=) ■
                                 (sym [][]) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Γ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (t[id])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Γ) → t[ id ∘ σ'' ]*) , t[id][_]*= }) Δ') σ') ■
                (cong⟨ t[_]* ⟩ idl))) ,=
               (refl)}
  ; ass•   = refl
  ; idl•   = λ { {σ• = ★} → refl }
  ; idr•   = λ { {σ• = ★} → refl }
  ; ○η•    = λ { {σ• = ★} → refl }
  ; ▷β•    = λ { {σ• = ★} → refl } 
  ; ▷η•    = λ { {σ• = ★} → refl }
  } where open I
module S = DepModel S

I*Sub : I.Con → I.Con → Set
I*Sub Δ I.○ = 𝟙
I*Sub Δ (Γ I.▷ A) = (I*Sub Δ Γ) × (I.Tm Δ A)

I* : Model
I* = record
   { Con   = I.Con
   ; Ty    = I.Ty
   ; Sub   = I.Sub
   ; Tm    = I.Tm
   ; ○     = I.○
   ; _▷_   = I._▷_
   ; ι     = I.ι
   ; _⇒_   = I._⇒_
   ; _∘_   = I._∘_
   ; id    = I.id
   ; ε     = I.ε
   ; _‣_   = I._‣_
   ; p     = I.p
   ; _[_]  = λ t → π₁ S.⟦ t ⟧•t
   ; q     = I.q
   ; lam   = I.lam
   ; _$_   = I._$_
   ; β     = λ {Γ}{A}{B}{t}{u} → I.β ■ (sym (unfold (π₂ (S.⟦ t ⟧•t) (I.id I.‣ u))))
   ; η     = λ {Γ}{A}{B}{t} → (cong⟨ (λ x → I.lam (x I.$ I.q)) ⟩ (unfold (π₂ (S.⟦ t ⟧•t) I.p))) ■ I.η
   ; [][]  = λ {Γ}{Δ}{Θ}{A}{t}{σ}{ρ} → cong⟨ (λ x → π₁ S.⟦ x ⟧•t ρ) ⟩ (unfold (π₂ S.⟦ t ⟧•t σ))
   ; q[]   = I.q[]
   ; lam[] = refl
   ; $[]   = refl
   ; t[id] = λ {Γ}{A}{t} → (unfold (π₂ (S.⟦ t ⟧•t) I.id)) ■ I.t[id] 
   ; ass   = I.ass
   ; idl   = I.idl
   ; idr   = I.idr
   ; ○η    = I.○η
   ; ▷β    = I.▷β
   ; ▷η    = I.▷η
   }
module I* = Model I*

-- Then we need to show this is a syntax :

-- We already have that (I*.⟦_⟧C , I*.⟦_⟧S , I*.⟦_⟧T , I*.⟦_⟧t) are morphism from I to I*
-- Identity is a function from I* to I, we need to show it is a morphism, only terms are differents so :

[]*  : ∀{Γ Δ : I*.Con}{A : I*.Ty}{t : I*.Tm Γ A}{σ : I*.Sub Δ Γ} →
       t I*.[ σ ] ≡ t I.[ σ ]
[]* {Γ}{Δ}{A}{t}{σ} = unfold (π₂ S.⟦ t ⟧•t σ)
q*   : ∀{Γ}{A} → (I*.q {Γ}{A})  ≡ I.q
q*   = refl
lam* : ∀{Γ : I*.Con}{A B : I*.Ty}{t : I*.Tm (Γ I*.▷ A) B} →
       (I*.lam t) ≡ (I.lam t)
lam* = refl
$*   : ∀{Γ : I*.Con}{A B : I*.Ty}{u : I*.Tm Γ (A I*.⇒ B)}{v : I*.Tm Γ A} →
       u I*.$ v ≡ u I.$ v
$*   = refl

record DepModelS {lc}{ls}{lty}{ltm} : Set (lsuc (lc ⊔ ls ⊔ lty ⊔ ltm)) where

  infixr 6 _[_]•
  infixr 7 _$•_
  infixr 5 _▷•_
  infixr 6 _∘•_
  infixr 5 _‣•_

  open I*

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
             transp⟨ Tm• Θ• A• ⟩ ([][] {Γ}{Δ}{Θ}{A}{t}{σ}{ρ}) (t• [ σ• ]• [ ρ• ]•) ≡ t• [ σ• ∘• ρ• ]•
    q[]•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{t}{t• : Tm• Δ• A• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             transp⟨ Tm• Δ• A• ⟩ q[] (q• [ σ• ‣• t• ]•) ≡ t•
    lam[]• : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• (Γ• ▷• A•) B• t}{σ}{σ• : Sub• Δ• Γ• σ} →
             (lam• t•) [ σ• ]• ≡ lam• (t• [ σ• ∘• p• ‣• q• ]•)
    $[]•   : ∀{Γ}{Γ• : Con• Γ}{Δ}{Δ• : Con• Δ}{A}{A• : Ty• A}{B}{B• : Ty• B}{t}{t• : Tm• Γ• (A• ⇒• B•) t}
             {u}{u• : Tm• Γ• A• u}{σ}{σ• : Sub• Δ• Γ• σ} →
             (t• $• u•) [ σ• ]• ≡ (t• [ σ• ]•) $• (u• [ σ• ]•)
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
 
  DMeq : DepModel
  DMeq = record
       { Con• = Con• ; ○• = ○• ; _▷•_ = _▷•_
       ; Sub• = Sub• ; _∘•_ = _∘•_ ; id• = id• ; ε• = ε• ; _‣•_ = _‣•_ ; p• = p•
       ; Ty• = Ty• ; ι• = ι• ; _⇒•_ = _⇒•_
       ; Tm• = Tm•
       ; _[_]• = λ {Γ}{Γ•}{Δ}{Δ•}{A}{A•}{t} t• {σ} σ• →
                 transp⟨ Tm• Δ• A• ⟩ ([]*) (t• [ σ• ]•)
       ; q• = q• ; lam• = lam• ; _$•_ = _$•_
       ; β•     = λ {Γ}{Γ•}{A}{A•}{B}{B•}{t}{t•}{u}{u•} →
                  (sym (transptransp (Tm• Γ• B•) β []*)) ■ (cong⟨ transp⟨ Tm• Γ• B• ⟩ []* ⟩ β•)
       ; η•     = λ {Γ}{Γ•}{A}{A•}{B}{B•}{t}{t•} →
                  (cong⟨ transp⟨ Tm• Γ• (A• ⇒• B•) ⟩ I.η ⟩
                     (transp$ (λ x (x• : Tm• (Γ• ▷• A•) (A• ⇒• B•) x) → lam• (x• $• q•)) []*)) ■
                  (transptransp (Tm• Γ• (A• ⇒• B•)) (cong⟨ (λ x → lam (x $ q)) ⟩ []*) I.η) ■
                  (η•)
       ; [][]•  = λ {Γ}{Γ•}{Δ}{Δ•}{Θ}{Θ•}{A}{A•}{t}{t•}{σ}{σ•}{ρ}{ρ•} →
                  (cong⟨ (λ x → transp⟨ Tm• Θ• A• ⟩ I.[][] (transp⟨ Tm• Θ• A• ⟩ []* x)) ⟩
                      (transp$ (λ x (x• : Tm• Δ• A• x) → x• [ ρ• ]•) []*)) ■
                  (transptransp (Tm• Θ• A•) []* I.[][]) ■
                  (transptransp (Tm• Θ• A•) (cong⟨ (λ x → x [ ρ ]) ⟩ ([]* {Γ}{Δ}{A}{t}{σ})) ([]* ■ I.[][])) ■
                  (sym (transptransp (Tm• Θ• A•) ([][] {Γ}{Δ}{Θ}{A}{t}{σ}{ρ}) []*)) ■
                  (cong⟨ transp⟨ Tm• Θ• A• ⟩ []* ⟩ [][]•)
       ; q[]•   = q[]•
       ; lam[]• = λ {Γ}{Γ•}{Δ}{Δ•}{A}{A•}{B}{B•}{t}{t•}{σ}{σ•} →
                  {!!}
       ; $[]•   = {!!}
       ; t[id]• = {!!}
       ; ass• = ass• ; idl• = idl• ; idr• = idr• ; ○η• = ○η• ; ▷β• = ▷β• ; ▷η• = ▷η•
       }
