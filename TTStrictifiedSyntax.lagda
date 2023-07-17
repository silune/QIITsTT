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
  { Con•   = λ Γ →
             Σ (∀{Δ} → Sub Δ Γ → Set)
               (λ Γ* → (∀{Δ Ω : Con}{σ : Sub Δ Γ}{ω : Sub Ω Δ} → Γ* σ → isRen Ω Δ ω → Γ* (σ ∘ ω)))
                     
  ; Sub•   = λ { {Δ} (Δ* , _[_]Δ) {Γ} (Γ* , _[_]Γ) σ →
             Σ (∀{Θ}{ρ : Sub Θ Δ} → Δ* ρ → Γ* (σ ∘ ρ))
               (λ σ* → (∀{Θ Ω}{ρ : Sub Θ Δ}{ρ' : Δ* ρ}{ω : Sub Ω Θ}{ωR : isRen Ω Θ ω} →
                        Lift (transp⟨ Γ* ⟩ (sym ass) ((σ* ρ') [ ωR ]Γ) ≡ σ* (ρ' [ ωR ]Δ))))}
                        
  ; Ty•    = λ _ → 𝟙
  ; Tm•    = λ { {Γ} (Γ* , _[_]Γ) {A} _ t →
             Σ (∀{Δ}{σ : Sub Δ Γ} → Γ* σ → Tm Δ A)
               (λ t* →(∀{Δ}{σ : Sub Δ Γ} → (σ' : Γ* σ) → Lift (t* σ' ≡ t [ σ ])))  }
                                
  ; ○•     = (λ σ → 𝟙) ,
             (λ _ _ → ★)
  ; _▷•_   = λ { {Γ} (Γ* , _[_]Γ) {A} _ →
             (λ {Δ} σ → Γ* (p ∘ σ) × (Σ (Tm Δ A) (λ t' → Lift (t' ≡ q [ σ ])))) ,
             (λ { {Δ}{Ω}{σ}{ω} (σ' , t' , ⟪ t'e ⟫) ωR →
                transp⟨ Γ* ⟩ (sym ass) (σ' [ ωR ]Γ) , (t' [ ω ]) , ⟪ (cong⟨ _[ ω ] ⟩ (t'e)) ■ [][] ⟫})} -- ? still a sub

  ; _∘•_   =  λ { {Γ}{Γ* , _[_]Γ}{Δ}{Δ* , _[_]Δ}{Θ}{Θ* , _[_]Θ}{σ} (σ* , σe) {ρ} (ρ* , ρe) →
             (λ x → transp⟨ Γ* ⟩ ass (σ* (ρ* x))) ,
             {!!} }
  ; id•    = λ { {Γ}{Γ* , _[_]Γ} →
             (λ x → transp⟨ Γ* ⟩ (sym idl) x) ,
             {!!}}
  ; ε•     = λ { {Γ}{Γ* , _[_]Γ} →
             (λ _ → ★) ,
             {!!} }
  ; _‣•_   = λ { {Γ}{Γ* , _[_]Γ}{Δ}{Δ* , _[_]Δ}{A}{_}{σ} (σ* , _) {t} (t* , _) →
             (λ {Θ}{ρ} x → transp⟨ Γ* ⟩ ((cong⟨ _∘ ρ ⟩ (sym ▷β)) ■ (sym ass)) (σ* x) , t* x , {!!}) ,
             {!!}}
  ; p•     = λ { {Γ}{Γ* , _[_]Γ}{A}{_} →
             π₁ ,
             {!!}}
  
  ; ι•     = ★
  ; _⇒•_   = λ _ _ → ★

  ; _[_]•  = λ { {Γ}{Γ* , _[_]Γ}{Δ}{Δ* , _[_]Δ}{A}{_}{t} (t* , _) {σ} (σ* , _) →
               (λ x → (t* (σ* x)) ) ,
               {!!}}
  ; q•     = λ { {Γ}{Γ* , _[_]Γ}{A}{_} →
               (λ x → π₁ (π₂ x)) ,
               {!!}}
  ; lam•   = λ { {Γ}{Γ* , _[_]Γ}{A}{_}{B}{_}{t} (t* , _) →
               (λ {_}{σ} σ* → lam (t* {_}{σ ∘ p ‣ q} (transp⟨ Γ* ⟩ (sym ▷β) (σ* [ pRen ]Γ) , q , ⟪ sym q[] ⟫))) ,
               {!!}}
  ; _$•_   = λ { {Γ}{Γ* , _[_]Γ}{A}{_}{B}{_}{t} (t* , _) {u} (u* , _) →
               (λ σ* → (t* σ*) $ (u* σ*)) ,
               {!!}}
  
  ; β•     =  λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=} →
                {!!}}
  ; η•     = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=} →
                {!!}}
  ; [][]•  = λ { {Γ}{_}{Δ}{_}{Θ}{_}{A}{_}{t}{t[_]* , t[_]*=}{σ}{_}{ρ}{_} →
                {!!}}
  ; q[]•   = λ { {Γ}{_}{Δ}{_}{A}{_}{t}{t[_]* , t[_]*=}{σ}{_} →
                {!!}}
  ; lam[]• = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{σ}{_} →
                {!!}}
  ; $[]•   = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=}{σ}{_} →
                {!!}}
  ; t[id]• = λ { {Γ}{_}{A}{_}{t}{t[_]* , t[_]*=} →
                {!!}}
  ; ass•   = {!!}
  ; idl•   = {!!}
  ; idr•   = {!!}
  ; ○η•    = {!!}
  ; ▷β•    = {!!} 
  ; ▷η•    = {!!}
  } where open I
module S = DepModel S

lemmaId : ∀{Γ}{A} → I.id {Γ I.▷ A} ≡ (I.id I.∘ I.p I.‣ I.q)
lemmaId = (sym I.▷η) ■ (cong⟨ I.p I.∘ I.id I.‣_ ⟩ I.t[id]) ■ cong⟨ I._‣ I.q ⟩ (I.idr ■ (sym I.idl))

unquoteId : ∀{Γ : I.Con} → π₁ S.⟦ Γ ⟧•C I.id
unquoteId {I.○} = ★
unquoteId {Γ I.▷ A} = transp⟨ π₁ S.⟦ Γ ⟧•C ⟩ (I.idl ■ (sym I.idr)) ((π₂ S.⟦ Γ ⟧•C (unquoteId {Γ}) pRen)) ,
                         I.q ,
                         ⟪ sym I.t[id] ⟫

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
   ; _[_]  = λ {Γ}{Δ}{A} t σ → π₁ S.⟦ t ⟧•t (π₁ S.⟦ σ ⟧•S (unquoteId {Δ})) 
   ; q     = I.q
   ; lam   = I.lam
   ; _$_   = I._$_
   ; β     = {!!}
   ; η     = {!!}
   ; [][]  = {!!}
   ; q[]   = {!refl!}
   ; lam[] = {!!}
   ; $[]   = refl
   ; t[id] = {!refl!} 
   ; ass   = I.ass
   ; idl   = I.idl
   ; idr   = I.idr
   ; ○η    = I.○η
   ; ▷β    = I.▷β
   ; ▷η    = {!!}
   }
module I* = Model I*

\end{code}


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
