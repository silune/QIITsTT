\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat
open import TTSyntax
open import SubAsList

module TTStrictifiedSyntax where

-- We can define a more strict syntax by defining _[_] by induction on terms, then mosts of the substitutions law are definitionals

ST : DepModelS*
ST = record
  { Con•   = λ _ → 𝟙 {lzero}
  ; Ty•    = λ _ → 𝟙 {lzero}
  ; Sub•   = λ _ _ _ → 𝟙 {lzero}
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
               (λ { {Δ'} (_ , t) → t}) ,
               (λ {Δ'} σ' → ⟪ sym I.q[] ⟫)}
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
                            ⟪ (cong⟨ (λ x → lam (t[ p ∘ (σ'' ∘ p ‣ q) ]* $ x)) ⟩ (sym q[])) ■
                              (cong⟨ (λ x → lam (x $ (q [ σ'' ∘ p ‣ q ]))) ⟩ (unfold t[ p ∘ (σ'' ∘ p ‣ q) ]*=)) ■
                              (cong⟨ (λ x → lam (x $ (q [ σ'' ∘ p ‣ q ]))) ⟩ (sym [][])) ■
                              (cong⟨ lam ⟩ (sym $[])) ■
                              (sym lam[]) ⟫)
              in
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (η)
                                         { (λ {Δ} (σ : Sub Δ Γ) → lam ((t[ p ∘ (σ ∘ p ‣ q) ]*) $ q)) , η[_]*= }) Δ') σ') ■
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
               ((funexti λ Δ' →
                funext  λ σ' →
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''} (σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (q[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → t [ σ'' ]) , (λ {Δ''} σ'' → ⟪ cong⟨ _[ σ'' ] ⟩ (sym q[]) ⟫)}) Δ') σ') ■
                 (sym (unfold t[ σ' ]*=)))) ,=
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
  } where open S*
module ST = DepModelS* ST

-- Then the model looks like :

I* : Model
I* = record
   { Con   = S*.Con
   ; Ty    = S*.Ty
   ; Sub   = S*.Sub
   ; Tm    = S*.Tm
   ; ○     = S*.○
   ; _▷_   = S*._▷_
   ; ι     = S*.ι
   ; _⇒_   = S*._⇒_
   ; _∘_   = S*._∘_
   ; id    = S*.id
   ; ε     = ★
   ; _‣_   = S*._‣_
   ; p     = S*.p
   ; _[_]  = λ t → π₁ ST.⟦ t ⟧•t
   ; q     = S*.q
   ; lam   = S*.lam
   ; _$_   = S*._$_
   ; β     = λ {Γ}{A}{B}{t}{u} → S*.β ■ (sym (unfold (π₂ (ST.⟦ t ⟧•t) (S*.id S*.‣ u))))
   ; η     = λ {Γ}{A}{B}{t} → (cong⟨ (λ x → S*.lam (x I.$ I.q)) ⟩ (unfold (π₂ (ST.⟦ t ⟧•t) S*.p))) ■ S*.η
   ; [][]  = λ {Γ}{Δ}{Θ}{A}{t}{σ}{ρ} → cong⟨ (λ x → π₁ ST.⟦ x ⟧•t ρ) ⟩ (unfold (π₂ ST.⟦ t ⟧•t σ))
   ; q[]   = refl
   ; lam[] = refl
   ; $[]   = refl
   ; t[id] = λ {Γ}{A}{t} → (unfold (π₂ (ST.⟦ t ⟧•t) S*.id)) ■ S*.t[id] 
   ; ass   = S*.ass
   ; idl   = S*.idl
   ; idr   = S*.idr
   ; ○η    = refl
   ; ▷β    = S*.▷β
   ; ▷η    = (refl ,= sym I.q[]) ■ S*.▷η
   }
module I* = Model I*

-- We still need to show it is equivalent to the syntax :
-- only terms are modified, and one form is not definitionaly the same :

[]comp : ∀{Γ Δ}{A}{t : I*.Tm Γ A}{σ : I*.Sub Δ Γ} → t I*.[ σ ] ≡ t S*.[ σ ]
[]comp {Γ}{Δ}{A}{t}{σ} = unfold (π₂ ST.⟦ t ⟧•t σ)

-- Then we can derive a new DepModel using this syntax !
