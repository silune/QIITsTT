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
  ; Ty•    = λ _ → 𝟙
  ; Sub•   = λ _ _ _ → 𝟙
  ; Tm•    = λ {Γ} _ {A} _ t → Σ (∀{Δ} → (σ : Sub Δ Γ) → Tm Δ A)
                                (λ t[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((t[ σ ]*) ≡ t [ σ ])))
  
  ; ○•     = ★
  ; _▷•_   = λ _ _ → ★
  
  ; p•     = ★
  ; ⟨_⟩•    = λ _ → ★
  ; _⁺•    = λ _ → ★
  
  ; ι•     = ★
  ; _⇒•_   = λ _ _ → ★
  
  ; _[_]•  = λ { {Γ}{_}{Δ}{_}{A}{_}{t} (t[_]* , t[_]*=) {σ} _ →
               (λ {Δ'} σ' → t[ σ ]* [ σ' ]) ,
               (λ {Δ'} σ' → ⟪ cong⟨ _[ σ' ] ⟩ (unfold t[ σ ]*=) ⟫)}
  ; q•     = λ { {Γ}{_}{A}{_} →
               (λ {Δ'} σ' → q [ σ' ]) ,
               (λ {Δ'} σ' → ⟪ refl ⟫)}
  ; lam•   = λ { {Γ}{_}{A}{_}{B}{_}{t} (t[_]* , t[_]*=) →
               (λ {Δ'} σ' → lam t[ σ' ⁺ ]*) ,
               (λ {Δ'} σ' → ⟪ (cong⟨ lam ⟩ (unfold t[ σ' ⁺ ]*=)) ■ (sym lam[]) ⟫)}
  ; _$•_   = λ { {Γ}{_}{A}{_}{B}{_}{t} (t[_]* , t[_]*=) {u} (u[_]* , u[_]*=) →
               (λ {Δ'} σ' → t[ σ' ]* $ u[ σ' ]*) ,
               (λ {Δ'} σ' → ⟪ (cong⟨ _$ u[ σ' ]* ⟩ (unfold t[ σ' ]*=)) ■ (cong⟨ (t [ σ' ])$_ ⟩ (unfold u[ σ' ]*=)) ■ (sym $[]) ⟫)}
  
  ; β•     = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=} →
               let β[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Γ) →
                             ⟪ (cong⟨ (lam t[ σ'' ⁺ ]*) $_ ⟩ (unfold u[ σ'' ]*=)) ■
                               (cong⟨ (λ x → (lam x) $ (u [ σ'' ])) ⟩ (unfold t[ σ'' ⁺ ]*=)) ■
                               (cong⟨ _$ (u [ σ'' ]) ⟩ (sym lam[])) ■
                               (sym $[]) ⟫)
               in
               (funexti λ Δ' →
                funext  λ σ' →
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (β {Γ}{A}{B}{t}{u})
                                         {(λ {Δ} (σ : Sub Δ Γ) → lam t[ σ ⁺ ]* $ u[ σ ]*) , β[_]*=}) Δ') σ') ■ 
                (unfold β[ σ' ]*=) ■
                (cong⟨ _[ σ' ] ⟩ β) ■
                (cong⟨ _[ σ' ] ⟩ (sym (unfold t[ ⟨ u ⟩ ]*=)))) ,=
               (refl) }
  ; η•     = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=} →
             (funexti λ Δ' →
              funext  λ σ' →
              let η[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Γ) →
                            ⟪ (cong⟨ lam ⟩ (sym $[])) ■
                              (sym lam[]) ■
                              (cong⟨ (λ x → lam (x $ q) [ σ'' ]) ⟩ (unfold t[ p ]*=)) ⟫)
              in
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (η)
                                         {(λ {Δ} (σ : Sub Δ Γ) → lam ((t[ p ]* [ σ ⁺ ]) $ (q [ σ ⁺ ]))) , η[_]*=}) Δ') σ') ■
              (unfold η[ σ' ]*=) ■
              (cong⟨ _[ σ' ] ⟩ η) ■
              (sym (unfold t[ σ' ]*=))) ,=
             (refl)}
  ; lam[]• = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{σ}{_} →
               (funexti λ Δ' →
                funext  λ σ' →
                let lam[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Δ) → ⟪ (cong⟨ (λ x → lam x [ σ'' ]) ⟩ (unfold t[ σ ⁺ ]*=)) ■
                                                                    (cong⟨ _[ σ'' ] ⟩ (sym lam[])) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (lam[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → lam t[ σ ⁺ ]* [ σ'' ]) , lam[_]*= }) Δ') σ') ■
                (lam[])) ,=
               (refl)}
  ; $[]•   = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=}{σ}{_} →
               (funexti λ Δ' →
                funext  λ σ' →
                let $[_]*= = (λ {Δ'' : Con} (σ'' : Sub Δ'' Δ) → ⟪ (cong⟨ (λ x → (x $ u[ σ ]*) [ σ'' ]) ⟩ (unfold t[ σ ]*=)) ■
                                                                 (cong⟨ (λ x → ((t [ σ ]) $ x) [ σ'' ]) ⟩ (unfold u[ σ ]*=)) ■
                                                                 (cong⟨ _[ σ'' ] ⟩ (sym $[])) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Δ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         ($[])
                                         {(λ {Δ''} (σ'' : Sub Δ'' Δ) → (t[ σ ]* $ u[ σ ]*) [ σ'' ]) , $[_]*= }) Δ') σ') ■
                ($[])) ,=
               (refl)}
  ; q⟨⟩•    = λ { {Γ}{_}{A}{_}{u}{u[_]* , u[_]*=} →
               (funexti λ Δ' →
                funext  λ σ' →
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (q⟨⟩)
                                         {(λ {Δ} (σ : Sub Δ Γ) → (q [ ⟨ u ⟩ ]) [ σ ]) , (λ {Δ} σ → ⟪ refl ⟫)}) Δ') σ') ■
               (cong⟨ _[ σ' ] ⟩ q⟨⟩) ■
               (sym (unfold u[ σ' ]*=))) ,=
               (refl)}
  ; q+•    = λ { {Γ}{_}{Δ}{_}{A}{_}{σ}{_} →
               (funexti λ Δ' →
                funext  λ σ' →
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' (Δ ▷ A)) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (q+)
                                         {(λ {Δ''} (σ'' : Sub Δ'' (Δ ▷ A)) → (q [ σ ⁺ ]) [ σ'' ]) , (λ {Δ''} σ'' → ⟪ refl ⟫)}) Δ') σ') ■
                (cong⟨ _[ σ' ] ⟩ q+)) ,=
               (refl)}
  ; p⟨⟩•    = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=} →
               (funexti λ Δ' →
                funext  λ σ' →
                let p⟨⟩[_]*= = (λ {Δ''} (σ'' : Sub Δ'' Γ) → ⟪ cong⟨ (λ x → (x [ ⟨ u ⟩ ]) [ σ'' ]) ⟩ (unfold t[ p ]*=) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Γ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (p⟨⟩)
                                         {(λ {Δ''} (σ'' : Sub Δ'' Γ) → (t[ p ]* [ ⟨ u ⟩ ]) [ σ'' ]) , p⟨⟩[_]*= }) Δ') σ') ■
                (unfold p⟨⟩[ σ' ]*=) ■
                (cong⟨ _[ σ' ] ⟩ p⟨⟩) ■
                (sym (unfold t[ σ' ]*=))) ,=
               (refl)}
  ; p+•    = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{σ}{_}{t}{t[_]* , t[_]*=} →
               let p+[_]*= = (λ {Δ'} (σ' : Sub Δ' (Δ ▷ B)) → ⟪ cong⟨ (λ x → (x [ σ ⁺ ]) [ σ' ]) ⟩ (unfold t[ p ]*=) ⟫)
               in
               (funexti λ Δ' →
                funext  λ σ' →
               (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                           {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' (Δ ▷ B)) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                           (p+)
                           {(λ {Δ''} (σ'' : Sub Δ'' (Δ ▷ B)) → (t[ p ]* [ σ ⁺ ]) [ σ'' ]) , p+[_]*= }) Δ') σ') ■
                (cong⟨ (λ x → (x [ σ ⁺ ]) [ σ' ]) ⟩ (unfold t[ p ]*=)) ■
                 (cong⟨ _[ σ' ] ⟩ p+) ■
                 (cong⟨ (λ x → (x [ p ]) [ σ' ]) ⟩ (sym (unfold t[ σ ]*=)))) ,=
               (refl)}
  } where open I
module S = DepModel S

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
   ; p     = I.p
   ; ⟨_⟩    = I.⟨_⟩
   ; _⁺    = I._⁺
   ; _[_]  = λ t σ → (pr₁ S.⟦ t ⟧•t) σ
   ; q     = I.q
   ; lam   = I.lam
   ; _$_   = I._$_
   ; β     = {!!}
   ; η     = {!!}
   ; lam[] = refl
   ; $[]   = refl
   ; q⟨⟩    = {!!}
   ; q+    = {!!}
   ; p⟨⟩    = {!!}
   ; p+    = {!!}
   }

\end{code}
