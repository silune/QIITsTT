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
  
  ; ρ•     = ★
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
                              (cong⟨ (λ x → lam (x $ q) [ σ'' ]) ⟩ (unfold t[ ρ ]*=)) ⟫)
              in
              (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift ((v[ σ ]*) ≡ v [ σ ]))}
                                         (η)
                                         {(λ {Δ} (σ : Sub Δ Γ) → lam ((t[ ρ ]* [ σ ⁺ ]) $ (q [ σ ⁺ ]))) , η[_]*=}) Δ') σ') ■
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
  ; ρ⟨⟩•    = λ { {Γ}{_}{A}{_}{B}{_}{t}{t[_]* , t[_]*=}{u}{u[_]* , u[_]*=} →
               (funexti λ Δ' →
                funext  λ σ' →
                let p⟨⟩[_]*= = (λ {Δ''} (σ'' : Sub Δ'' Γ) → ⟪ cong⟨ (λ x → (x [ ⟨ u ⟩ ]) [ σ'' ]) ⟩ (unfold t[ ρ ]*=) ⟫)
                in
                (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                                         {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' Γ) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                                         (ρ⟨⟩)
                                         {(λ {Δ''} (σ'' : Sub Δ'' Γ) → (t[ ρ ]* [ ⟨ u ⟩ ]) [ σ'' ]) , p⟨⟩[_]*= }) Δ') σ') ■
                (unfold p⟨⟩[ σ' ]*=) ■
                (cong⟨ _[ σ' ] ⟩ ρ⟨⟩) ■
                (sym (unfold t[ σ' ]*=))) ,=
               (refl)}
  ; ρ+•    = λ { {Γ}{_}{Δ}{_}{A}{_}{B}{_}{σ}{_}{t}{t[_]* , t[_]*=} →
               let p+[_]*= = (λ {Δ'} (σ' : Sub Δ' (Δ ▷ B)) → ⟪ cong⟨ (λ x → (x [ σ ⁺ ]) [ σ' ]) ⟩ (unfold t[ ρ ]*=) ⟫)
               in
               (funexti λ Δ' →
                funext  λ σ' →
               (cong$ (cong$i (transpπ₁ {_}{_}{_}{_}{_}
                           {λ v v[_]* → (∀{Δ''}(σ'' : Sub Δ'' (Δ ▷ B)) → Lift ((v[ σ'' ]*) ≡ v [ σ'' ]))}
                           (ρ+)
                           {(λ {Δ''} (σ'' : Sub Δ'' (Δ ▷ B)) → (t[ ρ ]* [ σ ⁺ ]) [ σ'' ]) , p+[_]*= }) Δ') σ') ■
                (cong⟨ (λ x → (x [ σ ⁺ ]) [ σ' ]) ⟩ (unfold t[ ρ ]*=)) ■
                 (cong⟨ _[ σ' ] ⟩ ρ+) ■
                 (cong⟨ (λ x → (x [ ρ ]) [ σ' ]) ⟩ (sym (unfold t[ σ ]*=)))) ,=
               (refl)}
  } where open I

\end{code}

S : DepModel
S = record
  { Con•   = λ _ → 𝟙
  ; Ty•    = λ { {Γ} _ A → Σ (∀{Δ} → Sub Δ Γ → Ty Δ)
                              (λ A[_]* → (∀{Δ}(σ : Sub Δ Γ) → Lift (A[ σ ]* ≡ A [ σ ])))
               } 
  ; Sub•   = λ _ _ _ → 𝟙
  ; Tm•    = λ { {Γ} _ (A[_]* , A[_]*=) t → Σ (∀{Δ} → (σ : Sub Δ Γ) → Tm Δ (A[ σ ]*))
                                               (λ t⟦_⟧* → (∀{Δ}(σ : Sub Δ Γ) → Lift (transp⟨ Tm Δ ⟩ (unfold A[ σ ]*=) (t⟦ σ ⟧*) ≡ t ⟦ σ ⟧)))
               }
               
  ; ○•     = ★
  ; _▷•_   = λ _ _ → ★
  
  ; U•     = (λ _ → U) , λ _ → ⟪ sym U[] ⟫
  ; El•    = λ { (a⟦_⟧* , a⟦_⟧*=) →
             (λ σ → El a⟦ σ ⟧*) ,
             λ {Δ} σ → ⟪ (cong⟨ El ⟩ (sym (transptransp (sym U[]) {U[]}))) ■
                         (cong⟨ (λ x → El (transp⟨ Tm Δ ⟩ U[] x)) ⟩ (unfold a⟦ σ ⟧*=)) ■
                         (sym El[]) ⟫}
  ; _[_]•  = λ { {_}{_}{_}{_}{A} (A[_]* , A[_]*=) {σ} _ →
              (λ {Δ'} σ' → A[ σ ]* [ σ' ]) ,
              (λ {Δ'} σ' → ⟪ cong⟨ _[ σ' ] ⟩ (unfold A[ σ ]*=) ⟫)}
  ; Π•     = λ {Γ}{Γ•}{A}(A[_]* , A[_]*=){B}(B[_]* , B[_]*=) →
             (λ {Δ} σ → Π (A[ σ ]*) (B[ transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) ]*)) ,
             (λ {Δ} σ → ⟪ (cong⟨ Π A[ σ ]* ⟩ (unfold B[ transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) ]*=)) ■
                          (cong⟨ (λ x → Π (pr₁ x) (B [ (pr₂ x) ])) ⟩ (unfold A[ σ ]*= ,= refl)) ■
                          (cong⟨ (λ x → Π (A [ σ ]) (B [ x ])) ⟩ (transptransp (sym (unfold A[ σ ]*=)) {unfold A[ σ ]*=})) ■
                          (sym Π[]) ⟫)
  
  ; ρ•     = ★
  ; ⟨_⟩•    = λ _ → ★
  ; _⁺•    = λ _ → ★
  
  ; _⟦_⟧•  = λ { {Γ}{Δ}{_}{_}{A}{A[_]* , A[_]*=}{t}(t⟦_⟧* , t⟦_⟧*=){σ}_ →
             (t⟦ σ ⟧* ⟦_⟧) ,
             λ {Δ'} σ' → ⟪ (transpcong (Tm Δ') (_[ σ' ]) (unfold A[ σ ]*=) {t⟦ σ ⟧* ⟦ σ' ⟧}) ■
                           (sym (transp$ (λ _ → _⟦ σ' ⟧) (unfold A[ σ ]*=))) ■
                          (cong⟨ _⟦ σ' ⟧ ⟩ (unfold t⟦ σ ⟧*=)) ⟫}
  ; q•     = λ { {_}{_}{A}{A[_]* , A[_]*=} →
              (λ {Δ} σ → transp⟨ Tm Δ ⟩ (sym (cong⟨ _[ σ ] ⟩ (unfold A[ ρ ]*=))) (q ⟦ σ ⟧)) ,
              (λ {Δ} σ → ⟪ transptransp {_}{_}{_}{Tm Δ} (sym (cong⟨ _[ σ ] ⟩ (unfold A[ ρ ]*=)))  ⟫)}
  ; lam•   = λ { {Γ}{_}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{t}(t⟦_⟧* , t⟦_⟧*=) →
             let transp⁺ = (λ {Δ} σ → transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺)) in
             let A'[_]*= = (λ {Δ} (σ : Sub Δ Γ) → unfold (A[ σ ]*=)) in
             let B'[_]*= = (λ {Δ} (σ : Sub Δ (Γ ▷ A)) → unfold (B[ σ ]*=)) in
              (λ {Δ} σ → (lam t⟦ transp⁺ σ ⟧*)) ,
              (λ {Δ} σ → let e1 = (cong⟨ (λ x → Π (pr₁ x) (B[ pr₂ x ]*)) ⟩ (sym A'[ σ ]*= ,= refl)) in
                         let ΠABσ*= = (cong⟨ Π A[ σ ]* ⟩ (unfold B[ transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) ]*=)) ■
                                      (cong⟨ (λ x → Π (pr₁ x) (B [ (pr₂ x) ])) ⟩ (unfold A[ σ ]*= ,= refl)) ■
                                      (cong⟨ (λ x → Π (A [ σ ]) (B [ x ])) ⟩ (transptransp (sym (unfold A[ σ ]*=)) {unfold A[ σ ]*=})) ■
                                      (sym Π[])
                         in
                         ⟪ (cong⟨ transp⟨ Tm Δ ⟩ (ΠABσ*=) ⟩
                                (transp$ {_}{_}{_}{λ x → Sub (Δ ▷ (pr₁ x)) (Γ ▷ A)} (λ x _ → lam t⟦ pr₂ x ⟧*) (sym A'[ σ ]*= ,= refl) {σ ⁺})) ■ 
                           (cong⟨ (λ u → transp⟨ Tm Δ ⟩ (ΠABσ*=) u) ⟩
                                (sym (transpcong (Tm Δ) (λ x → Π (pr₁ x) (B[ pr₂ x ]*)) (sym A'[ σ ]*= ,= refl)))) ■
                           (transptransp e1 {ΠABσ*=}) ■
                           (cong⟨ (λ x → transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) (lam x)) ⟩
                                (sym (transptransp {_}{_}{_}{Tm (Δ ▷ A [ σ ])} B'[ σ ⁺ ]*= {sym B'[ σ ⁺ ]*=}))) ■
                           (cong⟨ (λ x → transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) (lam (transp⟨ Tm (Δ ▷ A [ σ ]) ⟩ (sym B'[ σ ⁺ ]*=) x))) ⟩
                                (unfold t⟦ σ ⁺ ⟧*=)) ■
                           (cong⟨ transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) ⟩
                                (transp$ (λ (C : Ty (Δ ▷ A [ σ ])) (x : Tm (Δ ▷ A [ σ ]) C) → lam x) (sym B'[ σ ⁺ ]*=))) ■
                           (cong⟨ transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) ⟩
                                (sym (transpcong (Tm Δ) (Π (A [ σ ])) (sym B'[ σ ⁺ ]*=)))) ■
                           (cong⟨ (λ x → transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) (transp⟨ Tm Δ ⟩ (cong⟨ Π (A [ σ ]) ⟩ (sym B'[ σ ⁺ ]*=)) x)) ⟩
                                (sym lam[])) ■
                           (cong⟨ transp⟨ Tm Δ ⟩ (e1 ■ ΠABσ*=) ⟩
                                (transptransp Π[] {cong⟨ Π (A [ σ ]) ⟩ (sym B'[ σ ⁺ ]*=)})) ■
                           (transptransp (Π[] ■ (cong⟨ Π (A [ σ ]) ⟩ (sym B'[ σ ⁺ ]*=))) {e1 ■ ΠABσ*=}) ⟫)}
  -- app should be replaced with _$_
  ; app•   = λ { {Γ}{Γ•}{A}{A•}{B}{B[_]* , B[_]*=}{u}(u⟦_⟧* , u⟦_⟧*=) →
              (λ {Δ} σ → transp⟨ Tm Δ ⟩ (sym (unfold B[ σ ]*=)) ((app u) ⟦ σ ⟧)) ,
              (λ {Δ} σ → ⟪ transptransp {_}{_}{_}{Tm Δ} (sym (unfold B[ σ ]*=)) ⟫)}
             
  ; Π[]•   = λ { {Γ}{Δ}{_}{_}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{σ} →
             funexti (λ Δ' → funext (λ σ' →
             let transpσ⁺ =  transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) in
             let transpσ'⁺ =  transp⟨ (λ C → Sub (Δ' ▷ C) (Δ ▷ A [ σ ])) ⟩ (cong⟨ _[ σ' ] ⟩ (sym (unfold A[ σ ]*=))) (σ' ⁺) in
              (cong$ (cong$i (transpπ₁ I.Π[]) Δ') σ') ■ 
              (Π[] {Δ}{Δ'}{_}{B[ transpσ⁺ ]*}{σ'}) ■
              (cong⟨ (λ C → Π (A[ σ ]* [ σ' ]) (C [ σ' ⁺ ])) ⟩ (unfold B[ transpσ⁺ ]*=)) ■
              (cong⟨ Π (A[ σ ]* [ σ' ]) ⟩
                ((transp$ {_}{_}{_}{λ C → Sub (Δ ▷ C) (Γ ▷ A)} (λ C σ'' → B [ σ'' ] [ σ' ⁺ ]) (sym (unfold A[ σ ]*=)) { σ ⁺ }) ■
                 (sym (transp$ (λ C σ'' → B [ σ ⁺ ] [ σ'' ]) (sym (unfold A[ σ ]*=)) { σ' ⁺ })) ■
                 (cong⟨ B [ σ ⁺ ] [_] ⟩ (sym (transpcong (λ C → Sub (Δ' ▷ C) (Δ ▷ A [ σ ])) (_[ σ' ]) (sym (unfold A[ σ ]*=))))) ■
                 cong⟨ (λ D → D [ transpσ'⁺ ]) ⟩ (sym (unfold B[ σ ⁺ ]*=))))))
              ,= refl}
  ; β•     = λ { {Γ}{Γ•}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{t}{t⟦_⟧* , t⟦_⟧*=} →
              funexti (λ Δ → funext (λ σ →
                (cong$ (cong$i {_}{_}{_}{_}{_}{λ {Δ'} → (λ σ' → transp⟨ Tm Δ' ⟩ (sym (unfold B[ σ' ]*=)) (app (lam t) ⟦ σ' ⟧))}
                (transpπ₁ {_}{_}{_}{_}{_}
                          {λ u u⟦_⟧* → (∀{Δ'} σ' → Lift (transp⟨ Tm Δ' ⟩ (unfold B[ σ' ]*=) (u⟦ σ' ⟧*) ≡ u ⟦ σ' ⟧))}
                          {_}{t} I.β) Δ) σ) ■
                (cong⟨ (λ x → transp⟨ Tm Δ ⟩ (sym (unfold B[ σ ]*=)) (x ⟦ σ ⟧)) ⟩ (I.β)) ■
                (cong⟨ transp⟨ Tm Δ ⟩ (sym (unfold B[ σ ]*=)) ⟩ (sym (unfold t⟦ σ ⟧*=))) ■
                (transptransp (unfold B[ σ ]*=){sym (unfold B[ σ ]*=)})))
              ,= refl}
  ; η•     = λ { {Γ}{Γ•}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{t}{t⟦_⟧* , t⟦_⟧*=} →
             funexti (λ Δ → funext (λ σ →
             {!!})) ,= refl}
  ; U[]•   = λ {Γ}{Δ}{Γ•}{Δ•}{σ}{σ•} →
             funexti (λ Δ' → funext (λ σ' →
              (cong$ (cong$i (transpπ₁ I.U[]) Δ') σ') ■ I.U[]))
             ,= refl
  ; lam[]• = λ { {Γ}{Δ}{Γ•}{Δ•}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{t}{t⟦_⟧* , t⟦_⟧*=}{σ}{σ•} →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl}
  ; El[]•  = λ { {Γ}{Δ}{Γ•}{Δ•}{a}{a⟦_⟧* , a⟦_⟧*=}{σ}{σ•} →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl}
  ; q⟨⟩•    = λ { {Γ}{Γ•}{A}{A[_]* , A[_]*=}{u}{u⟦_⟧* , u⟦_⟧*=}{e} e• →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl}
  ; q+•    = λ { {Γ}{Δ}{Γ•}{Δ•}{A}{A[_]* , A[_]*=}{σ}{σ•}{e} e• →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl} 
  ; ρ⟨⟩•    = λ { {Γ}{Γ•}{A}{B}{A[_]* , A[_]*=}{B[_]* , B[_]*=}{t}{t⟦_⟧* , t⟦_⟧*=}{u}{u⟦_⟧* , u⟦_⟧*=}{e} e• →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl}
  ; ρ+•    = λ { {Γ}{Δ}{Γ•}{Δ•}{A}{B}{A[_]* , A[_]*=}{B[_]* , B[_]*=}{σ}{σ•}{t}{t⟦_⟧* , t⟦_⟧*=}{e} e• →
             funexti (λ Δ' → funext (λ σ' → {!!})) ,= refl}
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
  
  ; U     = I.U
  ; El    = I.El
  ; _[_]  = λ A → pr₁ (S.⟦ A ⟧•T)
  ; Π     = I.Π
  ; ρ     = I.ρ
  ; ⟨_⟩    = I.⟨_⟩
  ; _⁺    = λ {Γ}{Δ}{A} σ → transp⟨ (λ C → I.Sub (Δ I.▷ C) (Γ I.▷ A)) ⟩ (sym (unfold (pr₂ S.⟦ A ⟧•T σ))) (σ I.⁺)
  ; _⟦_⟧  = λ t → pr₁ (S.⟦ t ⟧•t)
  ; q     = λ {Γ}{A} → transp⟨ I.Tm (Γ I.▷ A) ⟩ (sym (unfold (pr₂ S.⟦ A ⟧•T I.ρ))) I.q
  ; lam   = I.lam
  ; app   = I.app
  ; Π[]   = refl
  ; β     = I.β
  ; η     = I.η
  ; U[]   = refl
  ; lam[] = refl
  ; El[]  = refl
  ; q⟨⟩    = {!!}
  ; q+    = {!!}
  ; ρ⟨⟩    = {!!}
  ; ρ+    = {!!}
  }

\end{code}
