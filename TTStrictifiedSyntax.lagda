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
  ; Π•     = λ {Γ}{_}{A}(A[_]* , A[_]*=){B}(B[_]* , B[_]*=) →
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
  ; lam•   = λ { {Γ}{_}{A}{A[_]* , A[_]*=}{_}{_}{t}(t⟦_⟧* , t⟦_⟧*=) →
              (λ {Δ} σ → lam (t⟦ transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) ⟧*)) ,
              (λ {Δ} σ → ⟪ ? ⟫) }
  -- app should be replaced with _$_
  ; app•   = λ { {Γ}{Γ•}{A}{A•}{B}{B[_]* , B[_]*=}{u}(u⟦_⟧* , u⟦_⟧*=) →
              (λ {Δ} σ → transp⟨ Tm Δ ⟩ (sym (unfold B[ σ ]*=)) ((app u) ⟦ σ ⟧)) ,
              (λ {Δ} σ → ⟪ transptransp {_}{_}{_}{Tm Δ} (sym (unfold B[ σ ]*=)) ⟫)}
             
  ; Π[]•   = λ { {Γ}{Δ}{_}{_}{A}{A[_]* , A[_]*=}{B}{B[_]* , B[_]*=}{σ} →
             funexti (λ Δ' → funext λ σ' →
             let transpσ⁺ =  transp⟨ (λ C → Sub (Δ ▷ C) (Γ ▷ A)) ⟩ (sym (unfold A[ σ ]*=)) (σ ⁺) in
             let transpσ'⁺ =  transp⟨ (λ C → Sub (Δ' ▷ C) (Δ ▷ A [ σ ])) ⟩ (cong⟨ _[ σ' ] ⟩ (sym (unfold A[ σ ]*=))) (σ' ⁺) in
              (cong$ (cong$i (transpπ₁ I.Π[]) Δ') σ') ■ 
              (Π[] {Δ}{Δ'}{_}{B[ transpσ⁺ ]*}{σ'}) ■
              (cong⟨ (λ C → Π (A[ σ ]* [ σ' ]) (C [ σ' ⁺ ])) ⟩ (unfold B[ transpσ⁺ ]*=)) ■
              (cong⟨ Π (A[ σ ]* [ σ' ]) ⟩
                ((transp$ {_}{_}{_}{λ C → Sub (Δ ▷ C) (Γ ▷ A)} (λ C σ'' → B [ σ'' ] [ σ' ⁺ ]) (sym (unfold A[ σ ]*=)) { σ ⁺ }) ■
                 (sym (transp$ (λ C σ'' → B [ σ ⁺ ] [ σ'' ]) (sym (unfold A[ σ ]*=)) { σ' ⁺ })) ■
                 (cong⟨ B [ σ ⁺ ] [_] ⟩ (sym (transpcong (λ C → Sub (Δ' ▷ C) (Δ ▷ A [ σ ])) (_[ σ' ]) (sym (unfold A[ σ ]*=))))) ■
                 cong⟨ (λ D → D [ transpσ'⁺ ]) ⟩ (sym (unfold B[ σ ⁺ ]*=)))))
              ,= refl}
  ; β•     = {!!}
  ; η•     = {!!}
  ; U[]•   = {!!}
  ; lam[]• = {!!}
  ; El[]•  = {!!}
  ; q⟨⟩•    = {!!}
  ; q+•    = {!!}
  ; ρ⟨⟩•    = {!!}
  ; ρ+•    = {!!}
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
  ; _⁺    = {!!}
  ; _⟦_⟧  = λ t → pr₁ (S.⟦ t ⟧•t)
  ; q     = {!!}
  ; lam   = {!!}
  ; app   = {!!}
  ; Π[]   = refl
  ; β     = {!!}
  ; η     = {!!}
  ; U[]   = refl
  ; lam[] = {!!}
  ; El[]  = refl
  ; q⟨⟩    = {!!}
  ; q+    = {!!}
  ; ρ⟨⟩    = {!!}
  ; ρ+    = {!!}
  }

\end{code}
