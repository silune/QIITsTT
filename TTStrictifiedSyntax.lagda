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
  ; El•    = (El [_]) , λ σ → ⟪ refl ⟫ -- not sure about this one ? El[] is not concidered
  ; _[_]•  = λ { {_}{_}{_}{_}{A} (A[_]* , A[_]*=) {σ} _ →
             (A[ σ ]* [_]) , λ σ' → ⟪ cong⟨ _[ σ' ] ⟩ (unfold A[ σ ]*=) ⟫ }
  ; Π•     = λ {_}{_}{A} _ {B} _ →
             (λ σ → Π (A [ σ ]) (B [ σ ⁺ ])) , λ _ → ⟪ sym Π[] ⟫
  
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
              λ {Δ} σ → ⟪ transpsym {_}{_}{_}{Tm Δ} (sym (cong⟨ _[ σ ] ⟩ (unfold A[ ρ ]*=)))  ⟫} 
  ; lam•   = λ { {_}{_}{_}{_}{_}{_}{t}(t⟦_⟧* , t⟦_⟧*=) →
             (λ σ → I.lam (t ⟦ σ ⁺ ⟧)) ,
             λ {Δ} σ → ⟪ (cong⟨ transp⟨ Tm Δ ⟩ (sym Π[]) ⟩ (sym lam[])) ■ transpsym Π[] ⟫}
  ; app•   = {!!}
  
  ; Π[]•   = {!!}
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
  ; _[_]  = {!!}
  ; Π     = {!!}
  ; ρ     = {!!}
  ; ⟨_⟩    = {!!}
  ; _⁺    = {!!}
  ; _⟦_⟧  = {!!}
  ; q     = {!!}
  ; lam   = {!!}
  ; app   = {!!}
  ; Π[]   = {!!}
  ; β     = {!!}
  ; η     = {!!}
  ; U[]   = {!!}
  ; lam[] = {!!}
  ; El[]  = {!!}
  ; q⟨⟩    = {!!}
  ; q+    = {!!}
  ; ρ⟨⟩    = {!!}
  ; ρ+    = {!!}
  }

\end{code}
