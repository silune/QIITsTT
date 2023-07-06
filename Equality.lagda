\begin{code}

-- Definition for propositional equality with some properties

{-# OPTIONS --prop --rewriting #-}

open import Logic
open import Agda.Primitive

module Equality where

  infixr 4 _≡_
  infixr 4 _,=_
  infixr 2 _≡⟨_⟩_
  infixr 2 _■_
  infixr 5 _∘_

  id : ∀{l}{A : Set l} → A → A
  id = λ x → x

  -- Equality

  data _≡_ {l}{A : Set l}(x : A) : A → Prop l where
    refl : x ≡ x

  {-# BUILTIN REWRITE _≡_ #-}

  record Lift {l}(A : Prop l) : Set l where
    constructor ⟪_⟫
    field unfold : A
  open Lift public

  data Single {l}{A : Set l} (x : A) : Set l where
    one : (x' : A) → (x ≡ x') → Single x
 
  single : ∀{l}{A : Set l} → (x : A) → Single x
  single x = one x refl
    
  open Single public
    
  -- Properities

  sym : ∀{l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀{l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  _■_ : ∀{l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _■_ = trans

  _≡⟨_⟩_ : ∀{l}{A : Set l}{y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ eqy ⟩ eqz = trans eqy eqz

  -- (lemma 2.2.1 HoTT)
  cong⟨_⟩ : ∀{l}{A : Set l}{l'}{B : Set l'}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
  cong⟨ f ⟩ refl = refl

  cong$ : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : (a : A) → B a} → f ≡ g → (x : A) → f x ≡ g x
  cong$ refl x = refl

  cong$i : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : {a : A} → B a} → (λ {x} → f {x}) ≡ g → (x : A) → f {x} ≡ g {x}
  cong$i refl x = refl
  
  -- (lemma 2.3.2 HoTT) (need to be postulate when working with Prop instead of Set ?)
  postulate transp⟨_⟩ : ∀{l}{A : Set l}{l'}(P : A → Set l'){x y : A} → x ≡ y → P x → P y
  -- transp⟨ P ⟩ refl px = px

  postulate transprefl : ∀{l}{A : Set l}{l'}{P : A → Set l'}{a : A}{e : a ≡ a}{p : P a} → transp⟨ P ⟩ e p ≡ p
  {-# REWRITE transprefl #-}

  _,=_ : ∀{l}{l'} → {A : Set l}{x x' : A} → (e : x ≡ x') →
                    {B : A → Set l'}{y : B x}{y' : B x'} → transp⟨ B ⟩ e y ≡ y' →
                    (x , y) ≡ (x' , y')
  refl ,= refl = refl

  _,×=_ : ∀{l}{l'} → {A : Set l}{x x' : A} → (ea : x ≡ x') →
                     {B : Set l'}{y y' : B} → (eb : y ≡ y') →
                     (x , y) ≡ (x' , y')
  refl ,×= refl = refl

  transpΣ : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}{C : A → B → Set l''}{a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
            transp⟨ (λ a → Σ B (C a)) ⟩ e w ≡ (pr₁ w , transp⟨ (λ a → C a (pr₁ w)) ⟩ e (pr₂ w))
  transpΣ refl = refl

  transpπ₁ : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}{C : A → B → Set l''}{a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
             pr₁ (transp⟨ (λ a → Σ B (C a)) ⟩ e w) ≡ pr₁ w
  transpπ₁ refl = refl

  transp× : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}{C : A → Set l''}{a a' : A}{x : B a × C a} → (e : a ≡ a') →
            transp⟨ (λ a → B a × C a) ⟩ e x ≡ (transp⟨ B ⟩ e (pr₁ x)) , (transp⟨ C ⟩ e (pr₂ x))
  transp× refl = refl

  -- (lemma 2.3.5 HoTT)
  transpconst : ∀{l}{A : Set l}{l'}{P : Set l'}{x y : A}(eq : x ≡ y){p : P} → transp⟨ (λ _ → P) ⟩ eq p ≡ p
  transpconst refl = refl

  transp$ : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}{C : A → Set l''}(f : (a : A) → B a → C a){a a' : A}(e : a ≡ a'){b : B a} →
            f a' (transp⟨ B ⟩ e b) ≡ transp⟨ C ⟩ e (f a b)
  transp$ _ refl = refl

  transp→ : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}(C : A → Set l''){a a' : A}(e : a ≡ a'){f : B a → C a} → 
            transp⟨ (λ a → B a → C a) ⟩ e f ≡ λ b' → transp⟨ C ⟩ e (f (transp⟨ B ⟩ (sym e) b'))
  transp→ C refl = refl

  transpcong : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}(C : B → Set l'')(f : A → B){a a' : A}(e : a ≡ a'){c : C (f a)} →
               transp⟨_⟩ {A = B} C {f a} {f a'} (cong⟨ f ⟩ e) c ≡ transp⟨_⟩ {A = A} (λ x → C (f x)) {a} {a'} e c
  transpcong _ _ refl = refl

  transptransp : ∀{l}{A : Set l}{l'}{P : A → Set l'}{a a' a'' : A}(e : a ≡ a'){e' : a' ≡ a''}{x : P a} →
              transp⟨ P ⟩ e' (transp⟨ P ⟩ e x) ≡ transp⟨ P ⟩ (e ■ e') x
  transptransp refl {refl} = refl

  -- Functional extensionality (Axiom 2.9.3 HoTT)

  postulate funext  : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : (a : A) → B a} → ((x : A) → f x ≡ g x) → f ≡ g
  postulate funexti : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : {a : A} → B a} → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
  
  _∘_ : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}{C : Set l''} → (f : B → C) → (g : A → B) → (A → C)
  f ∘ g = λ x → f (g x)

\end{code}
