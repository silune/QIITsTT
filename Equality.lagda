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

  ★-uniqueness : ∀{l} → (a : 𝟙 {l}) → (b : 𝟙 {l}) → a ≡ b
  ★-uniqueness ★ ★ = refl
  
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

  postulate coe : ∀{l}{A B : Set l} → A ≡ B → A → B
  postulate coerefl : ∀{l}{A : Set l}{e : A ≡ A}{x : A} → coe e x ≡ x
  {-# REWRITE coerefl #-}

  -- (lemma 2.3.2 HoTT) (need to be postulate when working with Prop instead of Set ?)
  transp⟨_⟩ : ∀{l}{A : Set l}{l'}(P : A → Set l'){x y : A} → x ≡ y → P x → P y
  transp⟨_⟩ {l}{A}{l'} P {x}{y} e px = coe {l'}{P x}{P y} (cong⟨ P ⟩ e) px

  _,=_ : ∀{l}{l'} → {A : Set l}{x x' : A} → (e : x ≡ x') →
                    {B : A → Set l'}{y : B x}{y' : B x'} → transp⟨ B ⟩ e y ≡ y' →
                    (x , y) ≡ (x' , y')
  refl ,= refl = refl

  _,×=_ : ∀{l}{l'} → {A : Set l}{x x' : A} → (ea : x ≡ x') →
                     {B : Set l'}{y y' : B} → (eb : y ≡ y') →
                     (x , y) ≡ (x' , y')
  refl ,×= refl = refl

  congdep⟨_⟩ : ∀{l}{A : Set l}{l'}{B : A → Set l'}(f : (a : A) → B a){x y : A} → (e : x ≡ y) → transp⟨ B ⟩ e (f x) ≡ f y
  congdep⟨ f ⟩ refl = refl

  transpΣ : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}{C : A → B → Set l''}{a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
            transp⟨ (λ a → Σ B (C a)) ⟩ e w ≡ (π₁ w , transp⟨ (λ a → C a (π₁ w)) ⟩ e (π₂ w))
  transpΣ refl = refl

  transpπ₁ : ∀{l}{A : Set l}{l'}{B : Set l'}{l''}{C : A → B → Set l''}{a a' : A}(e : a ≡ a'){w : Σ B (C a)} →
             π₁ (transp⟨_⟩ {l}{A}{l' ⊔ l''} (λ a → Σ B (C a)) {a} {a'} e w) ≡ π₁ w
  transpπ₁ refl = refl

  transp× : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}{C : A → Set l''}{a a' : A}{x : B a × C a} → (e : a ≡ a') →
            transp⟨ (λ a → B a × C a) ⟩ e x ≡ (transp⟨ B ⟩ e (π₁ x)) , (transp⟨ C ⟩ e (π₂ x))
  transp× refl = refl

  transp$ : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}{C : A → Set l''}(f : (a : A) → B a → C a){a a' : A}(e : a ≡ a'){b : B a} →
            f a' (transp⟨ B ⟩ e b) ≡ transp⟨ C ⟩ e (f a b)
  transp$ _ refl = refl

  transp→ : ∀{l}{A : Set l}{l'}{B : A → Set l'}{l''}(C : A → Set l''){a a' : A}(e : a ≡ a'){f : B a → C a} → 
            transp⟨ (λ a → B a → C a) ⟩ e f ≡ λ b' → transp⟨ C ⟩ e (f (transp⟨ B ⟩ (sym e) b'))
  transp→ C refl = refl

  transptransp : ∀{l}{A : Set l}{l'}{P : A → Set l'}{a a' a'' : A}(e : a ≡ a'){e' : a' ≡ a''}{x : P a} →
                 transp⟨ P ⟩ e' (transp⟨ P ⟩ e x) ≡ transp⟨ P ⟩ (e ■ e') x
  transptransp refl {refl} = refl

  transpeq : ∀{l}{A : Set l}{l'}{P : A → Set l'}{a a' b : A}(e : a ≡ b)(e' : a' ≡ b){x : P a}{y : P a'} → transp⟨ P ⟩ (e ■ (sym e')) x ≡ y →
             transp⟨ P ⟩ e x ≡ transp⟨ P ⟩ e' y
  transpeq refl refl refl = refl

  -- Functional extensionality (Axiom 2.9.3 HoTT)

  postulate funext  : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : (a : A) → B a} → ((x : A) → f x ≡ g x) → f ≡ g
  postulate funexti : ∀{l}{A : Set l}{l'}{B : A → Set l'}{f g : {a : A} → B a} → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g

\end{code}
