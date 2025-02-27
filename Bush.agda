{-# OPTIONS --guardedness --cubical #-}

module Bush where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  
record Bush (A : Type) : Type where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
open Bush

{-# TERMINATING #-}
Bush₁ : {X Y : Type} → (X → Y) → Bush X → Bush Y
head (Bush₁ f bx) = f (head bx)
tail (Bush₁ f bx) = Bush₁ (Bush₁ f) (tail bx)

private module _ where

  data BT : Type where
    leaf : BT
    node : BT → BT → BT

  {-# TERMINATING #-}
  φ : {A : Type} → (BT → A) → Bush A
  head (φ f) = f leaf
  tail (φ f) = φ (λ l → φ (λ r → f (node l r)))

  ψ : {A : Type} → Bush A → BT → A
  ψ bsh leaf = head bsh
  ψ bsh (node l r) = ψ (ψ (tail bsh) l) r

  {-# TERMINATING #-}
  retr : {A : Type} (f : BT → A) → ψ (φ f) ≡ f
  retr f i leaf = f leaf
  retr f i (node l r) = (
    ψ (φ f) (node l r)
      ≡⟨ (λ j → ψ (retr (λ l′ → φ (λ r′ → f (node l′ r′))) j l) r) ⟩
    ψ (φ (λ r′ → f (node l r′))) r
      ≡⟨ (λ j → retr (λ r′ → f (node l r′)) j r) ⟩ 
    f (node l r) ∎ 
    ) i

  {-# TERMINATING #-}
  sec : {A : Type} (as : Bush A) → φ (ψ as) ≡ as
  head (sec as i) = head as
  tail (sec as i) = (
    tail (φ (ψ as))
      ≡⟨ (λ j → φ (λ l′ → sec (ψ (tail as) l′) j)) ⟩
    φ (ψ (tail as))
      ≡⟨ sec (tail as) ⟩
    tail as ∎
    ) i

  thePath : {A : Type} → (BT → A) ≡ Bush A
  thePath = isoToPath (iso φ ψ sec retr)
