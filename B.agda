{-# OPTIONS --cubical #-}

open import Function.Base
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

record Func (F : Set → Set) : Set (ℓ-suc ℓ-zero) where
  constructor _▹_▹_
  field
    fmap : {X Y : Set} → (X → Y) → (F X → F Y)
    fmapid : ({X : Set} → fmap (id {A = X}) ≡ id)
    fmap∘ :  ({X Y Z : Set} (f : Y → Z) (g : X → Y) → fmap (f ∘ g) ≡ fmap f ∘ fmap g)
open Func

record Nat (F G : Set → Set) (FF : Func F) (GG : Func G) : Set (ℓ-suc ℓ-zero) where
  field
    η : (X : Set) → F X → G X
    nat : {X Y : Set} (f : X → Y) → η Y ∘ fmap FF f ≡ fmap GG f ∘ η X
open Nat

postulate
  Nat≡ : ∀ {F G} {FF : Func F} {GG : Func G} {α β : Nat F G FF GG}
    → Nat.η α ≡ Nat.η β → α ≡ β

idNat : {F : Set → Set} {FF : Func F} → Nat F F FF FF
idNat = record { η = λ X → id ; nat = λ f → refl }

∘Nat : {F G H : Set → Set} {FF : Func F} {GG : Func G} {HH : Func H}
  → Nat G H GG HH → Nat F G FF GG → Nat F H FF HH
∘Nat record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
  = record
  { η = λ X → η₁ X ∘ η₂ X
  ; nat = λ {X} {Y} f → cong (η₁ Y ∘_) (nat₂ f) ∙ cong (_∘ η₂ X) (nat₁ f)
  }

B : (Set → Set) → Set → Set
B F X = X × F (F X)

BB : {F : Set → Set} → Func F → Func (B F)
BB (fmap ▹ fmapid ▹ fmap∘)
  = (λ f (x , ffx) → f x , fmap (fmap f) ffx)
  ▹ (λ i (x , ffx) → x , (cong fmap fmapid ∙ fmapid) i ffx)
  ▹ (λ f g i (x , ffx) → f (g x) , (cong fmap (fmap∘ f g) ∙ fmap∘ (fmap f) (fmap g)) i ffx)

B₁ : {F G : Set → Set} {FF : Func F} {GG : Func G} → Nat F G FF GG → Nat (B F) (B G) (BB FF) (BB GG)
B₁ {F} {G} {FF} {GG} record { η = η ; nat = nat }
  = record
  { η = λ X (x , ffx) → x , η (G X) (fmap FF (η X) ffx)
  ; nat = λ f i (x , ffx) → f x , nat-B f i ffx
  }
  where
    nat-B : {X Y : Set} (f : X → Y) → η (G Y) ∘ fmap FF (η Y) ∘ fmap FF (fmap FF f) ≡ fmap GG (fmap GG f) ∘ η (G X) ∘ fmap FF (η X)
    nat-B {X} {Y} f =
      η (G Y) ∘ fmap FF (η Y) ∘ fmap FF (fmap FF f)  ≡⟨ cong (_∘ fmap FF (fmap FF f)) (nat (η Y)) ⟩
      fmap GG (η Y) ∘ η (F Y) ∘ fmap FF (fmap FF f)  ≡⟨ cong (fmap GG (η Y) ∘_) (nat (fmap FF f)) ⟩
      fmap GG (η Y) ∘ fmap GG (fmap FF f) ∘ η (F X)  ≡⟨ cong (_∘ η (F X)) (sym (fmap∘ GG (η Y) (fmap FF f))) ⟩
      fmap GG (η Y ∘ fmap FF f) ∘ η (F X)            ≡⟨ cong (_∘ η (F X)) (cong (fmap GG) (nat f)) ⟩
      fmap GG (fmap GG f ∘ η X) ∘ η (F X)            ≡⟨ cong (_∘ η (F X)) (fmap∘ GG (fmap GG f) (η X)) ⟩
      fmap GG (fmap GG f) ∘ fmap GG (η X) ∘ η (F X)  ≡⟨ cong (fmap GG (fmap GG f) ∘_) (sym (nat (η X))) ⟩
      fmap GG (fmap GG f) ∘ η (G X) ∘ fmap FF (η X)  ∎

Bid : {F : Set → Set} {FF : Func F} → B₁ {F} {F} {FF} {FF} idNat ≡ idNat
Bid {F} {FF} = Nat≡ (λ i X (x , ffx) → x , fmapid FF i ffx)

B∘ : {F G H : Set → Set} {FF : Func F} {GG : Func G} {HH : Func H}
  → (α : Nat G H GG HH) (β : Nat F G FF GG)
  → B₁ (∘Nat α β) ≡ ∘Nat (B₁ α) (B₁ β)
B∘ {F} {G} {H} {FF} {GG} {HH} record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
  = Nat≡ (λ i X (x , ffx) → x , nat-B∘ i ffx)
  where
    nat-B∘ : {X : Set} → 
      η₁ (H X) ∘ η₂ (H X) ∘ fmap FF (η₁ X ∘ η₂ X) ≡
      η₁ (H X) ∘ fmap GG (η₁ X) ∘ η₂ (G X) ∘ fmap FF (η₂ X)
    nat-B∘ {X} =
      η₁ (H X) ∘ η₂ (H X) ∘ fmap FF (η₁ X ∘ η₂ X) ≡⟨ cong ((η₁ (H X) ∘ η₂ (H X)) ∘_) (fmap∘ FF (η₁ X) (η₂ X)) ⟩
      η₁ (H X) ∘ η₂ (H X) ∘ fmap FF (η₁ X) ∘ fmap FF (η₂ X) ≡⟨ cong (η₁ (H X) ∘_) (cong (_∘ fmap FF (η₂ X)) (nat₂ (η₁ X))) ⟩
      η₁ (H X) ∘ fmap GG (η₁ X) ∘ η₂ (G X) ∘ fmap FF (η₂ X) ∎
