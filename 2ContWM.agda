{-# OPTIONS --guardedness #-}

module Cont.2ContWM where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

variable X Y : Set

postulate
  funExt :
    ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    {f g : (a : A) → B a} →
    ((a : A) → f a ≡ g a) →
    f ≡ g
{-
funExt₂ : ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ} {B : A → Set ℓ'}
  {C : (a : A) → B a → Set ℓ''}
  {f g : (a : A) (b : B a) → C a b}
  (a : A) (b : B a) → f a b ≡ g a b →
  f ≡ g
funExt₂ = {!!}
-}

funExt⁻ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  {f g : (a : A) → B a} →
  f ≡ g →
  (a : A) → f a ≡ g a
funExt⁻ refl a = refl

Σ-≡-intro :
  ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
  Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) →
  (a₁ , b₁) ≡ (a₂ , b₂)
Σ-≡-intro (refl , refl) = refl

{- Containers -}

infix  0 _◃_
infixr 0 _→ᶜ_
infixr 9 _∘ᶜ_

record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set
    
variable
  SP TQ SP' TQ' UV UV' F G : Cont

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

{- Category of Containers -}

record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

→ᶜ-≡-intro :
  {S T : Set} {P : S → Set} {Q : T → Set}
  {fS fS' : S → T} {fP : (s : S) → Q (fS s) → P s}
  {fP' : (s : S) → Q (fS' s) → P s}
  → (eqfS : fS ≡ fS')
  → (fP ≡ λ s q → fP' s (subst (λ v → Q (v s)) eqfS q))
  → _≡_ {_} {(S ◃ P) →ᶜ (T ◃ Q)} (fS ◃ fP) (fS' ◃ fP')
→ᶜ-≡-intro refl refl = refl

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(g ◃ h) ∘ᶜ (g' ◃ h') = (g ∘ g') ◃ λ s → h' s ∘ h (g' s)

{- WM -}

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

W₁ : SP →ᶜ TQ → W SP → W TQ
W₁ (g ◃ h) (sup (s , f)) = sup (g s , λ q → W₁ (g ◃ h) (f (h s q)))

module _ (X : Set) (SP : Cont) (g : ⟦ SP ⟧ X → X) where

  foldW : W SP → X
  foldW (sup (s , f)) = g (s , foldW ∘ f)

  commuteW : (sf : ⟦ SP ⟧ (W SP)) → foldW (sup sf) ≡ g (⟦ SP ⟧₁ foldW sf)
  commuteW sf = refl

  !foldW : (foldW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → foldW' (sup sf) ≡ g (⟦ SP ⟧₁ foldW' sf))
    → (w : W SP) → foldW' w ≡ foldW w
  !foldW foldW' commuteW' (sup (s , f)) = trans (commuteW' (s , f))
    (cong g (Σ-≡-intro (refl , funExt λ a → !foldW foldW' commuteW' (f a))))

{- 2nd Order Container -}

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

2⟦_⟧S' : (H : 2Cont) (T : Set) (Q : T → Set) → Set
2⟦ S ◃ PX + PF + RF ⟧S' T Q
  = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → 2⟦ RF s pf ⟧S' T Q))

2⟦_⟧P' : (H : 2Cont) (T : Set) (Q : T → Set) → 2⟦ H ⟧S' T Q → Set
2⟦ S ◃ PX + PF + RF ⟧P' T Q (s , f)
  = Σ[ pf ∈ PF s ] let (t , f') = f pf in
    Σ[ q ∈ Q t ] (2⟦ RF s pf ⟧P' T Q (f' q) ⊎ PX s)

2⟦_⟧S : (H : 2Cont) (TQ : Cont) → Set
2⟦ H ⟧S (T ◃ Q) = 2⟦ H ⟧S' T Q

2⟦_⟧P : (H : 2Cont) (TQ : Cont) → 2⟦ H ⟧S TQ → Set
2⟦ H ⟧P (T ◃ Q) = 2⟦ H ⟧P' T Q

2⟦_⟧ : 2Cont → Cont → Cont
2⟦ H ⟧ F = 2⟦ H ⟧S F ◃ 2⟦ H ⟧P F

2⟦_⟧S₁ : (H : 2Cont) → F →ᶜ G → 2⟦ H ⟧S F → 2⟦ H ⟧S G
2⟦ S ◃ PX + PF + RF ⟧S₁ (g ◃ h) (s , f)
  = s , λ pf → let (t , f') = f pf in
    g t , λ q → 2⟦ RF s pf ⟧S₁ (g ◃ h) (f' (h t q))

2⟦_⟧P₁ : (H : 2Cont) (gh : F →ᶜ G) (s : 2⟦ H ⟧S F) → 2⟦ H ⟧P G (2⟦ H ⟧S₁ gh s) → 2⟦ H ⟧P F s
2⟦ S ◃ PX + PF + RF ⟧P₁ (g ◃ h) (s , f) (pf , q , inj₁ p')
  = let (t , f') = f pf in pf , h t q , inj₁ (2⟦ RF s pf ⟧P₁ (g ◃ h) (f' (h t q)) p')
2⟦ S ◃ PX + PF + RF ⟧P₁ (g ◃ h) (s , f) (pf , q , inj₂ px)
  = let (t , f') = f pf in pf , h t q , inj₂ px

2⟦_⟧₁ : (H : 2Cont) → F →ᶜ G → 2⟦ H ⟧ F →ᶜ 2⟦ H ⟧ G
2⟦ H ⟧₁ F = 2⟦ H ⟧S₁ F ◃ 2⟦ H ⟧P₁ F

{- 2W & 2M -}

data 2WS' (H H' : 2Cont) : Set
2WP' : (H H' : 2Cont) → 2WS' H H' → Set

data 2WS' H H' where
  2supS' : (open 2Cont H')
    → Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ 2WS' H H ] (2WP' H H t → 2WS' H (RF s pf)))
    → 2WS' H H'

2WP' H (S ◃ PX + PF + RF) (2supS' (s , f))
  = Σ[ pf ∈ PF s ] let (s' , f') = f pf in
    Σ[ p' ∈ 2WP' H H s' ] (2WP' H (RF s pf) (f' p') ⊎ PX s)
    
2W : 2Cont → Cont
2W H = 2WS' H H ◃ 2WP' H H

2supS : {H H' : 2Cont} → 2⟦ H' ⟧S (2W H) → 2WS' H H'
2supS {H} {S ◃ PX + PF + RF} (s , f) =
  2supS' (s , λ pf → let (s' , f') = f pf in s' , λ p' → 2supS (f' p'))

2supP : {H H' : 2Cont} (s : 2⟦ H' ⟧S (2W H)) →
  2WP' H H' (2supS s) → 2⟦ H' ⟧P (2W H) s
2supP {H} {S ◃ PX + PF + RF} (s , f) (pf , p' , inj₁ pr) =
  let (s' , f') = f pf in pf , p' , inj₁ (2supP (f' p') pr)
2supP {H} {S ◃ PX + PF + RF} (s , f) (pf , p' , inj₂ px) =
  pf , p' , inj₂ px

-- 2sup : {H H' : 2Cont} → 2⟦ H' ⟧ (2W' H H) →ᶜ 2W' H H'
-- 2sup = 2supS ◃ 2supP
2sup : {H : 2Cont} → 2⟦ H ⟧ (2W H) →ᶜ 2W H
2sup = 2supS ◃ 2supP

fold2WS' : {H H' : 2Cont} {T : Set} {Q : T → Set} {gh : 2⟦ H' ⟧ (T ◃ Q) →ᶜ (T ◃ Q)}
  → 2WS' H H' → T
  
fold2WP' : {H H' : 2Cont} {T : Set} {Q : T → Set} {gh : 2⟦ H' ⟧ (T ◃ Q) →ᶜ (T ◃ Q)}
  → (s : 2WS' H H') → Q (fold2WS' {H} {H'} {T} {Q} {gh} s)
  → 2WP' H H' s

fold2WS' {H} {S ◃ PX + PF + RF} {T} {Q} {g ◃ h} (2supS' (s , f))
  = g (s , λ pf → let (s' , f') = f pf in fold2WS' {H} {H} {T} {Q} {{!!}} s'
    , λ u → {!!})

fold2WP' = {!!}

{-
fold2W' : {H H' : 2Cont} {F : Cont} {gh : 2⟦ H' ⟧ F →ᶜ F} → 2W' H H' →ᶜ F
fold2W' {H} {H'} {F} {gh} = fold2WS' {H} {H'} {F} {gh} ◃ fold2WP' {H} {H'} {F} {gh}

fold2W : {H : 2Cont} {F : Cont} {gh : 2⟦ H ⟧ F →ᶜ F} → 2W H →ᶜ F
fold2W {H} {F} {gh} = fold2W' {H} {H} {F} {gh}

commute2WS : {H : 2Cont} {F : Cont} {gh : 2⟦ H ⟧ F →ᶜ F}
  → (sf : 2⟦ H ⟧S (2W H)) → fold2WS' (2supS sf) ≡ gh ._→ᶜ_.fS (2⟦ H ⟧S₁ fold2W' sf)
commute2WS = {!!}

commute2W : {H : 2Cont} {F : Cont} {gh : 2⟦ H ⟧ F →ᶜ F}
  → fold2W ∘ᶜ 2sup ≡ gh ∘ᶜ 2⟦ H ⟧₁ fold2W
commute2W {H} {F} {gh} = →ᶜ-≡-intro (funExt commute2WS) {!!}
-}

