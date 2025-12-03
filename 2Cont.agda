{-# OPTIONS --guardedness #-}

module 2Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_]; J)

open import Cont

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

variable H J : 2Cont

record 2⟦_⟧ (SPPR : 2Cont) (F : Cont) (X : Set) : Set where
  inductive
  pattern
  open 2Cont SPPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧ (2⟦ RF s pf ⟧ F X)

app' : 2Cont → Cont → Cont
app' (S ◃ PX + PF + RF) TQ
  = Σᶜ[ s ∈ S ] ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ[ pf ∈ PF s ] (TQ ⊗ᶜ app' (RF s pf) TQ)))

{-
  IH : (s : S) (pf : PF s) → 2⟦ RF s pf ⟧ TQ X ≃ ⟦ app (RF s pf) TQ ⟧ X

  2⟦ S ◃ PX + PF + RF ⟧ TQ X
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (2⟦ RF s pf ⟧ TQ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (⟦ app (RF s pf) TQ ⟧ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (PX s → X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (⟦ ⊤ ◃ λ _ → PX s ⟧ X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, ⟦ (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ) ⟧ X
≃ ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ (app (RF s pf) TQ)) ⟧ X
≃ ⟦ app (S ◃ PX + PF + RF) TQ ⟧ X
-}

appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pf) (T ◃ Q)))

{-
appS : 2Cont → Cont → Set
appS H (T ◃ Q) = Σ[ s ∈ H .S ] ((pf : H .PF s) → Σ[ t ∈ T ] (Q t → appS (H .RF s pf) (T ◃ Q)))
  where open 2Cont
{-# INLINE appS #-}
-}

appP : (H : 2Cont) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ Q t ] (appP (RF s pf) (T ◃ Q) (g q) ⊎ PX s) 

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F

appS₁ : (SPPR : 2Cont) → TQ →ᶜ UV → appS SPPR TQ → appS SPPR UV
appS₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f)
  = s , λ pf → let (t , f') = f pf in
    g t , λ u → appS₁ (RF s pf) (g ◃ h) (f' (h t u))

appP₁ : (SPPR : 2Cont) (gh : TQ →ᶜ UV) (s : appS SPPR TQ) → appP SPPR UV (appS₁ SPPR gh s) → appP SPPR TQ s
appP₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f) (pf , (u , inj₁ p'))
  = let (t , f') = f pf in pf , (h t u , inj₁ (appP₁ (RF s pf) (g ◃ h) (f' (h t u)) p'))
appP₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f) (pf , (u , inj₂ px))
  = let (t , f') = f pf in (pf , (h t u , inj₂ px))

app₁ : (H : 2Cont) → SP →ᶜ TQ → app H SP →ᶜ app H TQ
app₁ H gh = appS₁ H gh ◃ appP₁ H gh

{-
{-# NO_POSITIVITY_CHECK #-}
data 2WS (H : 2Cont) : Set

{-# TERMINATING #-}
2WP : (H : 2Cont) → 2WS H → Set

data 2WS H where
  2supS : appS H (2WS H ◃ 2WP H) → 2WS H

2WP H (2supS s) = appP H (2WS H ◃ 2WP H) {!!}

2supP : {H : 2Cont} (s : appS H (2WS H ◃ 2WP H)) → 2WP H (2supS s) → appP H (2WS H ◃ 2WP H) {!!}
2supP s p = p
-}

{-
2W : 2Cont → Cont
2W H = 2WS H ◃ 2WP H

2sup : {H : 2Cont} → app H (2W H) →ᶜ 2W H
2sup {H} = 2supS ◃ 2supP {H}
-}

--        app₁ H fold2W  
--  app H (2W H)  →  app H TQ  
--
-- 2sup ↓               ↓ inTQ
--
--     2W H       →   TQ
--           fold2W

{-
-- data W (SP : Cont) : Set where
--   sup : ⟦ SP ⟧ (W SP) → W SP
--
-}


{-
appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → (appS (RF s pf) (T ◃ Q))))
-}


{-
⊤²ᶜ : 2Cont
⊤²ᶜ = ⊤ ◃ (λ _ → ⊥) + (λ _ → ⊥) + λ _ ()

⊥²ᶜ : 2Cont
⊥²ᶜ = ⊥ ◃ (λ ()) + (λ ()) + λ ()

_×²ᶜ_ : 2Cont → 2Cont → 2Cont
(S ◃ PX + PF + RF) ×²ᶜ (T ◃ QX + QF + LF)
  = (S × T)
  ◃ (λ (s , t) → PX s ⊎ QX t)
  + (λ (s , t) → PF s ⊎ QF t)
  + λ{ (s , t) (inj₁ p) → RF s p ; (s , t) (inj₂ q) → LF t q }

_⊎²ᶜ_ : 2Cont → 2Cont → 2Cont
(S ◃ PX + PF + RF) ⊎²ᶜ (T ◃ QX + QF + LF)
   = (S ⊎ T)
   ◃ (λ{ (inj₁ s) → PX s ; (inj₂ t) → QX t })
   + (λ{ (inj₁ s) → PF s ; (inj₂ t) → QF t })
   + λ{ (inj₁ s) pf → RF s pf ; (inj₂ t) qf → LF t qf }

{- ... -}

record _→²ᶜ_ (SPPR TQQL : 2Cont) : Set₁ where
  inductive
  constructor _+_+_+_
  pattern
  open 2Cont SPPR
  open 2Cont TQQL renaming (S to T; PX to QX; PF to QF; RF to LF)
  field
    g : S → T
    hx : (s : S) → QX (g s) → PX s
    hf : (s : S) → QF (g s) → PF s
    kf : (s : S) (q : QF (g s)) → RF s (hf s q) →²ᶜ LF (g s) q

⟦_⟧→²ᶜ : H →²ᶜ J → (UV : Cont) → app H UV →ᶜ app J UV
⟦ α ⟧→²ᶜ UV = g' α UV ◃ h' α UV
  where
  g' : H →²ᶜ J → (UV : Cont) → appS H UV → appS J UV
  g' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f)
    = g s , λ qf → let (u , f') = f (hf s qf) in u , λ v → g' (kf s qf) UV (f' v)

  h' : (α : H →²ᶜ J) (UV : Cont) (s' : appS H UV) → appP J UV (g' α UV s') → appP H UV s'
  h' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f) (qf , v , inj₁ idk) = let (u , f') = f (hf s qf) in hf s qf , v , inj₁ (h' (kf s qf) UV (f' v) idk)
  h' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f) (qf , v , inj₂ qx) = hf s qf , v , inj₂ (hx s qx)
-}
