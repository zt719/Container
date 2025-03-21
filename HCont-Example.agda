{-# OPTIONS --type-in-type #-}

module HCont-Example where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import HCont

private variable A B C : Ty

{- Bush Example -}

H : (Set → Set) → (Set → Set)
H F X = X × F (F X)

H-HCont : HCont ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
H-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ ∘ ⇒ ∘ ▹ ∘

  X-Nf : Nf Γ₀ ∘
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊤
    P tt (vs vz) = ⊥

    R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
    R tt vz tt = ε
    R tt (vs vz) ()
    
  F-Nf : Nf Γ₀ ∘
  F-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊥
    P tt (vs vz) = ⊤

    R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
    R tt (vs vz) tt = X-Nf , ε
    
  S : Set
  S = ⊤
  
  P : S → Var Γ₀ A → Set
  P tt vz = ⊤
  P tt (vs vz) = ⊤

  R : (s : S) (x : Var Γ₀ A) (p : P s x) → Sp Γ₀ A ∘
  R tt vz tt = ε
  R tt (vs vz) p = F-Nf , ε

{- Plus -}

_∘_ : ((Set → Set) → Set → Set) → ((Set → Set) → Set → Set) → (Set → Set) → Set → Set
(F ∘ G) H X = F H (G H X)

∘-HCont : HCont (((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
∘-HCont = lam (lam (lam (lam (ne (record { S = S ; P = P ; R = R })))))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ ∘ ⇒ ∘ ▹ ∘
  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt vz = ⊥
  P tt (vs vz) = ⊥
  P tt (vs (vs vz)) = ⊥
  P tt (vs (vs (vs vz))) = ⊤

  R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
  R tt (vs (vs (vs vz))) tt 
    = nvar (vs vz) -- 1 = H    
    , nvar (vs (vs vz)) $ nvar (vs vz) $ nvar vz -- 2 1 0 = G H X
    , ε

{- Times -}

_*_ : ((Set → Set) → Set → Set) → ((Set → Set) → Set → Set) → (Set → Set) → Set → Set
(F * G) H X = F (G H) X

*-HCont : HCont (((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
*-HCont = lam (lam (lam (lam (ne (record { S = S ; P = P ; R = R })))))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ ∘ ⇒ ∘ ▹ ∘
  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt vz = ⊥                -- X
  P tt (vs vz) = ⊥           -- H
  P tt (vs (vs vz)) = ⊥      -- G
  P tt (vs (vs (vs vz))) = ⊤ -- F

  R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
  R tt (vs (vs (vs vz))) tt
    = nvar (vs (vs vz)) $ nvar (vs vz) -- 2 1 = G H
    , nvar vz                          -- 0 = X
    , ε
