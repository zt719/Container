module HContExample where

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product

open import HCont

private
  variable
    A B C : Ty

M : Set → Set
M X = ⊤ ⊎ X

M-HCont : HCont (* ⇒ *)
M-HCont = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Set
  S = Bool

  P : Var (• ▷ *) A → S → Set
  P vz false = ⊥
  P vz true = ⊤

  R : (x : Var (• ▷ *) A) (s : S) → P x s → Sp (• ▷ *) A *
  R vz true tt = ε

M' : Set → Set
M' = ⟦ M-HCont ⟧

H : (Set → Set) → (Set → Set)
H F X = X × F (F X)

H-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
H-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = • ▷ * ⇒ * ▷ *

  S : Set
  S = ⊤
  
  P : Var Γ₀ A → S → Set
  P vz tt = ⊤
  P (vs vz) tt = ⊤

  R : (x : Var Γ₀ A) (s : S) (p : P x s) → Sp Γ₀ A *
  R vz tt tt = ε
  R (vs vz) tt p = napp (nvar (vs vz)) (nvar vz) , ε

H' : (Set → Set) → Set → Set
H' = ⟦ H-HCont ⟧

{-# NON_TERMINATING #-}
Fix : (Set → Set) → Set
Fix F = F (Fix F)

{-# NON_TERMINATING #-}
Fix-Nf : Nf • ((* ⇒ *) ⇒ *)
Fix-Nf = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Set
  S = ⊤

  P : Var (• ▷ * ⇒ *) A → S → Set
  P vz tt = ⊤

  R : (x : Var (• ▷ * ⇒ *) A) (s : S) → P x s → Sp (• ▷ * ⇒ *) A *
  R vz tt tt = napp (nvar vz) (napp (wkNf vz Fix-Nf) (nvar vz)) , ε
