{-# OPTIONS --type-in-type #-}

module HCont2 where

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙ : Con
  _▹_ : Con → Ty → Con

infixl 5 _▹_

{-
dom : Ty → Con
dom set = ∙
dom (A ⇒ B) = dom B ▹ A
-}

variable A B C : Ty
variable Γ Δ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▹ A) A
  suc  : Var Γ A → Var (Γ ▹ B) A

data HCont-NF : Con → Ty → Set

record HCont-NE (Γ : Con) : Set

data HCont-SP : Con → Ty → Set

data HCont-NF where
  lam : HCont-NF (Γ ▹ A) B → HCont-NF Γ (A ⇒ B)
  ne  : HCont-NE Γ → HCont-NF Γ set

record HCont-NE Γ where
  inductive
  field
    S : Var Γ A → Set
    P : {x : Var Γ A} (s : S x) → Set
    R : {x : Var Γ A} {s : S x} (p : P s) → HCont-SP Γ A

data HCont-SP where
  ε : HCont-SP Γ set
  _,_ : HCont-NF Γ A → HCont-SP Γ B → HCont-SP Γ (A ⇒ B)

HCont : Ty → Set
HCont A = HCont-NF ∙ A

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

TT : Ty
TT = (set ⇒ set) ⇒ (set ⇒ set)

Γ₀ : Con
Γ₀ = ∙ ▹ set ⇒ set ▹ set

BCont : HCont TT
BCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  R-FA : HCont-NE Γ₀
  R-FA = record { S = S ; P = P ; R = R }
    where
    S : {A : Ty} → Var Γ₀ A → Set
    S zero = ⊤
    S (suc zero) = ⊤

    P : {A : Ty} {x : Var Γ₀ A} → S x → Set
    P {x = zero} tt = ⊤
    P {x = suc zero} s = ⊥

    R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-SP Γ₀ A
    R {x = zero} tt = ε
    R {x = suc zero} ()
  
  R-FFA : HCont-NE Γ₀
  R-FFA = record { S = S ; P = P ; R = R }
    where
    S : {A : Ty} → Var Γ₀ A → Set
    S zero = ⊤
    S (suc zero) = ⊤

    P : {A : Ty} {x : Var Γ₀ A} → S x → Set
    P {x = zero} tt = ⊥
    P {x = suc zero} tt = ⊤

    R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-SP Γ₀ A
    R {x = zero} ()

    R {x = suc zero} p = ne R-FA , ε

  S : {A : Ty} → Var Γ₀ A → Set
  S zero = ⊤
  S (suc zero) = ⊤

  P : {A : Ty} {x : Var Γ₀ A} → S x → Set
  P {x = zero} tt = ⊤
  P {x = suc zero} tt = ⊤

  R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-SP Γ₀ A
  R {x = zero} tt = ε
  R {x = suc zero} tt = ne R-FFA , ε

-- first order containers

record Cont : Set where
  constructor _◃_
  field
    S : Set
    P : S → Set

Cont→HCont : Cont → HCont (set ⇒ set)
Cont→HCont (S ◃ P) = lam (ne (record { S = S' ; P = P' ; R = R }))
  where
  S' : {A : Ty} → Var (∙ ▹ set) A → Set
  S' zero = S

  P' : {A : Ty} {x : Var (∙ ▹ set) A} → S' x → Set
  P' {x = zero} = P

  R : {A : Ty} {x : Var (∙ ▹ set) A} {s : S' x} → P' s → HCont-SP (∙ ▹ set) A
  R {x = zero} {s} p = ε

HCont→Cont : HCont (set ⇒ set) → Cont
HCont→Cont (lam (ne record { S = S ; P = P ; R = R })) = S zero ◃ P

{- Semantics -}

--⟦_⟧HCont : HCont A → Set
--⟦ x ⟧HCont = {!!}
