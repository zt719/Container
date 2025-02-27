module Hereditary where

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

data Con : Set where
  ∙ : Con
  _▹_ : Con → Ty → Con

variable Γ Δ θ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▹ A) A
  suc : Var Γ A → Var (Γ ▹ B) A

variable x y z : Var Γ A

data Tm : Con → Ty → Set where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

variable t t₁ t₂ u u₁ u₂ : Tm Γ A

-- λf.λz.f ((λx.f x) z)
ex : Tm ∙ ((set ⇒ set) ⇒ (set ⇒ set))
ex = lam (lam (app (var (suc zero))
       (app (lam (app (var (suc (suc zero))) (var zero))) (var zero))))

_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
(Γ ▹ _) - zero = Γ
(Γ ▹ A) - suc x = (Γ - x) ▹ A

wkV : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkV zero y = suc y
wkV (suc x) zero = zero
wkV (suc x) (suc y) = suc (wkV x y)

wkTm : (x : Var Γ A) → Tm (Γ - x) B → Tm Γ B
wkTm x (var v) = var (wkV x v)
wkTm x (lam t) = lam (wkTm (suc x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

data EqV : Var Γ A → Var Γ B → Set where
  same : EqV x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqV x (wkV x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqV x y
eq zero zero = same
eq zero (suc y) = diff zero y
eq (suc x) zero = diff (suc x) zero
eq (suc x) (suc y) with eq x y
eq (suc x) (suc .x) | same = same
eq (suc x) (suc .(wkV x y)) | diff .x y = diff (suc x) (suc y)

substV : Var Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
substV v x u with eq x v
substV v .v u | same = u
substV .(wkV v x) .v u | diff v x = var x

substTm : Tm Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
substTm (var v) x u = substV v x u
substTm (lam t) x u = lam (substTm t (suc x) (wkTm zero u))
substTm (app t₁ t₂) x u = app (substTm t₁ x u) (substTm t₂ x u)

data _≡_ : Tm Γ A → Tm Γ A → Set where
  refl : t ≡ t
  sym  : t ≡ u → u ≡ t
  trans : t ≡ t₁ → t₁ ≡ t₂ → t ≡ t₂
  ap-lam : t ≡ u → lam t ≡ lam u
  ap-app : t₁ ≡ t₂ → u₁ ≡ u₂ → app t₁ u₁ ≡ app t₂ u₂
  β : app (lam t) u ≡ substTm t zero u
  η : lam (app (wkTm zero t) (var zero)) ≡ t

-- Normal Form by Neutural & Spine

data Nf : Con → Ty → Set

data Ne : Con → Set

data Sp : Con → Ty → Set

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ → Nf Γ set

data Ne where
  _,_ : Var Γ A → Sp Γ A → Ne Γ

data Sp where
  ε : Sp Γ set
  _,_ : Nf Γ A → Sp Γ B → Sp Γ (A ⇒ B)

-- λf.λz.f (f z)
ex' : Tm ∙ ((set ⇒ set) ⇒ (set ⇒ set))
ex' = lam (lam (app (var (suc zero)) (app (var (suc zero)) (var zero))))

exnf : Nf ∙ ((set ⇒ set) ⇒ (set ⇒ set))
exnf = lam (lam (ne (suc zero , (ne (suc zero , (ne (zero , ε) , ε)) , ε))))
