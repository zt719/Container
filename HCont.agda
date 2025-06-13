module HCont where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Level

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

private variable A B C : Ty

infixl 5 _▷_
data Con : Set where
  •   : Con
  _▷_ : Con → Ty → Con

private variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▷ A) A
  vs : Var Γ A → Var (Γ ▷ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Set₁

record Ne (Γ : Con) (B : Ty) : Set₁

data Sp : Con → Ty → Ty → Set₁

data Nf where
  lam : Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

private variable t u : Nf Γ A

record Ne Γ B where
  inductive
  field
    S : Set
    P : Var Γ A → S → Set
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B

private variable m n : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

private variable ts us : Sp Γ A B

HCont : Ty → Set₁
HCont A = Nf • A

{- Semantics -}

⟦_⟧T : Ty → Set₁
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set₁
⟦ • ⟧C = Lift (suc zero) ⊤
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧C → Set
-- record ⟦_⟧ne (_ : Ne Γ *) (γ : ⟦ Γ ⟧C) : Set

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P x s) → ⟦ R x s p ⟧sp γ (⟦ x ⟧v γ))

{-
{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ne {Γ} n γ where
  inductive
  open Ne n
  field
    s : S
    k : {A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ)
-}

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{- Weakening -}

_-_ : (Γ : Con) → Var Γ A → Con
• - ()
(Γ ▷ A) - vz = Γ
(Γ ▷ A) - (vs x) = (Γ - x) ▷ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

{- Variable (Heterogeneous) Equality -}

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y')) | diff .x y' = diff (vs x) (vs y')

{- Weakening Nf -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B
wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B
wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne e) = ne (wkNe x e)

wkNe {Γ} {A} {C} x record { S = S ; P = P ; R = R }
  = record { S = S ; P = P' ; R = R' }
  where
  P' : Var Γ B → S → Set
  P' y  s with eq x y
  P' .x s | same = ⊥
  P' y  s | diff .x y' = P y' s

  R' : (y : Var Γ B) (s : S) → P' y s → Sp Γ B C
  R' y  s p with eq x y
  R' .x s () | same
  R' y  s p  | diff .x y' = wkSp x (R y' s p)

wkSp x ε = ε
wkSp x (n , ns) = wkNf x n , wkSp x ns

{- Auxiliary functions -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (n , ns) u = n , appSp ns u

{- η-expansion -}

nvar : Var Γ A → Nf Γ A
ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x =
  ne2nf (record { S = S ; P = P ; R = R })
  where
  S : Set
  S = ⊤

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y' = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y'

ne2nf {Γ} {*} x = ne x
ne2nf {Γ} {A ⇒ C} record { S = S ; P = P ; R = R } =
  lam (ne2nf (record { S = S ; P = P' ; R = R' }))
  where
  P' : Var (Γ ▷ A) B → S → Set
  P' vz s = ⊥
  P' (vs x) s = P x s

  R' : (x : Var (Γ ▷ A) B) (s : S) → P' x s → Sp (Γ ▷ A) B C
  R' vz s ()
  R' (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

(lam t) [ x := u ] = lam (t [ vs x := wkNf vz u ])
(ne {Γ} record { S = S ; P = P ; R = R }) [ x := u ] =
  ne (record { S = S ; P = P' ; R = R' })
  where
  P' : Var (Γ - x) A → S → Set
  P' y s = P (wkv x y) s

  R' : (y : Var (Γ - x) A) (s : S) → P' y s → Sp (Γ - x) A *
  R' y s p = R (wkv x y) s p < x := u >
  
ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]

{- TODO : Morphism -}

data NfHom : {Γ : Con} {A : Ty} (t u : Nf Γ A) → Set₁

record NeHom (m n : Ne Γ A) : Set₁

data SpHom : {Γ : Con} {A B : Ty} (t u : Sp Γ A B) → Set₁

data NfHom where
  lam : NfHom t u → NfHom (lam t) (lam u)
  ne  : NeHom m n → NfHom (ne m) (ne n)

data SpHom where
  ε   : SpHom {Γ} {A} ε ε
  _,_ : NfHom t u → SpHom ts us → SpHom (t , ts) (u , us)
 
record NeHom {Γ} {B} m n where
  inductive
  open Ne
  field
    f : m .S → n .S
    g : (x : Var Γ A) (s : m .S) → n .P x (f s) → m .P x s
    h : (x : Var Γ A) (s : m .S) (p : n .P x (f s))
      → SpHom (m .R x s (g x s p)) (n .R x (f s) p)

HContHom : HCont A → HCont A → Set₁
HContHom = NfHom {•}

{- Semantics -}

dom : Ty → Con
dom * = •
dom (A ⇒ B) = dom B ▷ A

appDom : ⟦ A ⟧T → ⟦ dom A ⟧C → Set
appDom {*} a (lift tt) = a
appDom {A ⇒ B} f (γ , a) = appDom (f a) γ

{-
⟦_⟧nfHom : {t u : Nf Γ A} → NfHom t u → (γ : ⟦ Γ ⟧C) (δ : ⟦ dom A ⟧C)
  → appDom (⟦ t ⟧nf γ) δ → appDom (⟦ u ⟧nf γ) δ
⟦_⟧nfHom = {!!}

⟦_⟧neHom : {m n : Ne Γ *} → NeHom m n → (γ : ⟦ Γ ⟧C)
  → ⟦ m ⟧ne γ → ⟦ n ⟧ne γ
⟦ record { f = f ; g = g ; h = h } ⟧neHom γ (s , k) = f s , {!!}

⟦_⟧spHom : {ts us : Sp Γ A B} → SpHom ts us → (γ : ⟦ Γ ⟧C) (a : ⟦ A ⟧T)
  → {!⟦ ts ⟧sp!}
⟦_⟧spHom = {!!}

⟦_⟧Hom : {H J : HCont A} → HContHom H J
  → (γ : ⟦ dom A ⟧C) → appDom ⟦ H ⟧ γ → appDom ⟦ J ⟧ γ
⟦ x ⟧Hom γ = ⟦ x ⟧nfHom (lift tt) γ
-}
