module Hereditary where

{- The calculus -}

data Ty : Set where
  ∘   : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

data Con : Set where
  •   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y z : Var Γ A

data Tm : Con → Ty → Set where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  
{- Weakening -}

_-_ : (Γ : Con) → Var Γ A → Con
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - vs x = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
... | same = same
... | diff .x y = diff (vs x) (vs y)

{- Term weakening -}

wkTm : (x : Var Γ A) → Tm (Γ - x) B → Tm Γ B
wkTm x (var v) = var (wkv x v)
wkTm x (lam t) = lam (wkTm (vs x) t)
wkTm x (app t u) = app (wkTm x t) (wkTm x u)

{- Substitution function -}

substVar : Var Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x

subst : Tm Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
subst (var v) x u = substVar v x u
subst (lam t) x u = lam (subst t (vs x) (wkTm vz u))
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)

data Tms : Con → Con → Set where
  ε   : Tms Γ •
  _,_ : Tms Δ Γ → Tm Δ A → Tms Δ (Γ ▹ A)

wkTms : (x : Var Δ A) → Tms (Δ - x) Γ → Tms Δ Γ
wkTms x ε = ε
wkTms x (γ , t) = wkTms x γ , wkTm x t

_↑ : Tms Δ Γ → Tms (Δ ▹ A) (Γ ▹ A)
γ ↑ = wkTms vz γ , var vz

id : Tms Γ Γ
id {•} = ε
id {Γ ▹ A} = id ↑

_[_]v : Var Γ A → Tms Δ Γ → Tm Δ A
vz [ γ , t ]v = t
vs x [ γ , t ]v = x [ γ ]v

_[_] : Tm Γ A → Tms Δ Γ → Tm Δ A
var x [ γ ] = x [ γ ]v
lam t [ γ ] = lam (t [ γ ↑ ])
app t u [ γ ] = app (t [ γ ]) (u [ γ ])

{- Convertibility -}

module _ where

  private variable t t₁ t₂ t₃ u u₁ u₂ : Tm Γ A

  data _βη-≡_ : Tm Γ A → Tm Γ A → Set where
    brefl : t βη-≡ t
    bsym : t βη-≡ u → u βη-≡ t
    btrans : t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
    congLam : t₁ βη-≡ t₂ → lam t₁ βη-≡ lam t₂
    congApp : t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₂ βη-≡ app t₂ u₂
    beta : app (lam t) u βη-≡ subst t vz u
    eta  : lam (app (wkTm vz t) (var vz)) βη-≡ t

{- Normal forms -}

data Nf : Con → Ty → Set

data Ne : Con → Ty → Set

data Sp : Con → Ty → Ty → Set

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ ∘ → Nf Γ ∘

data Ne where
  _,_ : Var Γ A → Sp Γ A B → Ne Γ B

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

variable t u : Nf Γ A

embNf : Nf Γ A → Tm Γ A
embNe : Ne Γ A → Tm Γ A
embSp : Sp Γ A B → Tm Γ A → Tm Γ B

embNf (lam n) = lam (embNf n)
embNf (ne e) = embNe e

embNe (v , s) = embSp s (var v)

embSp ε t = t
embSp (n , ns) t = embSp ns (app t (embNf n))

emb = embNf

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B
wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B
wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam n) = lam (wkNf (vs x) n)
wkNf x (ne e) = ne (wkNe x e)

wkNe x (v , ns) = wkv x v , wkSp x ns

wkSp x ε = ε
wkSp x (n , ns) = wkNf x n , wkSp x ns

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε n = n , ε
appSp (t , ts) n = t , appSp ts n

nvar : Var Γ A → Nf Γ A
ne2nf : Ne Γ A → Nf Γ A

nvar x = ne2nf (x , ε)

ne2nf {A = ∘} e = ne e
ne2nf {A = A ⇒ B} (v , ns) =
  lam (ne2nf {A = B} (vs v , appSp (wkSp vz ns) (nvar vz)))

{- Nomarlization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne (y , ts) [ x := u ] with eq x y
... | same = u ◇ (ts < x := u >)
... | diff .x y' = ne (y' , (ts < x := u >))

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]

nf : Tm Γ A → Nf Γ A
nf (var x) = nvar x
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)

{- Completeness & Soundness -}

compNe : (e : Ne Γ A) → emb (ne2nf e) βη-≡ embNe e
compVar : (x : Var Γ A) → emb (nvar x) βη-≡ var x

compNe {A = ∘} (x , ts) = {!!}
compNe {A = A ⇒ B} e = {!!}

compVar x = {!!}

completeness : (t : Tm Γ A) → emb (nf t) βη-≡ t
completeness = {!!}

open import Relation.Binary.PropositionalEquality

soundness : (t : Nf Γ A) → nf (emb t) ≡ t
soundness = {!!}


{- Substitution -}

data Nfs : Con → Con → Set where
  ε   : Nfs Γ •
  _,_ : Nfs Δ Γ → Nf Δ A → Nfs Δ (Γ ▹ A)

wkNfs : (x : Var Δ A) → Nfs (Δ - x) Γ → Nfs Δ Γ
wkNfs x ε = ε
wkNfs x (γ , t) = wkNfs x γ , wkNf x t

_↑nf : Nfs Δ Γ → Nfs (Δ ▹ A) (Γ ▹ A)
γ ↑nf = wkNfs vz γ , nvar vz

idNfs : Nfs Γ Γ
idNfs {•} = ε
idNfs {Γ ▹ A} = idNfs ↑nf

subNvar : Var Γ A → Nfs Δ Γ → Nf Δ A
subNvar vz (γ , t) = t
subNvar (vs x) (γ , t) = subNvar x γ

foldSp : Nf Γ A → Sp Γ A B → Nf Γ B
foldSp t ε = t
foldSp t (u , us) = foldSp (napp t u) us

_[_]nf : Nf Γ A → Nfs Δ Γ → Nf Δ A

_[_]sp : Sp Γ A B → Nfs Δ Γ → Sp Δ A B

lam t [ γ ]nf = lam (t [ γ ↑nf ]nf)
ne (x , ts) [ γ ]nf = foldSp (subNvar x γ) (ts [ γ ]sp)

ε [ γ ]sp = ε
(t , ts) [ γ ]sp = (t [ γ ]nf) , (ts [ γ ]sp)

_∘nfs_ : Nfs Δ Γ → Nfs Θ Δ → Nfs Θ Γ
ε ∘nfs x₁ = ε
(δ , t) ∘nfs γ = (δ ∘nfs γ) , (t [ γ ]nf)
