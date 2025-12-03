module HCont where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

{- Kinds & Contexts & Variables -}

infixr 20 _⇒_
data Kind : Set where
  * : Kind
  _⇒_ : Kind → Kind → Kind

variable A B C : Kind

infixl 5 _▹_
data Con : Set where
  •   : Con
  _▹_ : Con → Kind → Con

variable Γ Δ Θ : Con

data Var : Con → Kind → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Normal Forms -}

infixr 4 _,_

data Nf : Con → Kind → Set₁

record Ne (Γ : Con) (B : Kind) : Set₁

data Sp : Con → Kind → Kind → Set₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

variable t u w : Nf Γ A

record Ne Γ B where
  constructor _◃_◃_
  inductive
  field
    S : Set
    P : Var Γ A → S → Set
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B

variable spr tql : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  
variable ts us ws : Sp Γ A B

HCont : Kind → Set₁
HCont = Nf •

ap : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
ap (lam t) = t

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

{- Variable Weakening & (Heterogeneous) Equality -}

_-_ : (Γ : Con) → Var Γ A → Con
• - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

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
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y′)) | diff .x y′ = diff (vs x) (vs y′)

{- Normal Forms Weakening -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B

wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne spr) = ne (wkNe x spr)

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S′ ◃ P′ ◃ R′
  where
  S′ : Set
  S′ = S
  
  P′ : Var Γ B → S → Set
  P′ y  s with eq x y
  P′ .x s | same = ⊥
  P′ y  s | diff .x y′ = P y′ s

  R′ : (y : Var Γ B) (s : S) → P′ y s → Sp Γ B C
  R′ y s p with eq x y
  R′ y s p | diff .x y′ = wkSp x (R y′ s p)

wkSp x ε = ε
wkSp x (t , ts) = wkNf x t , wkSp x ts

{- η-expansion -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (t , ts) u = t , appSp ts u

nvar : Var Γ A → Nf Γ A

ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Set
  S = ⊤

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y′ = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y′

ne2nf {Γ} {*} spr = ne spr
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P′ ◃ R′))
  where
  P′ : Var (Γ ▹ A) B → S → Set
  P′ vz s = ⊥
  P′ (vs x) s = P x s

  R′ : (x : Var (Γ ▹ A) B) (s : S) → P′ x s → Sp (Γ ▹ A) B C
  R′ vz s ()
  R′ (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} (S ◃ P ◃ R) [ x := u ] = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S
  
  P′ : Var (Γ - x) A → S → Set
  P′ y s = P (wkv x y) s
  
  R′ : (y : Var (Γ - x) A) (s : S) → P′ y s → Sp (Γ - x) A *
  R′ y s p = R (wkv x y) s p < x := u >

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
napp (lam t) u = t [ vz := u ]

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B
t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

{- Algebraic Structures -}

⊤nf : Nf Γ A
⊤nf {Γ} {*} = ne (⊤ ◃ (λ{ x tt → ⊥ }) ◃ λ{ x tt () })
⊤nf {Γ} {A ⇒ B} = lam ⊤nf

⊥nf : Nf Γ A
⊥nf {Γ} {*} = ne (⊥ ◃ (λ x ()) ◃ (λ x ()))
⊥nf {Γ} {A ⇒ B} = lam ⊥nf

_×nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ×nf lam u = lam (t ×nf u)
_×nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S × T

  P′ : Var Γ A → S′ → Set
  P′ x (s , t) = P x s ⊎ Q x t

  R′ : (x : Var Γ A) (s : S′) → P′ x s → Sp Γ A B
  R′ x (s , t) (inj₁ p) = R x s p
  R′ x (s , t) (inj₂ q) = L x t q

_⊎nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ⊎nf lam u = lam (t ⊎nf u)
_⊎nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S ⊎ T

  P′ : Var Γ A → S′ → Set
  P′ x (inj₁ s) = P x s
  P′ x (inj₂ t) = Q x t

  R′ : (x : Var Γ A) (s : S′) → P′ x s → Sp Γ A B
  R′ x (inj₁ s) p = R x s p
  R′ x (inj₂ t) q = L x t q

Πnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf {Γ} {A ⇒ B} I ts = lam (Πnf I (λ i → ap (ts i)))
Πnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Set
  S = (i : I) → en (ts i) .Ne.S

  P : Var Γ A → S → Set
  P x f = Σ[ i ∈ I ] en (ts i) .Ne.P x (f i)

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x f (i , p) = en (ts i) .Ne.R x (f i) p

Σnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf {Γ} {A ⇒ B} I ts = lam (Σnf I (λ i → ap (ts i)))
Σnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Set
  S = Σ[ i ∈ I ] en (ts i) .Ne.S

  P : Var Γ A → S → Set
  P x (i , s) = en (ts i) .Ne.P x s

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x (i , s) p = en (ts i) .Ne.R x s p

infix 2 Σnf-syntax
Σnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf-syntax = Πnf
syntax Σnf-syntax A (λ x → B) = Σnf[ x ∈ A ] B

infix 2 Πnf-syntax
Πnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf-syntax = Πnf
syntax Πnf-syntax A (λ x → B) = Πnf[ x ∈ A ] B

{- Morphisms -}

data NfHom : (Γ : Con) → Nf Γ A → Nf Γ A → Set₁

record NeHom Γ {B} (spr tql : Ne Γ B) : Set₁

data SpHom : (Γ : Con) → Sp Γ A B → Sp Γ A B → Set₁

data NfHom where
  lam : NfHom (Γ ▹ A) t u → NfHom Γ (lam t) (lam u)
  ne  : NeHom Γ spr tql → NfHom Γ (ne spr) (ne tql)

record NeHom Γ {B} spr tql where
  constructor _◃_◃_
  inductive
  open Ne spr
  open Ne tql renaming (S to T; P to Q; R to L)
  field
    f : S → T
    g : (x : Var Γ A) (s : S) → Q x (f s) → P x s
    h : (x : Var Γ A) (s : S) (q : Q x (f s))
      → SpHom Γ (R x s (g x s q)) (L x (f s) q)
       
data SpHom where
  ε   : SpHom Γ ts ts
  _,_ : NfHom Γ t u → SpHom Γ ts us → SpHom Γ (t , ts) (u , us)

HContHom : HCont A → HCont A → Set₁
HContHom = NfHom •

idNfHom : NfHom Γ t t
idNfHom {t = ne spr} = ne (id ◃ (λ x s → id) ◃ λ x s q → ε)
idNfHom {t = lam t} = lam (idNfHom {t = t})

_∘nfHom_ : NfHom Γ u w → NfHom Γ t u → NfHom Γ t w
_∘spHom_ : SpHom Γ us ws → SpHom Γ ts us → SpHom Γ ts ws

lam f ∘nfHom lam g = lam (f ∘nfHom g)
ne (f ◃ g ◃ h) ∘nfHom ne (f′ ◃ g′ ◃ h′) = ne (
  (f ∘ f′)
  ◃ (λ x s → g′ x s ∘ g x (f′ s))
  ◃ λ x s q → (h x (f′ s) q) ∘spHom h′ x s (g x (f′ s) q)
  )

ε ∘spHom ε = ε
ε ∘spHom (g , gs) = g , gs
(f , fs) ∘spHom ε = f , fs
(f , fs) ∘spHom (g , gs) = (f ∘nfHom g) , (fs ∘spHom gs)

wkNfHom : (x : Var Γ A) {t u : Nf (Γ - x) B} → NfHom (Γ - x) t u → NfHom Γ (wkNf x t) (wkNf x u)

wkNeHom : (x : Var Γ A) {spr tql : Ne (Γ - x) B} → NeHom (Γ - x) spr tql → NeHom Γ (wkNe x spr) (wkNe x tql)

wkSpHom : (x : Var Γ A) {ts us : Sp (Γ - x) B C} → SpHom (Γ - x) ts us → SpHom Γ (wkSp x ts) (wkSp x us)

wkNfHom x (lam f) = lam (wkNfHom (vs x) f)
wkNfHom x (ne f) = ne (wkNeHom x f)

wkNeHom {Γ} x {S ◃ P ◃ R} {T ◃ Q ◃ L} (f ◃ g ◃ h) = f′ ◃ g′ ◃ h′
  where
  open Ne (wkNe x (S ◃ P ◃ R)) renaming (S to S′; P to P′; R to R′)
  open Ne (wkNe x (T ◃ Q ◃ L)) renaming (S to T′; P to Q′; R to L′)

  f′ : S′ → T′
  f′ = f

  g′ : (y : Var Γ A) (s′ : S′) → Q′ y (f′ s′) → P′ y s′
  g′ y s′ q′ with eq x y
  g′ .(wkv x y′) s′ q′ | diff .x y′ = g y′ s′ q′

  h′ : (y : Var Γ A) (s′ : S′) (q′ : Q′ y (f′ s′)) → SpHom Γ (R′ y s′ (g′ y s′ q′)) (L′ y (f′ s′) q′)
  h′ y s′ q′ with eq x y
  h′ .(wkv x y′) s′ q′ | diff .x y′ = wkSpHom x (h y′ s′ q′)

wkSpHom x ε = ε
wkSpHom x (f , fs) = wkNfHom x f , wkSpHom x fs


_[_:=_]Hom : NfHom Γ t u → (x : Var Γ A) (w : Nf (Γ - x) A) → NfHom (Γ - x) (t [ x := w ]) (u [ x := w ])

_<_:=_>Hom : SpHom Γ ts us → (x : Var Γ A) (w : Nf (Γ - x) A) → SpHom (Γ - x) (ts < x := w >) (us < x := w >)

(lam f) [ x := w ]Hom = lam (f [ vs x := wkNf vz w ]Hom)
ne {Γ} {S ◃ P ◃ R} {T ◃ Q ◃ L} (f ◃ g ◃ h) [ x := w ]Hom = ne (f′ ◃ g′ ◃ h′)
  where
  S′ : Set
  S′ = S

  P′ : Var (Γ - x) A → S → Set
  P′ y s = P (wkv x y) s

  R′ : (y : Var (Γ - x) A) (s : S) → P′ y s → Sp (Γ - x) A *
  R′ y s p = R (wkv x y) s p < x := w >

  T′ : Set
  T′ = T

  Q′ : Var (Γ - x) A → T → Set
  Q′ y t = Q (wkv x y) t

  L′ : (y : Var (Γ - x) A) (t : T) → Q′ y t → Sp (Γ - x) A *
  L′ y t q = L (wkv x y) t q < x := w >
  
  f′ : S → T
  f′ = f

  g′ : (y : Var (Γ - x) A) (s′ : S′) → Q′ y (f′ s′) → P′ y s′
  g′ y s′ x = g (wkv _ y) s′ x

  h′ : (y : Var (Γ - x) A) (s′ : S′) (q′ : Q′ y (f′ s′)) → SpHom (Γ - x) (R′ y s′ (g′ y s′ q′)) (L′ y (f′ s′) q′)
  h′ y s′ q′ = h (wkv x y) s′ q′ < x := w >Hom

ε < x := w >Hom = ε
(f , fs) < x := w >Hom = (f [ x := w ]Hom) , (fs < x := w >Hom)

-- napp₁ : (t : Nf Γ (A ⇒ B)) {u w : Nf Γ A} → NfHom Γ u w → NfHom Γ (napp t u) (napp t w)
-- napp₁ (lam t) f = {!!}

{-
!nf : (t : Nf Γ A) → NfHom Γ t ⊤nf
!nf (lam t) = lam (!nf t)
!nf (ne (S ◃ P ◃ R)) = ne ((λ _ → tt) ◃ (λ x s ()) ◃ λ x s ())

¿nf : (t : Nf Γ A) → NfHom Γ ⊥nf t
¿nf (lam t) = lam (¿nf t)
¿nf (ne (S ◃ P ◃ R)) = ne ((λ ()) ◃ (λ x ()) ◃ λ x ())

π₁nf : (t u : Nf Γ A) → NfHom Γ (t ×nf u) t
π₁nf (lam t) (lam u) = lam (π₁nf t u)
π₁nf {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (f ◃ g ◃ h)
  where
  f : S × T → S
  f (s , t) = s

  g : (x : Var Γ A) (st : S × T) → P x (f st) → P x (st .proj₁) ⊎ Q x (st .proj₂)
  g x (s , t) p = inj₁ p

  h : (x : Var Γ A) (st : S × T) (q : P x (f st)) → SpHom Γ (R x (f st) q) (R x (f st) q)
  h x (s , t) q = ε

i₁nf : (t u : Nf Γ A) → NfHom Γ t (t ⊎nf u)
i₁nf (lam t) (lam u) = lam (i₁nf t u)
i₁nf {Γ} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (f ◃ g ◃ h)
  where
  f : S → S ⊎ T
  f s = inj₁ s

  g : (x : Var Γ A) (s : S) → P x s → P x s
  g x s p = p

  h : (x : Var Γ A) (s : S) (q : P x s) → SpHom Γ (R x s (g x s q)) (R x s q)
  h x s q = ε

<_,_>nf : NfHom Γ t u → NfHom Γ t w → NfHom Γ t (u ×nf w)
< lam tu , lam tv >nf = lam < tu , tv >nf
<_,_>nf {Γ} {B} (ne (f₁ ◃ g₁ ◃ h₁)) (ne (f₂ ◃ g₂ ◃ h₂)) = ne (ff ◃ gg ◃ hh)
  where
  ff : _
  ff = < f₁ , f₂ >

  gg : (x : Var Γ A) (s : _) → _
  gg x s (inj₁ q₁) = g₁ x s q₁
  gg x s (inj₂ q₂) = g₂ x s q₂

  hh : (x : Var Γ A) (s : _) (q : _) → _
  hh x s (inj₁ q₁) = h₁ x s q₁
  hh x s (inj₂ q₂) = h₂ x s q₂

[_,_]nf : NfHom Γ t w → NfHom Γ u w → NfHom Γ (t ⊎nf u) w
[ lam tv , lam uv ]nf = lam [ tv , uv ]nf
[_,_]nf {Γ} {B} (ne (f₁ ◃ g₁ ◃ h₁)) (ne (f₂ ◃ g₂ ◃ h₂)) = ne (ff ◃ gg ◃ hh)
  where
  ff : _
  ff = [ f₁ , f₂ ]

  gg : (x : Var Γ A) (s : _) → _
  gg x (inj₁ s₁) q₁ = g₁ x s₁ q₁
  gg x (inj₂ s₂) q₂ = g₂ x s₂ q₂

  hh : (x : Var Γ A) (s : _) (q : _) → _
  hh x (inj₁ s₁) q₁ = h₁ x s₁ q₁
  hh x (inj₂ s₂) q₂ = h₂ x s₂ q₂
-}

{- Semantics -}

{- One Interpreation -}

⟦_⟧k : Kind → Set₁
⟦ * ⟧k = Set
⟦ A ⇒ B ⟧k = ⟦ A ⟧k → ⟦ B ⟧k

⟦_⟧c : Con → Set₁
⟦ • ⟧c = Lift (suc zero) ⊤
⟦ Γ ▹ A ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧k

⟦_⟧v : Var Γ A → ⟦ Γ ⟧c → ⟦ A ⟧k
⟦ vz ⟧v (as , a) = a
⟦ vs x ⟧v (as , a) = ⟦ x ⟧v as

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧c → ⟦ A ⟧k

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧c → Set

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧c → ⟦ A ⟧k → ⟦ B ⟧k

⟦ lam t ⟧nf as a = ⟦ t ⟧nf (as , a)
⟦ ne spr ⟧nf as = ⟦ spr ⟧ne as

⟦_⟧ne {Γ} (S ◃ P ◃ R) as =
  Σ[ s ∈ S ] ({A : Kind} (x : Var Γ A) (p : P x s)
  → ⟦ R x s p ⟧sp as (⟦ x ⟧v as))

⟦ ε ⟧sp as a = a
⟦ t , ts ⟧sp as f = ⟦ ts ⟧sp as (f (⟦ t ⟧nf as))

⟦_⟧ : HCont A → ⟦ A ⟧k
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{- Λ Terms -}

data Ty : Con → Kind → Set₁ where
  var : Var Γ A → Ty Γ A
  lam : Ty (Γ ▹ A) B → Ty Γ (A ⇒ B)
  app : Ty Γ (A ⇒ B) → Ty Γ A → Ty Γ B
  Πtm : (I : Set) → (I → Ty Γ A) → Ty Γ A
  Σtm : (I : Set) → (I → Ty Γ A) → Ty Γ A

{- Normalization -}

nf : Ty Γ A → Nf Γ A
nf (var x) = nvar x
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)
nf (Πtm I f) = Πnf I (nf ∘ f)
nf (Σtm I f) = Σnf I (nf ∘ f)

{- Embedding -}

emb : Nf Γ A → Ty Γ A

embSp : Sp Γ A B → Ty Γ A → Ty Γ B

emb (lam t) = lam (emb t)
emb {Γ} {A} (ne (S ◃ P ◃ R))
  = Σtm S (λ s → Πtm (Var Γ A) (λ x → Πtm (P x s) (λ p → embSp (R x s p) (var x))))

embSp ε u = u
embSp (t , ts) u = embSp ts (app u (emb t))
