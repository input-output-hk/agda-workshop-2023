---
layout: default
title: "Notes from the 2023 IO Agda Workshop"
date: "2023-06-02"
author: "James Chapman"
---

```agda
{-# OPTIONS --type-in-type #-}

module UU where
```

# Notes from the 2023 IO Agda Workshop

**Parma 23 May -- 2 June 2023**


## Imports

```agda
open import Data.Bool
open import Data.Vec using (Vec;zipWith) public
open import Data.Nat using (ℕ;zero;suc;_+_) public
open import Data.Unit using (⊤) public
open import Data.Product using (_×_;_,_;proj₁;proj₂;_,′_) public
open import Data.Nat.Properties public
open import Relation.Nullary.Decidable public
open import Relation.Binary.PropositionalEquality public
open import Data.Maybe using (Maybe;just;nothing) public
open import Data.Char using (Char) public
open import Function public
```

-----------

## Monoids

```agda
record Monoid (X : Set) : Set where
  field  ε      : X
         _·_    : X → X → X
         idl    : ∀ x → ε · x ≡ x
         idr    : ∀ x → x · ε ≡ x
         assoc  : ∀ x y z → (x · y) · z ≡ x · (y · z)
```


**Example** (`Nat`)

```agda
NatMonoid : Monoid ℕ
NatMonoid = record {
  ε = 0 ;
  _·_ = _+_ ;
  idl = +-identityˡ;
  idr = +-identityʳ ;
  assoc = +-assoc }
```

**Example** (`List`)

```agda
data List (X : Set) : Set where
  [] : List X
  _∷_ : X → List X → List X

infixr 5 _∷_

_++_ : ∀{X} → List X  → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_
```


**EXERCISE 1**. Prove that lists form a monoid with `_++_` and `[]`.


---


## Monads


```agda
record Monad (M : Set → Set) : Set where
  field  return : ∀{A} → A → M A
         ext   : {A B : Set} → (A → M B) → M A → M B
         law1   : ∀{A B}(f : A → M B)(a : A) → ext f (return a) ≡ f a
         law2   : ∀{A}(ma : M A) → ext return ma ≡ ma
         law3   : ∀{A B C}(f : A → M B)(g : B → M C)(mx : M A)
                  → ext g (ext f mx) ≡ ext (ext g ∘ f) mx

  _>>=_ : ∀{A B} → M A → (A → M B) →  M B
  ma >>= f = ext f ma

  _>>_ : ∀{A B} → M A → M B → M B
  ma >> mb = ma >>= const mb

  fmap : ∀{A B} → (A → B) → M A → M B
  fmap f as = as >>= (return ∘ f)
```

**EXERCISE 1b** Define `join : ∀{A} → M (M A) → M A` 


### Monad Examples

```agda
--open Monad {{...}} public
open Monad ⦃...⦄ public

mext : ∀{X Y} → (X → Maybe Y) → Maybe X → Maybe Y
mext f nothing   = nothing
mext f (just x)  = f x

mlaw1 : ∀{A B}(f : A → Maybe B)(a : A) → mext f (just a) ≡ f a
mlaw1 f a = refl

mlaw2 : ∀{A}(ma : Maybe A) → mext just ma ≡ ma
mlaw2 nothing = refl
mlaw2 (just x) = refl

mlaw3 : ∀{A B C}(f : A → Maybe B)(g : B → Maybe C)(mx : Maybe A)
        → mext g (mext f mx) ≡ mext (mext g ∘ f) mx
mlaw3 f g nothing = refl
mlaw3 f g (just x) = refl

instance
  MaybeMonad : Monad Maybe
  MaybeMonad = record {
    return = just ;
    ext = mext ;
    law1 = mlaw1 ;
    law2 = mlaw2 ;
    law3 = mlaw3 }
```


**EXERCISE 2** Define `return`, `join` and `ext` for `List`; prove that lists form a monad.

**EXERCISE 2b** Show that `¬ ¬` and `Dec` are monads 

---

## Modelling IO expressions as a free monad

a syntax tree of commands

```agda
data IOᵗᵗ : Set → Set where
  putCharᵗᵗ : ∀{A} → Char → IOᵗᵗ A → IOᵗᵗ A
  getCharᵗᵗ : ∀{A} → (Char → IOᵗᵗ A) → IOᵗᵗ A
  returnᵗᵗ : ∀{A} → A → IOᵗᵗ A
```

(draw picture)

```agda
exIO : IOᵗᵗ ⊤
exIO = getCharᵗᵗ (λ x → putCharᵗᵗ x (returnᵗᵗ _))

extIO : ∀{A B} → (A → IOᵗᵗ B) → IOᵗᵗ A → IOᵗᵗ B
extIO f (putCharᵗᵗ x c)  = putCharᵗᵗ x (extIO f c)
extIO f (getCharᵗᵗ g)    = getCharᵗᵗ λ x → extIO f (g x)
extIO f (returnᵗᵗ x)    = f x

postulate
  iolaw1   : ∀{A B}(f : A → IOᵗᵗ B)(a : A) → extIO f (returnᵗᵗ a) ≡ f a
  iolaw2   : ∀{A}(ma : IOᵗᵗ A) → extIO returnᵗᵗ ma ≡ ma
  iolaw3   : ∀{A B C}(f : A → IOᵗᵗ B)(g : B → IOᵗᵗ C)(mx : IOᵗᵗ A)
                  → extIO g (extIO f mx) ≡ extIO (extIO g ∘ f) mx
```

**EXERCISE 3**. Prove the above laws.

*Hint*. Postulate extensionality :

    ∀{A B}(f g : A → B) → (∀ a → f a ≡ g a) → f ≡ g

<!--
postulate law1IO : {A B : Set} (f : A → IOᵗᵗ B) (a : A) → f a ≡ f a
postulate law2IO : {A : Set} (ma : IOᵗᵗ A) → extIO returnᵗᵗ ma ≡ ma
postulate law3IO :  {A B C : Set} (f : A → IOᵗᵗ B) (g : B → IOᵗᵗ C) (mx : IOᵗᵗ A)  →       extIO g (extIO f mx) ≡ extIO (λ x → extIO g (f x)) mx
-->

```agda
instance
  IOᵗᵗMonad : Monad IOᵗᵗ
  IOᵗᵗMonad = record {
    return = returnᵗᵗ;
    ext = extIO ;
    law1 = iolaw1 ;
    law2 = iolaw2 ;
    law3 = iolaw3 }

putChar : Char → IOᵗᵗ ⊤
putChar s = putCharᵗᵗ s (returnᵗᵗ _)

getChar : IOᵗᵗ Char
getChar = getCharᵗᵗ returnᵗᵗ
```

```agda
import IO.Primitive as Prim
postulate putCharP : Char → Prim.IO ⊤
postulate getCharP : Prim.IO Char

eval : ∀{a} → IOᵗᵗ a  → Prim.IO a
eval (putCharᵗᵗ s c) = putCharP s Prim.>>= const (eval c)
eval (getCharᵗᵗ c)   = getCharP Prim.>>= eval ∘ c
eval (returnᵗᵗ a)   = Prim.return a

echo : ℕ → IOᵗᵗ ⊤
echo zero = returnᵗᵗ _
echo (suc n) = do
  c ← getChar
  putChar c
  echo n
```

one could give a pure semantics as a fucntion from lists to lists
or streams to streams, or steams to `output` or could compile to Haskell IO.
one could also consider whether two programs were equivalent

---

## Cryptography

```agda
BitVec : ℕ → Set
BitVec n = Vec Bool n

all-zero : ∀{n} → Vec Bool n
all-zero {zero}   = Vec.[]
all-zero {suc n}  = false Vec.∷ all-zero

all-one : ∀{n} → Vec Bool n
all-one {zero}   = Vec.[]
all-one {suc n}  = true Vec.∷ all-one

data Crypto (ST : Set) : Set → Set where
  coin       : Crypto ST Bool
  uniform    : ∀ n → Crypto ST (BitVec n)
  set-state  : ST → Crypto ST ⊤
  get-state  : Crypto ST ST
  returnC    : ∀{a : Set} → a → Crypto ST a
  _>>=C_     : ∀{a b : Set} → Crypto ST a → (a → Crypto ST b) → Crypto ST b

open Crypto

extC : ∀{ST a b : Set} → (a → Crypto ST b) → Crypto ST a → Crypto ST b
extC f c = c >>=C f

-- convert to Wouter style
-- can define a bind that uses >>=C and shuffles computations to the
-- right and then the laws will hold

postulate
  claw1   : ∀{ST A B}(f : A → Crypto ST B)(a : A) → extC f (returnC a) ≡ f a
  claw2   : ∀{ST A}(ma : Crypto ST A) → extC returnC ma ≡ ma
  claw3   : ∀{ST A B C}(f : A → Crypto ST B)(g : B → Crypto ST C)
            → (mx : Crypto ST A)
            → extC g (extC f mx) ≡ extC (extC g ∘ f) mx

instance
  CryptoMonad : ∀{ST} → Monad (Crypto ST)
  CryptoMonad = record {
    return = returnC ;
    ext = λ f x → x >>=C f ;
    law1 = claw1 ;
    law2 = claw2 ;
    law3 = claw3 }

K = BitVec 256
PT = BitVec 256
CT = BitVec 256

-- newtypes ^ !

record EncScheme : Set₁ where
  field  keygen   : ∀{ST} → Crypto ST K
         encrypt  : ∀{ST} → K → PT → Crypto ST CT -- not why this isn't pure?
open EncScheme

record Adversary (ST : Set) : Set where
  field  A₁ : Crypto ST (PT × PT)
         A₂ : CT → Crypto ST Bool
open Adversary


-- why is it called this?
IND-EAV : ∀{ST} → EncScheme → Adversary ST → Crypto ST Bool
IND-EAV enc adv = do
  m₁ , m₂ ← A₁ adv
  k ← keygen enc
  b ← coin
  let pt = if b then m₁ else m₂
  ct ← encrypt enc k pt
  b' ← A₂ adv ct
  return (isYes (b Data.Bool.≟ b'))

-- why is there no proof?
```

---

## OTP

```agda
_⊗_ : ∀{n} → BitVec n → BitVec n → BitVec n
xs ⊗ ys = zipWith _xor_ xs ys

OTP : EncScheme
keygen OTP = uniform 256
encrypt OTP key msg = return (key ⊗ msg)
```

could be defined from game above

```agda
IND-EAV-OTP₁ : ∀{ST} → Adversary ST → Crypto ST Bool
IND-EAV-OTP₁ adv = do
  m₁ , m₂ ← A₁ adv
  k ← uniform 256
  b ← coin
  let pt = if b then m₁ else m₂
  ct ← return (k ⊗ pt)
  b' ← A₂ adv ct
  return (isYes (b Data.Bool.≟ b'))

IND-EAV-OTP₂ : ∀{ST} → Adversary ST → Crypto ST Bool
IND-EAV-OTP₂ adv = do
  m₁ , m₂ ← A₁ adv
  b ← coin
  let pt = if b then m₁ else m₂
  ct ← fmap (λ k → k ⊗ pt) (uniform 256)
  b' ← A₂ adv ct
  return (isYes (b Data.Bool.≟ b'))

IND-EAV-OTP₃ : ∀{ST} → Adversary ST → Crypto ST Bool
IND-EAV-OTP₃ adv = do
  m₁ , m₂ ← A₁ adv
  b ← coin
  ct ← uniform 256
  b' ← A₂ adv ct
  return (isYes (b Data.Bool.≟ b'))

IND-EAV-OTP₄ : ∀{ST} → Adversary ST → Crypto ST Bool
IND-EAV-OTP₄ adv = do
  m₁ , m₂ ← A₁ adv
  ct ← uniform 256
  b' ← A₂ adv ct
  fmap (λ b → isYes (b Data.Bool.≟ b')) coin

IND-EAV-OTP₅ : ∀{ST} → Adversary ST → Crypto ST Bool
IND-EAV-OTP₅ adv = do
  m₁ , m₂ ← A₁ adv
  ct ← uniform 256
  b' ← A₂ adv ct
  coin
```

---

## Oracles

```agda
OracleState = K
OracleArg = PT
OracleResult = CT

postulate
  init-oracle : ∀{ST} → OracleState → Crypto ST ⊤
  call-oracle : ∀{ST} → OracleArg → Crypto ST OracleResult
```

why is call-oracle not part of the adversary's operations?

(this should really be added to the Crypto datatype)

```agda
IND-CPA : ∀{ST} → EncScheme → Adversary ST → Crypto ST Bool
IND-CPA enc adv = do
  m₁ , m₂ ← A₁ adv
  k ← keygen enc
  init-oracle k
  b ← coin
  let pt = if b then m₁ else m₂
  ct ← encrypt enc k pt
  b' ← A₂ adv ct
  return (isYes (b Data.Bool.≟ b'))

init-oracle-impl : K → Crypto K ⊤
init-oracle-impl = set-state


-- enc arg not given on page 9
call-oracle-impl : EncScheme → K → Crypto K CT
call-oracle-impl enc pt = do
  k ← get-state
  encrypt enc k pt
```

---

## OTP Again

```agda
postulate _=bv=_ : BitVec 256 → BitVec 256 → Bool

IND-CPA-OTP-ADV : Adversary ⊤
A₁ IND-CPA-OTP-ADV = return (all-zero , all-one)
A₂ IND-CPA-OTP-ADV ct = do
  r ← call-oracle all-zero
  return (ct =bv= r)

IND-CPA-OTP1 : Crypto K Bool
IND-CPA-OTP1 = do
  let m1 , m2 = all-zero ,′ all-one
  k ← uniform 256
  init-oracle-impl k
  b ← coin
  let pt = if b then m1 else m2
  let ct = k ⊗ pt
  k' ← get-state  -- oracle...
  let b' = ct =bv= (k' ⊗ all-zero)
  return (isYes (b Data.Bool.≟ b'))

IND-CPA-OTP₂ : Crypto (⊤ × K) Bool
IND-CPA-OTP₂ = do
  k ← uniform 256
  b ← coin
  let pt = if b then all-zero else all-one
  let ct = k ⊗ pt
  let b' = ct =bv= (k ⊗ all-zero)
  return (isYes (b Data.Bool.≟ b'))

IND-CPA-OTP₃ : Crypto (⊤ × K) Bool
IND-CPA-OTP₃ = do
  k ← uniform 256
  b ← coin
  let pt = if b then all-zero else all-one
  let b' = (k ⊗ pt) =bv= (k ⊗ all-zero)
  return (isYes (b Data.Bool.≟ b'))

IND-CPA-OTP₄ : Crypto (⊤ × K) Bool
IND-CPA-OTP₄ = do
  k ← uniform 256
  b ← coin
  let pt = if b then all-zero else all-one
  let b' = pt =bv= all-zero
  return (isYes (b Data.Bool.≟ b'))
```

---

## Notes

modelling games as monadic computations
typechecked specs
generate pdf
model in agda/could give a semantics in agda/compile to Haskell
testing/model checking to find counterexamples? e.g., given the same inputs all indistinguisable games should yield the same result?
agda proofs of ε-indistinguisability
one work stream, our other workstream (formal methods/research) is to look at UC style proofs, but we our current focus to be too categoricially heavy for this workshop...

**EXERCISE 4**.  (idea) Implement counter example search in Haskell.

* `ε`-indistiungishibility

```agda
data _≡E_ : ∀{ST A} → Crypto ST A → Crypto ST A → Set where
  reflE : ∀{ST A}{c : Crypto ST A} → c ≡E c
  symE  : ∀{ST A}{c c' : Crypto ST A} → c ≡E c'
  transE : ∀{ST A}{c c' c'' : Crypto ST A} → c ≡E c' → c' ≡E c'' → c ≡E c''
  uniform⊕E : ∀{ST n pt} → fmap (λ k → k ⊗ pt) (uniform n) ≡E uniform {ST} n
```

