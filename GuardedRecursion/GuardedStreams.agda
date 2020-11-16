{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with guarded streams of natural numbers
--
-- Note that the option omega-in-omega is used to
-- make the type Stream an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.GuardedStreams where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec.Base hiding ([_]; _⊛_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
open import Level renaming (zero to lzero; suc to lsuc)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import GuardedRecursion.Later
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

private
  variable
    Γ Δ : Ctx ω ℓ


--------------------------------------------------
-- Some basic operations and proofs regarding vectors

first-≤ : ∀ {m n} {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n as = []
first-≤ (s≤s ineq) (a ∷ as) = a ∷ first-≤ ineq as

first-≤-refl : ∀ {n} {A : Set ℓ} {as : Vec A n} → first-≤ (≤-refl) as ≡ as
first-≤-refl {as = []} = refl
first-≤-refl {as = a ∷ as} = cong (a ∷_) first-≤-refl

first-≤-trans : ∀ {k m n} {A : Set ℓ} (k≤m : k ≤ m) (m≤n : m ≤ n) (as : Vec A n) →
                first-≤ (≤-trans k≤m m≤n) as ≡ first-≤ k≤m (first-≤ m≤n as)
first-≤-trans z≤n m≤n as = refl
first-≤-trans (s≤s k≤m) (s≤s m≤n) (a ∷ as) = cong (a ∷_) (first-≤-trans k≤m m≤n as)

first-≤-head : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               head as ≡ head (first-≤ (s≤s m≤n) as)
first-≤-head m≤n (a ∷ as) = refl

first-≤-tail : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               first-≤ m≤n (tail as) ≡ tail (first-≤ (s≤s m≤n) as)
first-≤-tail m≤n (a ∷ as) = refl


--------------------------------------------------
-- Definition of guarded streams.

Stream : Ty Γ 0ℓ
type Stream n _ = Vec ℕ (suc n)
morph Stream m≤n _ = first-≤ (s≤s m≤n)
morph-cong Stream refl = refl
morph-id Stream _ = first-≤-refl
morph-comp Stream k≤m m≤n _ _ = first-≤-trans (s≤s k≤m) (s≤s m≤n)

str-head : Tm Γ Stream → Tm Γ Nat'
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eγ =
  begin
    head (s ⟨ n , γ ⟩')
  ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
    head (Stream {Γ = Γ} ⟪ m≤n , eγ ⟫ (s ⟨ n , γ ⟩'))
  ≡⟨ cong head (naturality s m≤n eγ) ⟩
    head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning

str-tail : Tm Γ Stream → Tm Γ (▻' Stream)
term (str-tail s) zero _ = tt
term (str-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (str-tail s) z≤n _ = refl
naturality (str-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) {γ}{γ'} eγ =
  begin
    first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
  ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
    tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
  ≡⟨ cong tail (naturality s (s≤s m≤n) eγ) ⟩
    tail (s ⟨ suc m , γ' ⟩') ∎
  where open ≡-Reasoning

str-cons : Tm Γ (Nat' ⊠ (▻' Stream)) → Tm Γ Stream
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons t) {zero} {suc n} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eγ =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eγ)) (naturality (snd t) (s≤s m≤n) eγ)

stream-natural : (σ : Δ ⇒ Γ) → Stream [ σ ] ≅ᵗʸ Stream
func (from (stream-natural σ)) = id
naturality (from (stream-natural σ)) _ = refl
func (to (stream-natural σ)) = id
naturality (to (stream-natural σ)) _ = refl
eq (isoˡ (stream-natural σ)) _ = refl
eq (isoʳ (stream-natural σ)) _ = refl


--------------------------------------------------
-- Declarations needed for the naturality solver
-- This shows that it is easy to extend the solver to work with custom types
-- and type operations (even the ones that are only definable in a particular
-- base category).

instance
  stream-nul : IsNullaryNatural Stream
  natural-nul {{stream-nul}} = stream-natural

  ▻'-un : IsUnaryNatural ▻'
  natural-un {{▻'-un}} = ▻'-natural
  cong-un {{▻'-un}} = ▻'-cong

  ◄-functor : IsCtxFunctor ◄
  ctx-map {{◄-functor}} = ◄-subst
  ctx-map-id {{◄-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-functor}} = ◄-subst-⊚

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong


--------------------------------------------------
-- Some operations on guarded streams
--
-- Most functions are an implementation of the examples on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The guarded lambda-calculus: Programming and reasoning with guarded recursion for coinductive types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.

str-snd : Tm Γ Stream → Tm Γ (▻' Nat')
str-snd s = next' (lamι Stream (str-head (varι 0))) ⊛' str-tail s

str-thrd : Tm Γ Stream → Tm Γ (▻' (▻' Nat'))
str-thrd s = next' (lamι Stream (str-snd (varι 0))) ⊛' str-tail s

zeros : Tm Γ Stream
zeros = löbι Stream
             (str-cons (pair zero' (varι 0)))

private
  module _ {Γ : Ctx ω ℓ} where
    zeros-test : str-head {Γ = Γ} zeros ≅ᵗᵐ zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : str-snd {Γ = Γ} zeros ≅ᵗᵐ next' zero'
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

str-map : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Stream ⇛ Stream)
str-map f = löbι (Stream ⇛ Stream) (
                 lamι Stream (
                      str-cons (pair (app (↑ι⟨ 2 ⟩ f) (str-head (varι 0)))
                                     (varι 1 ⊛' str-tail (varι 0)))))

iterate : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ Stream)
iterate f = löbι (Nat' ⇛ Stream) (
                 lamι Nat' (
                      str-cons (pair (varι 0)
                                     (varι 1 ⊛' next' (app (↑ι⟨ 2 ⟩ f) (varι 0))))))

iterate' : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ Stream)
iterate' f = lamι Nat' (
                  löbι Stream (
                       str-cons (pair (varι 1)
                                      (next' (↑ι⟨ 2 ⟩ str-map f) ⊛' varι 0))))

suc-func : Tm Γ (Nat' ⇛ Nat')
suc-func = discr-func suc

nats : Tm Γ Stream
nats = app (iterate' suc-func) zero'

private
  module _ {Γ : Ctx ω ℓ} where
    nats-test : str-head {Γ = Γ} nats ≅ᵗᵐ zero'
    eq nats-test {x = zero}  _ = refl
    eq nats-test {x = suc n} _ = refl

    nats-test2 : str-snd {Γ = Γ} nats ≅ᵗᵐ next' (suc' zero')
    eq nats-test2 {x = zero}        _ = refl
    eq nats-test2 {x = suc zero}    _ = refl
    eq nats-test2 {x = suc (suc n)} _ = refl

    nats-test3 : str-thrd {Γ = Γ} nats ≅ᵗᵐ next' (next' (suc' (suc' zero')))
    eq nats-test3 {x = zero}              _ = refl
    eq nats-test3 {x = suc zero}          _ = refl
    eq nats-test3 {x = suc (suc zero)}    _ = refl
    eq nats-test3 {x = suc (suc (suc n))} _ = refl

    map-test : str-head {Γ = Γ} (app (str-map suc-func) zeros) ≅ᵗᵐ discr 1
    eq map-test {x = zero}  _ = refl
    eq map-test {x = suc x} _ = refl

    map-test2 : str-thrd {Γ = Γ} (app (str-map suc-func) (app (str-map suc-func) nats)) ≅ᵗᵐ next' (next' (discr 4))
    eq map-test2 {x = zero}              _ = refl
    eq map-test2 {x = suc zero}          _ = refl
    eq map-test2 {x = suc (suc zero)}    _ = refl
    eq map-test2 {x = suc (suc (suc n))} _ = refl

interleave : Tm Γ (Stream ⇛ ▻' Stream ⇛ Stream)
interleave = löbι (Stream ⇛ ▻' Stream ⇛ Stream)
                  (lamι Stream
                        (lamι (▻' Stream)
                              (str-cons (pair (str-head (varι 1))
                                              (varι 2 ⊛' varι 0 ⊛' next' (str-tail (varι 1)))))))

toggle : Tm Γ Stream
toggle = löbι Stream
              (str-cons (pair (suc' zero')
                              (next' (str-cons (pair zero' (varι 0))))))

paperfolds : Tm Γ Stream
paperfolds = löbι Stream (app (app interleave toggle) (varι 0))

module _ (T-op : NullaryTypeOp {C = ω} ℓ) {{_ : IsNullaryNatural T-op}} where
  T : Ty Γ ℓ
  T = ⟦ nul T-op ⟧exp

{-
  initial : Tm Γ ((Nat' ⊠ ▻' T ⇛ T) ⇛ Stream ⇛ T)
  initial = löbι ((Nat' ⊠ ▻' T ⇛ T) ⇛ Stream ⇛ T)
                 (lamι (Nat' ⊠ ▻' T ⇛ T)
                       (lamι Stream
                             (app (varι 1) (pair (str-head (varι 0))
                                                 (varι 2 ⊛' next' (varι 1) ⊛' str-tail (varι 0))))))

  final : Tm Γ ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ Stream)
  final = löbι ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ Stream)
               (lamι (T ⇛ Nat' ⊠ ▻' T)
                     (lamι T let x = app (varι 1) (varι 0)
                             in str-cons (pair (fst x)
                                               (varι 2 ⊛' next' (varι 1) ⊛' snd x))))
-}

-- This is an implementation of an example on page 3 of the paper
--   Robert Atkey, and Conor McBride.
--   Productive Coprogramming with Guarded Recursion.
--   ICFP 2013.
mergef : Tm Γ (Nat' ⇛ Nat' ⇛ ▻' Stream ⇛ Stream) → Tm Γ (Stream ⇛ Stream ⇛ Stream)
mergef f = löbι (Stream ⇛ Stream ⇛ Stream) (
                lamι Stream (
                     lamι Stream (
                          let xs = varι 1
                              ys = varι 0
                          in
                            app (app (app (↑ι⟨ 3 ⟩ f)
                                          (str-head xs))
                                     (str-head ys))
                                (varι 2 ⊛' str-tail xs ⊛' str-tail ys))))

-- Examples that were not taken from a paper.
str-zipWith : Tm Γ (Nat' ⇛ Nat' ⇛ Nat') → Tm Γ (Stream ⇛ Stream ⇛ Stream)
str-zipWith f = mergef (lamι Nat' (
                             lamι Nat' (
                                  lamι (▻' Stream) (
                                       str-cons (pair (app (app (↑ι⟨ 3 ⟩ f) (varι 2)) (varι 1))
                                                      (varι 0))))))

nat-sum : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nat-elim (Nat' ⇛ Nat')
                   (lamι Nat' (varι 0))
                   (lamι (Nat' ⇛ Nat') (
                         lamι Nat' (suc' (app (varι 1) (varι 0)))))

str-cons' : Tm Γ ((Nat' ⊠ ▻' Stream) ⇛ Stream)
str-cons' = lamι (Nat' ⊠ ▻' Stream) (str-cons (pair (fst (varι 0)) (snd (varι 0))))

str-tail' : Tm Γ (Stream ⇛ ▻' Stream)
str-tail' = lamι Stream (str-tail (varι 0))

pair' : Tm Γ (Nat' ⇛ ▻' Stream ⇛ Nat' ⊠ ▻' Stream)
pair' = lamι Nat' (lamι (▻' Stream) (pair (varι 1) (varι 0)))

fibs : Tm Γ Stream
fibs = löbι Stream (
            str-cons (pair (suc' zero')
                           (next' str-cons' ⊛' (next' pair'
                                                ⊛' next' (suc' zero')
                                                ⊛' (next' f ⊛' next' (varι 0) ⊛' (next' str-tail' ⊛' varι 0))))))
  where
    f : Tm Γ (▻' Stream ⇛ ▻' Stream ⇛ ▻' Stream)
    f = lamι (▻' Stream) (lamι (▻' Stream) (next' (str-zipWith nat-sum) ⊛' varι 1 ⊛' varι 0))

private
  module _ where
    fibs-test : str-thrd {Γ = Γ} fibs ≅ᵗᵐ next' (next' (discr 2))
    eq fibs-test {x = zero} _ = refl
    eq fibs-test {x = suc zero} _ = refl
    eq fibs-test {x = suc (suc zero)} _ = refl
    eq fibs-test {x = suc (suc (suc x))} _ = refl
