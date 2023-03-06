--------------------------------------------------
-- A presheaf model for an MSTT instance with the
-- purpose of reasoning about a restricted form of
-- unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.Model where

open import Data.Empty
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Function using (id; _∘_)
open import Level using (0ℓ)
open import Relation.Unary hiding (_⇒_; _⟨→⟩_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Model.CwF-Structure.Reflection.SubstitutionSequence
open import Extraction

open BaseCategory ¶

private
  variable
    Γ : Ctx ¶


--------------------------------------------------
-- Constructing a semantic closed type over any context 
-- on the base category ¶ using an Agda type and a predicate

-- Creates a semantic type in the empty context 
PrimFromPred : (A : Set) (P : Pred A 0ℓ) → Ty {C = ¶} ◇
PrimFromPred A P ⟨ left ,  _ ⟩ = A
PrimFromPred A P ⟨ relation , _ ⟩ = Σ[ a ∈ A ] a ∈ P
  {-
    `a ∈ P` = `P a`

    the dependent pair type inhabited by terms whose 
      - first components are terms of type A that satisfy predicate P and 
      - second components are corresponding proofs
  -}
_⟪_,_⟫_ (PrimFromPred A P) left-id  _ = id
_⟪_,_⟫_ (PrimFromPred A P) relation-id _ = id
_⟪_,_⟫_ (PrimFromPred A P) left-rel  _ = proj₁
  -- Σ[ a ∈ A ] a ∈ P → A
ty-cong (PrimFromPred A P) refl {eγ = refl}{eγ' = refl} = refl
ty-id (PrimFromPred A P) {x = left}  = refl
ty-id (PrimFromPred A P) {x = relation} = refl
ty-comp (PrimFromPred A P) {f = left-id}     {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromPred A P) {f = relation-id} {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromPred A P) {f = left-rel}  {g = relation-id} = refl

-- Creates a semantic closed type
FromPred : (A : Set) (P : Pred A 0ℓ) → ClosedTy ¶
FromPred A P {Γ = Γ} = PrimFromPred A P [ !◇ Γ ]
  {-
      FromPred A P {Γ = Γ} ⟨ left , _ ∈ Γ ⟨ left ⟩ ⟩
    = PrimFromPred A P ⟨ left , tt ⟩
    = A

      FromPred A P {Γ = Γ} ⟨ relation , _ ⟩
    = Σ[ a ∈ A ] a ∈ P
  -}

-- A proof of the natural property of any closed type `FromPred A P` over ¶
frompred-natural : {A : Set} {P : Pred A 0ℓ} → IsClosedNatural (FromPred A P)
closed-natural frompred-natural σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromPred _ _) (◇-terminal _ _ _)
  {-
    ty-subst-seq-cong (!◇ Γ ∷ σ ◼) (!◇ Δ ◼) (PrimFromPred A P) (◇-terminal Δ (fold (!◇ Γ ∷ σ ◼)) (fold (!◇ Δ ◼)))
    
    !◇ Γ ∷ σ ◼ , !◇ Δ ◼ : Δ ⇒⁺ ◇

    fold (!◇ Γ ∷ σ ◼) ≅ˢ fold (!◇ Δ ◼) = !◇ Γ ⊚ σ ≅ˢ !◇ Δ

      (PrimFromPred A P) ⟦ !◇ Γ ∷ σ ◼ ⟧ ≅ᵗʸ (PrimFromPred A P) ⟦ !◇ Δ ◼ 
    = ((PrimFromPred A P) [ !◇ Γ ]) [ σ ] ≅ᵗʸ (PrimFromPred A P) [ !◇ Δ ]
  -}
eq (from-eq (closed-id (frompred-natural {A} {P}))) {x = x} _ =
  ty-id (PrimFromPred A P) {x = x}
  {-
    closed-id : {Γ : Ctx ¶} → closed-natural (id-subst Γ) ≅ᵉ ty-subst-id (FromPred A P)
    = {Γ : Ctx ¶} → e1 ≅ᵉ e2 where
    e1 , e2 : (FromPred A P) [ id-subst Γ ] ≅ᵗʸ (FromPred A P)
    
    from-eq (closed-id (frompred-natural {A} {P})) : from e1 ≅ⁿ from e2
    _ = t : (FromPred A P) [ id-subst Γ ] ⟨ x , γ ⟩ 
        = (FromPred A P) ⟨ x , func (id-subst Γ) γ ⟩
        = (FromPred A P) ⟨ x , γ ⟩

    the output : func (from e1) t ≡ func (from e2) t
    where func (from e1) , func (from e2) : 
      ∀ {x} {γ} → (FromPred A P) [ id-subst Γ ] ⟨ x , γ ⟩ → (FromPred A P) ⟨ x , γ ⟩
    func (from e1) t , func (from e2) t : (FromPred A P) ⟨ x , γ ⟩
  -}
eq (from-eq (closed-⊚ (frompred-natural {A} {P}) σ τ)) {x = x} t =
  ty-cong-2-1 {x = x} (PrimFromPred A P) {f = hom-id} {g = hom-id} hom-idʳ
  {-
    ty-cong-2-1 {x = x} (PrimFromPred A P) {f = hom-id} {g = hom-id} hom-idʳ : (PrimFromPred A P) ⟪ hom-id {x} , refl ⟫ ((PrimFromPred A P) ⟪ hom-id {x} , refl ⟫ t) ≡ (PrimFromPred A P) ⟪ hom-id {x} , refl ⟫ t

    transᵗʸ : S ≅ᵗʸ T → T ≅ᵗʸ R → S ≅ᵗʸ R
    closed-⊚ (frompred-natural {A} {P}) σ τ : 
    
    (transᵗʸ (ty-subst-cong-ty τ (closed-natural σ)) (closed-natural τ)) ≅ᵉ (transᵗʸ (ty-subst-comp U σ τ) (closed-natural (σ ⊚ τ)))
    
    (FromPred A P) [ σ ] [ τ ] ≅ᵗʸ (FromPred A P)
    ≅ᵉ
    (FromPred A P) [ σ ] [ τ ] ≅ᵗʸ (FromPred A P)


  -}

-- closed-subst-eq : {Γ Δ : Ctx C} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
--                    transᵗʸ (ty-subst-cong-subst ε U) (closed-natural τ) ≅ᵉ 
--                    closed-natural σ
eq (from-eq (closed-subst-eq (frompred-natural {A} {P}) ε)) {x = x} t =
  ty-cong-2-1 {x = x} (PrimFromPred A P) {f = hom-id} {g = hom-id} hom-idʳ

-- Given two predicates over A and B respectively, constructs a predicate that a map f : A → B satisfies exactly when it respects predicates P and Q in the sense that if a term a : A satisfies P, then term f a : B satisfies Q.
infixr 0 _⟨→⟩_
_⟨→⟩_ : ∀ {a b} {A : Set a} {B : Set b} →
        Pred A 0ℓ → Pred B 0ℓ → Pred (A → B) _
(P ⟨→⟩ Q) f = ∀ {a} → P a → Q (f a)

-- for term construction and type inference
-- If a term satisfies a predicate P in Agda, then it is a term of type `FromPred A P` in context Γ.
from-pred : {A : Set} {P : Pred A 0ℓ} (a : A) → P a → Tm Γ (FromPred A P)
from-pred a p ⟨ left  , _ ⟩' = a
from-pred a p ⟨ relation , _ ⟩' = [ a , p ]
Tm.naturality (from-pred a p) left-id  _ = refl
Tm.naturality (from-pred a p) relation-id _ = refl
Tm.naturality (from-pred a p) left-rel  _ = refl

-- for term construction and type inference
from-pred1 : {A : Set} {P : Pred A 0ℓ}
            {B : Set} {Q : Pred B 0ℓ}
            (f : A → B) → (P ⟨→⟩ Q) f →
            Tm (Γ ,, FromPred A P) (FromPred B Q)
from-pred1 f h ⟨ left  , [ _ , a ] ⟩' = f a
  {-
    [ _ , a ] : (Γ ,, FromPred A P) ⟨ left ⟩
    = Σ[ _ ∈ ⟨ left ⟩ ] (FromPred A P ⟨ left , _ ⟩)
    = Σ[ _ ∈ ⟨ left ⟩ ] A 

    f a : B = (FromPred B Q) ⟨ left , _ ⟩
  -}
from-pred1 f h ⟨ relation , [ _ , [ a , p ] ] ⟩' = [ f a , h p ]
  {-
    [ _ , [ a , p ] ] : (Γ ,, FromPred A P) ⟨ relation ⟩
    = Σ[ _ ∈ Γ ⟨ relation ⟩ ] (FromPred A P ⟨ relation , _ ⟩)
    = Σ[ _ ∈ Γ ⟨ relation ⟩ ] Σ[ a ∈ A ] a ∈ P

    [ f a , h p ] : (FromPred B Q) ⟨ relation , [ _ , [ a , p ] ] ⟩
    = Σ[ b ∈ B ] b ∈ Q
  -}
Tm.naturality (from-pred1 f h) left-id refl = refl
Tm.naturality (from-pred1 f h) relation-id refl = refl
Tm.naturality (from-pred1 f h) left-rel refl = refl

-- for term construction and type inference
from-pred2 : {A : Set} {P : Pred A 0ℓ}
            {B : Set} {Q : Pred B 0ℓ}
            {C : Set} {R : Pred C 0ℓ}
            (f : A → B → C) → (P ⟨→⟩ Q ⟨→⟩ R) f →
            Tm (Γ ,, FromPred A P ,, FromPred B Q) (FromPred C R)
from-pred2 f h ⟨ left  , [ [ _ , a ] , b ] ⟩' = f a b 
  {-
    [ [ _ , a ] , b ] : (Γ ,, FromPred A P ,, FromPred B Q) ⟨ left ⟩
    = Σ[ _ ∈ (Γ ,, FromPred A P) ⟨ left ⟩ ] FromPred B Q ⟨ left , _ ⟩
    = Σ[ _ ∈ (Γ ,, FromPred A P) ⟨ left ⟩ ] B
    = Σ[ _ ∈ Σ[ _ ∈ Γ ⟨ left ⟩ ] FromPred A P ⟨ left , _ ⟩ ] B
    = Σ[ _ ∈ Σ[ _ ∈ Γ ⟨ left ⟩ ] A ] B

    f a b : C = FromPred C R ⟨ left  , [ [ _ , a ] , b ] ⟩
  -}
from-pred2 f h ⟨ relation , [ [ _ , [ a , p ] ] , [ b , q ] ] ⟩' = [ f a b , h p q ]
  {-
    [ [ _ , [ a , p ] ] , [ b , q ] ] : (Γ ,, FromPred A P ,, FromPred B Q) ⟨ relation ⟩
    = Σ[ _ ∈ (Γ ,, FromPred A P) ⟨ relation ⟩ ] FromPred B Q ⟨ relation , _ ⟩
    = Σ[ _ ∈ (Γ ,, FromPred A P) ⟨ relation ⟩ ] Σ[ b ∈ B ] b ∈ Q
    = Σ[ _ ∈ Σ[ _ ∈ Γ ⟨ relation ⟩ ] FromPred A P ⟨ relation , _ ⟩ ] Σ[ b ∈ B ] b ∈ Q
    = Σ[ _ ∈ Σ[ _ ∈ Γ ⟨ relation ⟩ ] Σ[ a ∈ A ] a ∈ P ] Σ[ b ∈ B ] b ∈ Q

    [ f a b , h p q ] : Σ[ c ∈ C ] c ∈ R = FromPred C R ⟨ relation , [ [ _ , [ a , p ] ] , [ b , q ] ] ⟩
  -}
Tm.naturality (from-pred2 f h) left-id refl = refl
Tm.naturality (from-pred2 f h) relation-id refl = refl
Tm.naturality (from-pred2 f h) left-rel refl = refl


--------------------------------------------------
-- Definition of a modality from ¶ to ★.

just-left : Ctx ★ → Ctx ¶
just-left Γ ⟨ left ⟩ = Γ ⟨ tt ⟩
just-left Γ ⟨ relation ⟩ = ⊥
_⟪_⟫_ (just-left Γ) left-id = id
_⟪_⟫_ (just-left Γ) relation-id = id
_⟪_⟫_ (just-left Γ) left-rel = ⊥-elim
ctx-id (just-left Γ) {x = left} = refl
ctx-id (just-left Γ) {x = relation} = refl
ctx-comp (just-left Γ) {f = left-id} = refl
ctx-comp (just-left Γ) {f = relation-id} = refl
ctx-comp (just-left Γ) {f = left-rel} {g = relation-id} = refl

-- Given a substitution σ from context Δ to Γ over the trivial base category, constructs a substituion between their corresponding contexts over the base category ¶. 
just-left-subst : {Δ Γ : Ctx ★} → Δ ⇒ Γ → just-left Δ ⇒ just-left Γ
func (just-left-subst σ) {x = left}     = func σ
func (just-left-subst σ) {x = relation} = ⊥-elim
_⇒_.naturality (just-left-subst σ) {f = left-id} = refl

-- Every substitution constructed using `just-left-subst` preserves the equivalence of substitutions `_≅ˢ_`.
just-left-subst-cong : {Δ Γ : Ctx ★} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → just-left-subst σ ≅ˢ just-left-subst τ
eq (just-left-subst-cong σ=τ) {x = left} δ = eq σ=τ δ

-- `just-left-subst` respects identity substitutions. 
just-left-subst-id : {Γ : Ctx ★} → just-left-subst (id-subst Γ) ≅ˢ id-subst (just-left Γ)
eq just-left-subst-id {x = left} _ = refl

-- `just-left-subst` respects composition of substitutions.
just-left-subst-⊚ : {Δ Γ Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                    just-left-subst (σ ⊚ τ) ≅ˢ just-left-subst σ ⊚ just-left-subst τ
eq (just-left-subst-⊚ σ τ) {x = left} _ = refl

-- Given a type in context `just-left Γ` over ¶, constructs a type in context Γ over the trivial base category.
forget-right-ty : {Γ : Ctx ★} → Ty (just-left Γ) → Ty Γ
forget-right-ty T ⟨ tt , γ ⟩ = T ⟨ left , γ ⟩
forget-right-ty {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ left-id , trans (sym (ctx-id Γ)) eγ ⟫ t
ty-cong (forget-right-ty T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (forget-right-ty T) = strong-ty-id T
ty-comp (forget-right-ty T) = strong-ty-comp T

module _ {Γ : Ctx ★} {T : Ty (just-left Γ)} where
  -- Given a term of some type T in context `just-left Γ` over ¶, constructs a term of type `forget-right-ty T` in context Γ over the trivial base category.
  forget-right-tm : Tm (just-left Γ) T → Tm Γ (forget-right-ty T)
  forget-right-tm t ⟨ _ , γ ⟩' = t ⟨ left , γ ⟩'
  Tm.naturality (forget-right-tm t) tt eγ = Tm.naturality t left-id _

  -- the inverse of `forget-right-tm`
  unforget-right-tm : Tm Γ (forget-right-ty T) → Tm (just-left Γ) T
  unforget-right-tm t ⟨ left , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (unforget-right-tm t) left-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ) eγ))


module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (just-left Γ)} where
  forget-right-ty-natural : (forget-right-ty T) [ σ ] ≅ᵗʸ forget-right-ty (T [ just-left-subst σ ])
  func (from forget-right-ty-natural) = id
  _↣_.naturality (from forget-right-ty-natural) = ty-cong T refl
  func (to forget-right-ty-natural) = id
  _↣_.naturality (to forget-right-ty-natural) = ty-cong T refl
  eq (isoˡ forget-right-ty-natural) _ = refl
  eq (isoʳ forget-right-ty-natural) _ = refl

  forget-right-tm-natural : (t : Tm (just-left Γ) T) →
                            forget-right-tm t [ σ ]' ≅ᵗᵐ ι[ forget-right-ty-natural ] forget-right-tm (t [ just-left-subst σ ]')
  eq (forget-right-tm-natural t) _ = refl

  unforget-right-tm-natural : (t : Tm Γ (forget-right-ty T)) →
                              unforget-right-tm t [ just-left-subst σ ]' ≅ᵗᵐ unforget-right-tm (ι⁻¹[ forget-right-ty-natural ] (t [ σ ]'))
  eq (unforget-right-tm-natural t) {x = left} _ = refl

forget-right-ty-cong : {Γ : Ctx ★} {T : Ty (just-left Γ)} {T' : Ty (just-left Γ)} →
                       T ≅ᵗʸ T' → forget-right-ty T ≅ᵗʸ forget-right-ty T'
func (from (forget-right-ty-cong T=T')) = func (from T=T')
_↣_.naturality (from (forget-right-ty-cong T=T')) = _↣_.naturality (from T=T')
func (to (forget-right-ty-cong T=T')) = func (to T=T')
_↣_.naturality (to (forget-right-ty-cong T=T')) = _↣_.naturality (to T=T')
eq (isoˡ (forget-right-ty-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-right-ty-cong T=T')) = eq (isoʳ T=T')

module _ {Γ : Ctx ★} {T : Ty (just-left Γ)} where
  forget-right-tm-cong : {t t' : Tm (just-left Γ) T} → t ≅ᵗᵐ t' → forget-right-tm t ≅ᵗᵐ forget-right-tm t'
  eq (forget-right-tm-cong t=t') γ = eq t=t' γ

  unforget-right-tm-cong : {t t' : Tm Γ (forget-right-ty T)} → t ≅ᵗᵐ t' → unforget-right-tm t ≅ᵗᵐ unforget-right-tm t'
  eq (unforget-right-tm-cong t=t') {x = left} γ = eq t=t' γ

  forget-right-β : (t : Tm (just-left Γ) T) → unforget-right-tm (forget-right-tm t) ≅ᵗᵐ t
  eq (forget-right-β t) {x = left} _ = refl

  forget-right-η : (t : Tm Γ (forget-right-ty T)) → forget-right-tm (unforget-right-tm t) ≅ᵗᵐ t
  eq (forget-right-η t) _ = refl

module _ {Γ : Ctx ★} {T S : Ty (just-left Γ)} {T=S : T ≅ᵗʸ S} where
  forget-right-tm-ι : (s : Tm (just-left Γ) S) → ι[ forget-right-ty-cong T=S ] forget-right-tm s ≅ᵗᵐ forget-right-tm (ι[ T=S ] s)
  eq (forget-right-tm-ι s) _ = refl

  unforget-right-tm-ι : (s : Tm Γ (forget-right-ty S)) → ι[ T=S ] unforget-right-tm s ≅ᵗᵐ unforget-right-tm (ι[ forget-right-ty-cong T=S ] s)
  eq (unforget-right-tm-ι s) {x = left} _ = refl

instance
  just-left-is-functor : IsCtxFunctor just-left
  ctx-map {{just-left-is-functor}} = just-left-subst
  ctx-map-cong {{just-left-is-functor}} = just-left-subst-cong
  ctx-map-id {{just-left-is-functor}} = just-left-subst-id
  ctx-map-⊚ {{just-left-is-functor}} = just-left-subst-⊚

just-left-functor : CtxFunctor ★ ¶
ctx-op just-left-functor = just-left
is-functor just-left-functor = just-left-is-functor

forget-right : Modality ¶ ★
ctx-functor forget-right = just-left-functor
⟨_∣_⟩ forget-right = forget-right-ty
mod-cong forget-right = forget-right-ty-cong
eq (from-eq (mod-cong-refl forget-right)) _ = refl
eq (from-eq (mod-cong-sym forget-right)) _ = refl
eq (from-eq (mod-cong-trans forget-right)) _ = refl
eq (from-eq (mod-cong-cong forget-right 𝑒)) t = eq (from-eq 𝑒) t
mod-natural forget-right = forget-right-ty-natural
eq (from-eq (mod-natural-ty-eq forget-right _ _)) _ = refl
eq (from-eq (mod-natural-id forget-right {T = T})) _ = ty-id T
eq (from-eq (mod-natural-⊚ forget-right _ _ {T = T})) _ = sym (ty-id T)
eq (from-eq (mod-natural-subst-eq forget-right {T = T} _)) _ = ty-cong T refl
mod-intro forget-right = forget-right-tm
mod-intro-cong forget-right = forget-right-tm-cong
mod-intro-natural forget-right = forget-right-tm-natural
mod-intro-ι forget-right = forget-right-tm-ι
mod-elim forget-right = unforget-right-tm
mod-elim-cong forget-right = unforget-right-tm-cong
mod-β forget-right = forget-right-β
mod-η forget-right = forget-right-η

extract-forget-right-pred : {A : Set} {P : Pred A 0ℓ} → Extractable (forget-right-ty (FromPred A P))
translated-type (extract-forget-right-pred {A = A}) = A
extract-term extract-forget-right-pred t = t ⟨ tt , tt ⟩'
embed-term extract-forget-right-pred a = MkTm (λ _ _ → a) (λ _ _ → refl)