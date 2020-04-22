module Types.Functions where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

-- TODO: show that everything is natural with respect to the context (so e.g. that
-- (T ⇛ S) [ σ ] ≡ T [ σ ] ⇛ S [ σ ])

--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

record PresheafFunc {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) (n : ℕ) (γ : Γ ⟨ n ⟩) : Set ℓ where
  constructor MkFunc
  field
    _$⟨_,_⟩_ : ∀ {m} (m≤n : m ≤ n) {γ' : Γ ⟨ m ⟩} (eq : Γ ⟪ m≤n ⟫ γ ≡ γ') →
               T ⟨ m , γ' ⟩ → S ⟨ m , γ' ⟩
    naturality : ∀ {k m} {k≤m : k ≤ m} {m≤n : m ≤ n} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                 (eq-nm : Γ ⟪ m≤n ⟫ γ ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) (t : T ⟨ m , γm ⟩)→
                 _$⟨_,_⟩_ (≤-trans k≤m m≤n) (strong-rel-comp Γ eq-nm eq-mk) (T ⟪ k≤m , eq-mk ⟫ t) ≡
                   S ⟪ k≤m , eq-mk ⟫ (_$⟨_,_⟩_ m≤n eq-nm t)
  infix 13 _$⟨_,_⟩_
open PresheafFunc public

$-ineq-cong : {Γ : Ctx ℓ} {T S : Ty Γ} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (f : PresheafFunc T S n γn)
              {m≤n m≤n' : m ≤ n} (e-ineq : m≤n ≡ m≤n')
              (eγ : Γ ⟪ m≤n' ⟫ γn ≡ γm)
              {t : T ⟨ m , γm ⟩} →
              f $⟨ m≤n , trans (cong (Γ ⟪_⟫ γn) e-ineq) eγ ⟩ t ≡ f $⟨ m≤n' , eγ ⟩ t
$-ineq-cong f refl eγ = refl

to-pshfun-eq : {Γ : Ctx ℓ} {T S : Ty Γ} {n : ℕ} {γ : Γ ⟨ n ⟩} {f g : PresheafFunc T S n γ} →
               (∀ {m} (m≤n : m ≤ n) {γ'} (eq : Γ ⟪ m≤n ⟫ γ ≡ γ') t →
                   f $⟨ m≤n , eq ⟩ t ≡ g $⟨ m≤n , eq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ m≤n → funextI (funext λ eq → funext λ t → e m≤n eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

lower-presheaffunc : ∀ {m n} {Γ : Ctx ℓ} {T S : Ty Γ} (m≤n : m ≤ n)
                     {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eq : Γ ⟪ m≤n ⟫ γn ≡ γm) →
                     PresheafFunc T S n γn → PresheafFunc T S m γm
lower-presheaffunc {m = m}{n}{Γ}{T}{S} m≤n {γn}{γm} eq-nm f = MkFunc g g-nat
  where
    g : ∀ {k} (k≤m : k ≤ m) {γk} (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) →
        T ⟨ k , γk ⟩ → S ⟨ k , γk ⟩
    g k≤m eq-mk = f $⟨ ≤-trans k≤m m≤n , strong-rel-comp Γ eq-nm eq-mk ⟩_
    open ≡-Reasoning
    g-nat : ∀ {k l} {k≤l : k ≤ l} {l≤m : l ≤ m} {γl : Γ ⟨ l ⟩} {γk : Γ ⟨ k ⟩}
            (eq-ml : Γ ⟪ l≤m ⟫ γm ≡ γl) (eq-lk : Γ ⟪ k≤l ⟫ γl ≡ γk) → _
    g-nat {k≤l = k≤l}{l≤m} eq-ml eq-lk t =
      f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n , strong-rel-comp Γ eq-nm (strong-rel-comp Γ eq-ml eq-lk) ⟩ (T ⟪ k≤l , eq-lk ⟫ t)
        ≡⟨ cong (f $⟨ _ ,_⟩ _) (uip _ _) ⟩
      f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n , trans (cong (Γ ⟪_⟫ γn) (≤-irrelevant _ _))
                                                 (strong-rel-comp Γ (strong-rel-comp Γ eq-nm eq-ml) eq-lk) ⟩
           (T ⟪ k≤l , eq-lk ⟫ t)
        ≡⟨ $-ineq-cong f (≤-irrelevant _ _) _ ⟩
      f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) , strong-rel-comp Γ (strong-rel-comp Γ eq-nm eq-ml) eq-lk ⟩ (T ⟪ k≤l , eq-lk ⟫ t)
        ≡⟨ naturality f (strong-rel-comp Γ eq-nm eq-ml) eq-lk t ⟩
      S ⟪ k≤l , eq-lk ⟫ (f $⟨ ≤-trans l≤m m≤n , strong-rel-comp Γ eq-nm eq-ml ⟩ t) ∎

_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (_⇛_ {Γ = Γ} T S) n γ = PresheafFunc T S n γ
morph (T ⇛ S) = lower-presheaffunc
morph-id (_⇛_ {Γ = Γ} T S) f = to-pshfun-eq λ m≤n eγ t →
  f $⟨ ≤-trans m≤n ≤-refl , strong-rel-comp Γ (rel-id Γ _) eγ ⟩ t
    ≡⟨ cong (λ x → f $⟨ _ , x ⟩ _) (uip _ _) ⟩
  f $⟨ ≤-trans m≤n ≤-refl , trans (cong (Γ ⟪_⟫ _) (≤-irrelevant _ _)) eγ ⟩ t
    ≡⟨ $-ineq-cong f (≤-irrelevant _ _) eγ ⟩
  f $⟨ m≤n , eγ ⟩ t ∎
  where open ≡-Reasoning
morph-comp (_⇛_ {Γ = Γ} T S) l≤m m≤n eq-nm eq-ml f = to-pshfun-eq λ k≤l eq-lk t →
  f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) , strong-rel-comp Γ (strong-rel-comp Γ eq-nm eq-ml) eq-lk ⟩ t
    ≡⟨ cong (λ x → f $⟨ _ , x ⟩ _) (uip _ _) ⟩
  f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) , trans (cong (Γ ⟪_⟫ _) (≤-irrelevant _ _))
                                             (strong-rel-comp Γ eq-nm (strong-rel-comp Γ eq-ml eq-lk)) ⟩ t
    ≡⟨ $-ineq-cong f (≤-irrelevant _ _) (strong-rel-comp Γ eq-nm (strong-rel-comp Γ eq-ml eq-lk)) ⟩
  f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n , strong-rel-comp Γ eq-nm (strong-rel-comp Γ eq-ml eq-lk) ⟩ t ∎
  where open ≡-Reasoning

lam : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
term (lam T {S} b) n γ = MkFunc (λ m≤n {γ'} eγ t → b ⟨ _ , [ γ' , t ] ⟩')
                                (λ {k}{m}{k≤m}{_}{γm}{γk} eq-nm eq-mk t →
  b ⟨ k , [ γk , T ⟪ k≤m , eq-mk ⟫ t ] ⟩'
    ≡⟨ sym (naturality b k≤m (to-Σ-eq eq-mk (morph-subst T refl eq-mk t))) ⟩
  S ⟪ k≤m , from-Σ-eq1 (to-Σ-eq eq-mk _) ⟫ b ⟨ m , [ γm , t ] ⟩'
    ≡⟨ cong (λ x → S ⟪ k≤m , x ⟫ _) (from-to-Σ-eq1 (morph-subst T refl eq-mk t)) ⟩
  S ⟪ k≤m , eq-mk ⟫ b ⟨ m , [ γm , t ] ⟩' ∎)
  where open ≡-Reasoning
naturality (lam T b) m≤n eq-nm = to-pshfun-eq λ k≤m eq-mk t → refl

_€⟨_,_⟩_ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → S ⟨ n , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f n γ t = f ⟨ n , γ ⟩' $⟨ ≤-refl , rel-id Γ γ ⟩ t

€-natural : {Γ : Ctx ℓ} {T S : Ty Γ} (f : Tm Γ (T ⇛ S)) (m≤n : m ≤ n)
            {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm)
            (t : T ⟨ n , γn ⟩) →
            S ⟪ m≤n , eγ ⟫ (f €⟨ n , γn ⟩ t) ≡ f €⟨ m , γm ⟩ (T ⟪ m≤n , eγ ⟫ t)
€-natural {Γ = Γ}{T}{S} f m≤n {γn}{γm} eγ t =
  S ⟪ m≤n , eγ ⟫ (f ⟨ _ , γn ⟩' $⟨ ≤-refl , rel-id Γ γn ⟩ t)
    ≡⟨ sym (naturality (f ⟨ _ , γn ⟩') (rel-id Γ γn) eγ t) ⟩
  f ⟨ _ , γn ⟩' $⟨ ≤-trans m≤n ≤-refl , strong-rel-comp Γ (rel-id Γ γn) eγ ⟩ (T ⟪ m≤n , eγ ⟫ t)
    ≡⟨ cong (λ x → f ⟨ _ , γn ⟩' $⟨ _ , x ⟩ _) (uip _ _) ⟩
  f ⟨ _ , γn ⟩' $⟨ ≤-trans m≤n ≤-refl , trans (cong (Γ ⟪_⟫ γn) (≤-irrelevant _ _))
                                             (strong-rel-comp Γ eγ (rel-id Γ γm)) ⟩
      (T ⟪ m≤n , eγ ⟫ t)
    ≡⟨ $-ineq-cong (f ⟨ _ , γn ⟩') (≤-irrelevant _ _) (strong-rel-comp Γ eγ (rel-id Γ γm)) ⟩
  f ⟨ _ , γn ⟩' $⟨ ≤-trans ≤-refl m≤n , strong-rel-comp Γ eγ (rel-id Γ γm) ⟩ (T ⟪ m≤n , eγ ⟫ t)
    ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f m≤n eγ) ⟩
  f ⟨ _ , γm ⟩' $⟨ ≤-refl , rel-id Γ γm ⟩ (T ⟪ m≤n , eγ ⟫ t) ∎
  where open ≡-Reasoning

app : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app f t) n γ = f €⟨ n , γ ⟩ (t ⟨ n , γ ⟩')
naturality (app {Γ = Γ}{T}{S} f t) m≤n {γn}{γm} eq =
  S ⟪ m≤n , eq ⟫ (f €⟨ _ , γn ⟩ (t ⟨ _ , γn ⟩'))
    ≡⟨ €-natural f m≤n eq (t ⟨ _ , γn ⟩') ⟩
  f €⟨ _ , γm ⟩ (T ⟪ m≤n , eq ⟫ (t ⟨ _ , γn ⟩'))
    ≡⟨ cong (f €⟨ _ , γm ⟩_) (naturality t m≤n eq) ⟩
  f €⟨ _ , γm ⟩ (t ⟨ _ , γm ⟩') ∎
  where open ≡-Reasoning

{-
to-⇛[_]_ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} → Tm Δ ((T [ σ ]) ⇛ (S [ σ ])) → Tm Δ ((T ⇛ S) [ σ ])
term (to-⇛[_]_ σ {T}{S} f) n δ = MkFunc (λ m≤n t → subst (λ x → S ⟨ _ , x ⟩) (sym (naturality σ δ))
                                                       (f ⟨ _ , δ ⟩' $⟨ m≤n ⟩
                                                       subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) t))
                                         {!!}
naturality (to-⇛[ σ ] f) = {!!}
-}
{-
-- Another approach to the introduction of function types (based on https://arxiv.org/pdf/1805.08684.pdf).
{-
_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⇛ S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊚ π ])
morph (_⇛_ {Γ = Γ} T S) = λ m≤n γ s → helper (s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]')
  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊚ π ] [ (to-𝕪⇒𝕪 m≤n) ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊚ π ])
    helper {m} {n} {m≤n} {γ} = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊚ π) ((to-𝕪⇒𝕪 m≤n) ⊹))
morph-id (T ⇛ S) = {!!}
morph-comp (T ⇛ S) = {!!}
-}
{-
Π : {Γ : Ctx ℓ} (T : Ty Γ) (S : Ty (Γ ,, T)) → Ty Γ
type (Π T S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊹ ])
morph (Π {Γ = Γ} T S) {m = m} m≤n γ s = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊹ ])) (𝕪-comp m≤n γ)
                                        (subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) {!!} {!s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]'!})
{-  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊹ ] [ to-𝕪⇒𝕪 m≤n ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊹ ])
    helper {m} {n} {m≤n} {γ} = {!subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹))!} ∘
                               {!subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊹) (to-𝕪⇒𝕪 m≤n ⊹))!}-}
morph-id (Π T S) = {!!}
morph-comp (Π T S) = {!!}
-}
{-
module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  lam : Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
  term (lam b) = λ n γ → subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) (S [ x ])) (⊹-π-comm (to-𝕪⇒* γ))
                                (subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) x) (ty-subst-comp S π (to-𝕪⇒* γ ⊹))
                                       (b [ to-𝕪⇒* γ ⊹ ]'))
  naturality (lam b) = {!!}

  ap : Tm Γ (T ⇛ S) → Tm (Γ ,, T) (S [ π ])
  term (ap f) = λ n γ → {!term f!}
  naturality (ap f) = {!!}

  app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
  app f t = {!ap f [ ? ]'!}
-}
-}
