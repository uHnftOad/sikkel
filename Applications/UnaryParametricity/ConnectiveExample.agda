--------------------------------------------------
-- An example of representation independence using
-- unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.ConnectiveExample where

open import Agda.Builtin.Nat using (_*_; _-_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Level using (0ℓ) 
open import Relation.Unary hiding (_⇒_; _⟨→⟩_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory hiding (★; ¶)
open import Model.Type.Function hiding (_⇛_; lam; lam[_∈_]_)
open import Extraction

open import Applications.UnaryParametricity.Model as M using (_⟨→⟩_)
open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension
open import MSTT.TCMonad using (return)
import Applications.UnaryParametricity.MSTT


--------------------------------------------------
infix 3 IsBool
data IsBool : Pred ℕ 0ℓ where
  one-true : IsBool 1
  zero-false : IsBool 0

-- and
_∧ℕ_ : ℕ → ℕ → ℕ
_∧ℕ_ = _*_

-- not
¬ℕ : ℕ → ℕ
¬ℕ = (_-_) 1 

¬ℕ-preserves-IsBool : (IsBool ⟨→⟩ IsBool) (¬ℕ)
¬ℕ-preserves-IsBool one-true = zero-false
¬ℕ-preserves-IsBool zero-false = one-true

∧ℕ-preserves-IsBool : (IsBool ⟨→⟩ IsBool ⟨→⟩ IsBool) (_∧ℕ_)
∧ℕ-preserves-IsBool one-true one-true = one-true
∧ℕ-preserves-IsBool one-true zero-false = zero-false
∧ℕ-preserves-IsBool zero-false one-true = zero-false
∧ℕ-preserves-IsBool zero-false zero-false = zero-false


--------------------------------------------------
-- Definition of a universe for the instance of MSTT for unary parametricity. There is one code for a type 𝔹 representing ℕ and the predicate IsBool.

data PredCode : Set where
  𝔹-code : PredCode

b-pred-ext : PredExt
PredExt.PredCode b-pred-ext = PredCode
PredExt.show-code b-pred-ext 𝔹-code = "𝔹"
PredExt._≟code_ b-pred-ext 𝔹-code 𝔹-code = return refl
PredExt.interpret-code b-pred-ext 𝔹-code =
  record { Left = ℕ ; Relation = IsBool }


--------------------------------------------------
-- Definition of some basic operations in MSTT

open Applications.UnaryParametricity.MSTT b-pred-ext

private
  variable
    m : ModeExpr

-- a shortcut for defining a Sikkel function
-- Γ ⊢ liftA2 μ A B C : ⟨ μ ∣ A ⇛ B ⇛ C ⟩ ⇛ ⟨ μ ∣ A ⟩ ⇛ ⟨ μ ∣ B ⟩ ⇛ ⟨ μ ∣ C ⟩
liftA2 : ∀ {m m'} → ModalityExpr m' m → TyExpr m' → TyExpr m' → TyExpr m' → TmExpr m
liftA2 μ A B C =
  lam[ μ ∣ "f" ∈ A ⇛ B ⇛ C ]
    lam[ μ ∣ "a" ∈ A ]
      lam[ μ ∣ "b" ∈ B ]
        mod⟨ μ ⟩ (svar "f" ∙ svar "a" ∙ svar "b")


--------------------------------------------------
-- Continuing the Boolean example: definition of the interface
--   and proof that or preserves the predicate IsBool.

record BoolStructure {m} (A : TyExpr m) : Set where
  field
    and : TmExpr m
    not : TmExpr m
    and-well-typed : ∀ {Γ} → infer-type and Γ ≡ ok (A ⇛ A ⇛ A)
    not-well-typed : ∀ {Γ} → infer-type not Γ ≡ ok (A ⇛ A)

open BoolStructure {{...}}
  -- Makes the fields of the record available as functions taking instance arguments

-- P ∨ Q = ¬ ( ¬ P ∧ ¬ Q )
or : (A : TyExpr m) {{_ : BoolStructure A}} → TmExpr m
or A = lam[ "P" ∈ A ] lam[ "Q" ∈ A ] not ∙ (and ∙ (not ∙ svar "P") ∙ (not ∙ svar "Q"))

𝔹 : TyExpr ¶
𝔹 = FromPred 𝔹-code
  -- = (Ext ¶) (FromPred-code 𝔹-code) tt 
  -- Ext ¶ : TyExpr ¶

instance
  𝔹-is-int : BoolStructure 𝔹
  BoolStructure.and 𝔹-is-int = from-pred2 𝔹-code 𝔹-code 𝔹-code (_∧ℕ_) ∧ℕ-preserves-IsBool
  BoolStructure.not 𝔹-is-int = from-pred1 𝔹-code 𝔹-code (¬ℕ) ¬ℕ-preserves-IsBool
  BoolStructure.and-well-typed 𝔹-is-int = refl
  BoolStructure.not-well-typed 𝔹-is-int = refl

--------------------------------------------------
-- Creates a function at mode ★
-- Γ ⊢ or★ : ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩
or★ : TmExpr ★
or★ = liftA2 forget-right 𝔹 𝔹 𝔹 ∙⟨ forget-right ⟩ or 𝔹
--  = (liftA2 forget-right 𝔹 𝔹 𝔹) ∙ (mod⟨ forget-right ⟩ (or 𝔹 {{𝔹-is-int}}))

-- manually proves that the (semantic) types of the function above is extractable
or★-extractable : Extractable ⟦ ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩ ⟧ty
  {-
      ⟦ ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩ ⇛ ⟨ forget-right ∣ 𝔹 ⟩ ⟧ty
    = ⟦ ⟨ forget-right ∣ 𝔹 ⟩ ⟧ty M.⇛ ⟦ ⟨ forget-right ∣ 𝔹 ⟩ ⟧ty M.⇛ ⟦ ⟨ forget-right ∣ 𝔹 ⟩ ⟧ty
    = M.⟨ ⟦ forget-right ⟧modality ∣ ⟦ 𝔹 ⟧ty ⟩ M.⇛ M.⟨ ⟦ forget-right ⟧modality ∣ ⟦ 𝔹 ⟧ty ⟩ M.⇛ M.⟨ ⟦ forget-right ⟧modality ∣ ⟦ 𝔹 ⟧ty ⟩
    = M.⟨ M.forget-right ∣ M.FromPred ℕ IsBool ⟩ M.⇛ M.⟨ M.forget-right ∣ M.FromPred ℕ IsBool ⟩ M.⇛ M.⟨ M.forget-right ∣ M.FromPred ℕ IsBool ⟩

      ⟦ 𝔹 ⟧ty
    = ⟦ (Ext ¶) (FromPred-code 𝔹-code) tt ⟧ty
    = interpret-ext-ty (interpret-code (FromPred-code 𝔹-code)) tt
    = interpret-ext-ty (M.FromPred (CodeLeft 𝔹-code) (CodeRelation 𝔹-code)) tt
    = interpret-ext-ty (M.FromPred ℕ IsBool) tt
    = M.FromPred ℕ IsBool
  -}
or★-extractable = extract-func M.extract-forget-right-pred 
                 (extract-func M.extract-forget-right-pred 
                               M.extract-forget-right-pred)

or-int : ℕ → ℕ → ℕ
or-int = extract-term or★-extractable (⟦ or★ ⟧tm)

or-int-preserves-IsBool : (IsBool ⟨→⟩ IsBool ⟨→⟩ IsBool) or-int
or-int-preserves-IsBool p q = 
  let or-𝔹 = ⟦ or 𝔹 ⟧tm
  in proj₂ ((or-𝔹 €⟨ relation , tt ⟩ [ _ , p ]) $⟨ relation-id , refl ⟩ [ _ , q ])
