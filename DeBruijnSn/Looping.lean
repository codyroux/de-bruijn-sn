
inductive Term : Type where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term

def Ren := Nat → Nat

def Subst := Nat → Term

def Ren.lift n := n+1

def cons u (σ : Nat → α) := λ n ↦ if n = 0 then u else σ (n-1)


theorem cons_zero (u : α) (σ : Nat → α) : cons u σ 0 = u := by simp [cons]

infix:80 " ⬝ " => cons


@[simp]
def renVar (n : Nat) (ρ : Ren) : Nat := ρ n

def renTerm (ρ : Ren) : Term → Term
| .var n => .var $ renVar n ρ
| .app t₁ t₂ => .app (renTerm ρ t₁) (renTerm ρ t₂)
| .lam t => .lam (renTerm (0 ⬝ (Ren.lift ∘ ρ)) t)

notation "↑" => renTerm Ren.lift

def Subst.lift (σ : Subst) : Subst := .var 0 ⬝ (↑ ∘ σ)

notation "⇑" => Subst.lift


@[simp]
def substVar (n : Nat) (σ : Subst) : Term := σ n

def idS := λ n ↦ Term.var n
set_option hygiene false

-- idk about these precedences
notation t:60 " ⟨ " s:60 " ⟩ " => (subst s t)

def subst (σ : Subst) : Term → Term
| .var n => substVar n σ
| .app t₁ t₂ => .app (t₁⟨σ⟩) (t₂⟨σ⟩)
| .lam t => .lam (t⟨ ⇑ σ ⟩)

notation t:60 " ⟶ " t':60 => (Red t t')

inductive Red : Term → Term → Type where
| beta : (.app (.lam t) u) ⟶ t⟨u ⬝ idS⟩
| congApp₁ : t ⟶ t' → (.app t u) ⟶ (.app t' u)
| congApp₂ : u ⟶ u' → (.app t u) ⟶ (.app t u')
| congLam : t ⟶ t' → (.lam t) ⟶ (.lam t')

notation t:60 " ⟶* " t':60 => (RedStar t t')

inductive RedStar : Term → Term → Type :=
| done : t ⟶* t
| step : t₁ ⟶ t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃

-- Weak head expansion: a family of "necessary reductions for normalization"
inductive WeakHeadExp : Term → Term → Term → Type where
| headWH : WeakHeadExp (.app (.lam t) u) (t⟨u⬝idS⟩) u
| appWH : WeakHeadExp t t' u → WeakHeadExp (.app t v) (.app t' v) u

-- A little strange to *define* SN like this...
-- but these are all *true* statements about strongly normalizing
-- terms (and we claim that they are sufficient conditions as well)
mutual
inductive SN : Term → Type where
| normLambda : SN t → SN (.lam t)
| normNE : NE t → SN t
| normVarApp : SN (.app t (.var n)) → SN t
| normWH : WeakHeadExp t t' u → SN t' → SN u → SN t
inductive NE : Term → Type where
| varNE : NE (.var n)
| appNE : NE n → SN t → NE (.app n t)
end

inductive Ty where
| retract : Ty
| arrow : Ty → Ty → Ty

infix:60 " ⇒ " => Ty.arrow

notation "Ctx" => (List Ty)

notation ctx:50 " ⊢ " t:50 " :+ " ty:50 => (TypeTerm ctx t ty)
inductive TypeTerm : Ctx → Term → Ty → Type where
| varTy : ∀ Γ A n, Γ.get? n = .some A →  Γ ⊢ .var n :+ A
| appTy : ∀ Γ A B t u, Γ ⊢ t :+ A ⇒ B → Γ ⊢ u :+ A → Γ ⊢ .app t u :+ B
| lamTy : ∀ Γ A t, (A :: Γ) ⊢ t :+ B → Γ ⊢ .lam t :+ A ⇒ B
| unfoldTy : ∀ Γ t, Γ ⊢ t :+ .retract → Γ ⊢ t :+ .retract ⇒ .retract
| foldTy : ∀ Γ t, Γ ⊢ t :+ .retract ⇒ .retract → Γ ⊢ t :+ .retract

-- This axiom is false, of course. But it'll allow us to prove normalization
-- in an interesting way.
-- FIXME: is this the right axiom?
axiom foldType : ∀ P : Term → Type, (∀ t, P t → P t) → ∀ t, P t

notation "⟦" ty "⟧" => (interpTy ty)

@[simp]
def interpTy : Ty → Term → Type
| .retract => SN
| ty₁ ⇒ ty₂ => λ t ↦ ∀ u, ⟦ty₁⟧ u → ⟦ty₂⟧ (.app t u)

def validSubst (Γ : Ctx) (σ : Subst) := ∀ n A, Γ.get? n = .some A → ⟦A⟧ (σ n)

infix:85 " ⊧ " => validSubst

theorem Function.comp_assoc : f ∘ g ∘ h = (f ∘ g) ∘ h :=
by funext; simp

def Subst.comp (σ τ : Subst) : Subst :=
  λ n ↦ (σ n)⟨τ⟩

infix:81 " ⟫ " => Subst.comp

@[simp]
theorem subst_var_comp : (substVar x τ)⟨σ⟩ = substVar x (τ ⟫ σ) :=
by
  simp [substVar, subst, Subst.comp]

@[simp]
theorem cons_ren : σ ∘ (v ⬝ ρ) = (σ v) ⬝ (σ ∘ ρ) :=
by
  funext x; simp [cons]; split <;> trivial

theorem cons_comp : (t ⬝ σ) ⟫ τ = t⟨τ⟩ ⬝ (σ ⟫ τ) :=
by
  funext x
  simp [Subst.comp, subst, cons]
  split <;> simp

@[simp]
theorem cons_lift : (t ⬝ σ) ∘ Ren.lift = σ :=
by
  funext x; simp [cons, Ren.lift]
  split
  case h.inl => contradiction
  case h.inr => trivial

theorem renTerm_comp_aux : renTerm ρ₁ (renTerm ρ₂ t) = renTerm (ρ₁ ∘ ρ₂) t :=
by
  cases t <;> simp [renTerm]
  case app => constructor <;> apply renTerm_comp_aux
  case lam =>
    rw [renTerm_comp_aux]; simp [cons_zero, Function.comp_assoc]

theorem renTerm_comp : (renTerm ρ₁) ∘ (renTerm ρ₂) = renTerm (ρ₁ ∘ ρ₂) :=
by
  funext t; apply renTerm_comp_aux

theorem comp_assoc_ren_aux : (renTerm ρ t)⟨σ⟩ = t⟨σ ∘ ρ⟩ :=
by
  cases t <;> simp [renTerm, subst]
  case app => constructor <;> apply comp_assoc_ren_aux
  case lam =>
    rw [comp_assoc_ren_aux]
    simp [Subst.lift]
    simp [cons_zero]
    rw [Function.comp_assoc, cons_lift]
    rw [← Function.comp_assoc]

theorem comp_assoc_ren : renTerm ρ ∘ τ ⟫ σ = τ ⟫ σ ∘ ρ :=
by
  funext; simp [renTerm, subst, Subst.comp]
  apply comp_assoc_ren_aux

theorem congr_arg₂ (x x' : α) (y y' : β) (f : α → β → γ): x = x' → y = y' → f x y = f x' y' :=
by intros r₁ r₂; rw [r₁, r₂]

theorem ren_subst_assoc_aux : renTerm ρ (t⟨σ⟩) = t⟨renTerm ρ ∘ σ⟩ :=
by
  cases t <;> simp [subst, renTerm]
  case app => constructor <;> apply ren_subst_assoc_aux
  case lam =>
    rw [ren_subst_assoc_aux]
    simp [Subst.lift, renTerm, cons_zero]
    apply congr_arg₂ <;> try trivial
    apply congr_arg₂; trivial
    -- FIXME: this is ugly
    rw [Function.comp_assoc, renTerm_comp]; simp
    rw [Function.comp_assoc, renTerm_comp]

theorem ren_subst_assoc : renTerm ρ ∘ (σ ⟫ τ) = σ ⟫ (renTerm ρ ∘ τ) :=
by
  funext t; simp [Function.comp, Subst.comp]
  rw [ren_subst_assoc_aux]
  apply congr_arg₂ <;> trivial

theorem shift_comp : ⇑ (σ ⟫ τ) = (⇑ σ) ⟫ (⇑ τ) :=
by
  simp [Subst.lift, cons_comp, subst, cons_zero]
  rw [comp_assoc_ren, cons_lift]
  apply congr_arg₂; trivial
  rw [ren_subst_assoc]

theorem subst_subst_comp : t⟨τ⟩⟨σ⟩ = t⟨τ ⟫ σ⟩ :=
by
  cases t <;> simp [subst]
  case var => simp [Subst.comp]
  case app => constructor <;> apply subst_subst_comp
  case lam => rw [subst_subst_comp, shift_comp]

theorem comp_assoc : (σ ⟫ τ) ⟫ φ = σ ⟫ (τ ⟫ φ) :=
by
  funext
  simp [Subst.comp]
  apply subst_subst_comp

theorem subst_comp : t⟨σ⟩⟨τ⟩ = t⟨σ ⟫ τ⟩ :=
by
  cases t <;> simp [subst]
  case var => simp [Subst.comp]
  case app => constructor <;> apply subst_comp
  case lam => rw [subst_comp, shift_comp]

@[simp]
theorem liftIdS : ⇑ idS = idS :=
by
  funext t
  cases t <;> simp [idS, Subst.lift, cons, Ren.lift, renTerm]
  apply Nat.sub_succ

@[simp]
theorem substIdS : t⟨idS⟩ = t :=
by
  cases t <;> simp [subst, substVar]
  case var => simp [idS]
  case app => constructor <;> apply substIdS
  case lam => apply substIdS


theorem renTerm_IdS : t⟨idS ∘ ρ⟩ = renTerm ρ t :=
by
  rw [← comp_assoc_ren_aux]; simp

@[simp]
theorem compIdL : idS ⟫ σ = σ :=
by
  funext; simp [Subst.comp, idS, subst, substVar]

@[simp]
theorem compIdR : σ ⟫ idS = σ :=
by
  funext x; simp [Subst.comp]

theorem comp_lift : (⇑ σ) ⟫ (t ⬝ idS) = t ⬝ σ :=
by
  simp [Subst.lift, subst, cons_comp]
  rw [comp_assoc_ren]
  rw [cons_lift, compIdR]; simp [cons_zero]

theorem app_subst : (.app ((.lam t)⟨σ⟩) u) ⟶ t⟨u⬝σ⟩ :=
by
  simp [subst]
  rw [← comp_lift, ← subst_comp]
  apply Red.beta

theorem wh_comp : WeakHeadExp t t' u → SN u → ⟦A⟧ t' → ⟦A⟧ t :=
by
  cases A <;> simp
  case retract =>
    intros wh sn_u sn_t'; apply SN.normWH (u := u) <;> trivial
  case arrow A₁ A₂ =>
    intros wh sn_u comp_t' u' comp_u'
    apply wh_comp; apply WeakHeadExp.appWH; trivial
    . trivial
    . apply comp_t' <;> trivial



mutual
theorem sn_comp : ⟦A⟧ t → SN t :=
by
  cases A <;> simp
  case retract => intros; trivial
  case arrow =>
    intro comp_t
    apply SN.normVarApp
    apply sn_comp; apply comp_t
    apply neutral_comp
    constructor; exact 0

theorem neutral_comp : NE n → ⟦A⟧ n :=
by
  cases A <;> simp
  case retract => intro ne_n; constructor; trivial
  case arrow =>
    intros neutral_n u comp_u
    have norm_u := sn_comp comp_u
    apply neutral_comp
    constructor <;> trivial
end

theorem soundness (d : Γ ⊢ t :+ A) (valid : Γ ⊧ σ): ⟦A⟧ (t⟨σ⟩) :=
by
  cases d <;> simp [subst]
  case varTy n h => apply valid; trivial
  case appTy T t u tyT tyU =>
    have ihT : ⟦T ⇒ A⟧ (t⟨σ⟩) := by apply soundness <;> trivial
    have ihU : ⟦T⟧ (u⟨σ⟩) := by apply soundness <;> trivial
    simp at ihT
    apply (ihT (u⟨σ⟩) ihU)
  case lamTy B A t tyT =>
    intros u compU
    have wh_t : WeakHeadExp (Term.app (Term.lam (t⟨⇑ σ⟩)) u) (t⟨u ⬝ σ⟩) u :=
    by
      rw [← comp_lift,← subst_comp]
      apply WeakHeadExp.headWH
    apply wh_comp wh_t
    . apply sn_comp; trivial
    . apply soundness; trivial
      intro v; cases v <;> intros; simp [cons, List.get?] at *
      case a.valid.zero A' eq => exact eq ▸ compU
      case a.valid.succ =>
        simp [cons, List.get?] at *
        apply valid; trivial
  case unfoldTy =>
    intros _ _
    apply foldType -- This feels too nuclear
    intros _ _; trivial
  case foldTy =>
    apply sn_comp
    apply soundness <;> trivial


theorem idS_valid : Γ ⊧ idS :=
by
  intros n A _
  apply neutral_comp; simp [idS]; constructor


theorem sn_idX : SN ((.app (.lam (.var 0)) (.var 0))⟨idS⟩) :=
by
  apply (@sn_comp .retract)
  apply @soundness (valid := @idS_valid [.retract])
  repeat constructor

#print sn_idX

#reduce sn_idX

def δ : Term := .lam (.app (.var 0) (.var 0))

theorem sn_Omega : SN ((.app δ δ)⟨idS⟩) :=
by
  apply (@sn_comp .retract)
  apply @soundness (valid := @idS_valid [.retract])
  constructor
  case a.d.a =>
    constructor
    case a =>
      constructor
      case a => apply TypeTerm.unfoldTy; apply TypeTerm.varTy; simp [List.get?]; rfl
      case a => apply TypeTerm.varTy; simp [List.get?]
  case a.d.a =>
    apply TypeTerm.foldTy
    constructor
    case a =>
      constructor
      case a => apply TypeTerm.unfoldTy; apply TypeTerm.varTy; simp [List.get?]; rfl
      case a => apply TypeTerm.varTy; simp [List.get?]
