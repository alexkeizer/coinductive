import Coinductive

namespace Stream
open Coinductive Lean.Order

inductive StreamF (α : Type w) (Stream : Type w) : Type w where
  -- | snil
  | scons (x : α) (tl : Stream)

inductive StreamF.In (α : Type u) : Type u where
  -- | snil
  | scons (x : α)

instance (α : Type u) : PF (StreamF α) where
  P := ⟨StreamF.In α, fun
    -- | .snil => PEmpty
    | .scons _ => PUnit⟩
  unpack
    -- | .snil => .obj (.snil) nofun
    | .scons hd tl => .obj (.scons hd) λ _ => tl
  pack
    -- | .obj (.snil) _ => .snil
    | .obj (.scons hd) tl => .scons hd (tl ⟨⟩)
  unpack_pack := by rintro _ (_) <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev Stream (α : Type u) : Type u := CoInd (StreamF α)

def Stream.fold (t : StreamF α (Stream α)) : Stream α := CoInd.fold _ t
-- def Stream.snil {α : Type u} : Stream α := Stream.fold (.snil)
def Stream.scons {α : Type u} (hd : α) (tl : Stream α) : Stream α := Stream.fold (.scons hd tl)

-- @[simp]
-- theorem snil_approx_1 α n :
--   (Stream.snil (α:=α)).approx (n + 1) = StreamF.snil := by
--     simp [Stream.snil, Stream.fold, CoInd.fold, PF.map, PF.pack]

@[simp]
theorem scons_approx_1 α i (s : Stream α) n :
  (Stream.scons i s).approx (n + 1) = StreamF.scons i (s.approx n) := by
    simp [Stream.scons, Stream.fold, CoInd.fold, PF.map, PF.pack]

-- @[simp]
-- theorem unfold_snil α :
--   CoInd.unfold _ Stream.snil = StreamF.snil (α:=α) := by
--     simp [Stream.snil, Stream.fold]

@[simp]
theorem unfold_scons α (i : α) s:
  CoInd.unfold _ (Stream.scons i s) = StreamF.scons i s := by
    simp [Stream.scons, Stream.fold]

abbrev OptStreamF α β := (Option <| StreamF α β)
abbrev OptStream α := CoInd (OptStreamF α)

def OptStreamF.scons (hd : α) (tl : β) : OptStreamF α β := some (StreamF.scons hd tl)

def OptStream.fold (t : OptStreamF α (OptStream α)) : OptStream α := CoInd.fold _ t
def OptStream.scons {α : Type u} (hd : α) (tl : OptStream α) : OptStream α := OptStream.fold (.scons hd tl)

def OptStream.none : OptStream α := fold Option.none

@[simp]
theorem OptStream.bot_eq α :
    CoInd.bot (OptStreamF α) = OptStream.none := by
  rw [CoInd.bot_eq];rfl


theorem Stream.le_unfold α (s1 s2 : OptStream α) :
  (s1 ⊑ s2) = (s1 = bot ∨
    ∃ i s1' s2', s1 = .scons i s1' ∧ s2 = .scons i s2' ∧ s1' ⊑ s2') := by
    stop
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-unfold_fold _ s1, <-unfold_fold _ s2]
      rw [<-PF.unpack_pack s1.unfold, <-PF.unpack_pack s2.unfold]
      simp only [h1, h2]
      cases i <;> simp [PF.pack, snil, scons, fold]
      right
      exists ?_, ?_; rotate_left 1
      constructor; rfl
      apply Exists.intro
      constructor; rfl
      simp_all
    · rintro (rfl|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack]
        constructor <;> try rfl
        grind

theorem scons_monoN α i (s1 s2 : OptStream α) n :
  CoIndN.le _ (s1.approx n) (s2.approx n) →
  CoIndN.le _ ((OptStream.scons i s1).approx (n + 1))
    ((OptStream.scons i s2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    stop
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem scons_mono β α [PartialOrder β] i (f : β → OptStream α) :
  monotone f →
  monotone (λ x => OptStream.scons i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply scons_monoN
    grind [CoInd.leN_le, monotone]

def OptStream.map {α} (f : α → β) (s : OptStream α) : OptStream β :=
  match s.unfold with
  | .scons hd tl => .scons (f hd) (map f tl)
  | .none => .none
partial_fixpoint

def OptStream.shead? {α} (s : OptStream α) : Option α :=
  match s.unfold with
  | .scons hd _ => some hd
  | .none => .none

def OptStream.stail {α} (s : OptStream α) : OptStream α :=
  match s.unfold with
  | .scons _ tl => tl
  | .none => none

coinductive OptStream.IsInf : (xs : OptStream α) → Prop where
  | scons (x xs) : OptStream.IsInf xs → OptStream.IsInf (.scons x xs)

def OptStream.shead (xs : OptStream α) (h : xs.IsInf) : α :=
  xs.shead?.get <| by cases h; rfl

def OptStream.toStream (xs : OptStream α) (h : xs.IsInf) : Stream α :=
  let xs : { xs : OptStream α // xs.IsInf } := ⟨xs, h⟩
  let f := fun ⟨xs, h⟩ =>
    .scons (xs.shead h) ⟨xs.stail, by cases h; assumption⟩
  cofix _ f xs

def Stream.shead {α} (s : Stream α) : α :=
  match s.unfold with
  | .scons hd _ => hd

def Stream.stail {α} (s : Stream α) : Stream α :=
  match s.unfold with
  | .scons _ tl => tl

def Stream.toOptStream (xs : Stream α) : OptStream α :=
  .scons xs.shead xs.stail.toOptStream
partial_fixpoint

@[cases_eliminator, elab_as_elim]
def Stream.casesOn {motive : Stream α → Sort u}
    (scons : ∀ (x : α) (xs : Stream α), motive (.scons x xs))
    (xs : Stream α) : motive xs := by
  cases xs using CoInd.casesOn' with | unfold xs =>
  cases xs with | scons x xs =>
  apply scons

@[cases_eliminator, elab_as_elim]
def OptStream.casesOn {motive : OptStream α → Sort u}
    (scons : ∀ (x : α) (xs : OptStream α), motive (.scons x xs))
    (none : motive .none)
    (xs : OptStream α) : motive xs := by
  cases xs using CoInd.casesOn' with | unfold xs =>
  cases xs with
  | some xs => apply scons
  | none => apply none

@[simp, grind =]
theorem Stream.toOptStream_scons : (Stream.scons x xs).toOptStream = .scons x xs.toOptStream := by
  conv => lhs; unfold toOptStream
  rfl

@[simp, grind =]
theorem OptStream.map_scons {f : α → β} : map f (.scons x xs) = .scons (f x) (map f xs) := by
  conv => lhs; unfold map
  rfl

@[simp, grind .]
theorem OptStream.inf_toOptStream (xs : Stream α) : xs.toOptStream.IsInf := by
  apply IsInf.coinduct (fun xs? => ∃ xs : Stream α, xs? = xs.toOptStream)
  · rintro _ ⟨xs, rfl⟩
    cases xs with | scons x xs =>
    refine ⟨x, xs.toOptStream, ⟨xs, rfl⟩, ?_⟩
    simp
  · exact ⟨xs, rfl⟩

def Stream.map (f : α → β) (xs : Stream α) : Stream β :=
  (xs.toOptStream.map f).toStream <| by
    apply OptStream.IsInf.coinduct (fun ys? => ∃ xs? : OptStream α, xs?.IsInf ∧ ys? = xs?.map f)
    · rintro ys? ⟨xs?, h_inf, rfl⟩
      cases h_inf with | scons x xs? h_inf =>
      refine ⟨f x, xs?.map f, ⟨⟨xs?, h_inf, rfl⟩, ?_⟩⟩
      simp
    · have xs_inf : xs.toOptStream.IsInf := by simp
      exact ⟨xs.toOptStream, xs_inf, rfl⟩

@[simp]
theorem unfold_bot : CoInd.unfold (OptStreamF α) ⊥ = none := by
  sorry

@[partial_fixpoint_monotone]
theorem map_mono α β γ [PartialOrder γ] (f : α → β) (g : γ → OptStream α) :
  monotone g →
  monotone (λ x => OptStream.map f (g x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hs : (g t1) ⊑ (g t2) := by grind [monotone]
    generalize g t1 = s1, g t2 = s2 at hs
    induction n generalizing s1 s2; simp [CoIndN.le]
    unfold OptStream.map
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    apply scons_monoN
    sorry
    -- grind

@[partial_fixpoint_monotone]
theorem stail_mono β α [PartialOrder β] (f : β → OptStream α) :
  monotone f →
  monotone (λ x => OptStream.stail (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    cases n; simp [CoIndN.le]
    have hs : (f t1) ⊑ (f t2) := by grind [monotone]
    generalize f t1 = s1, f t2 = s2 at hs
    unfold OptStream.stail
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    sorry
    -- grind [CoInd.leN_le]

def s3? : OptStream Nat :=
  (.scons 0 $ .scons 1 $ .stail s3?)
partial_fixpoint

def s3 : Stream Nat :=
  OptStream.toStream s3? <| by
    apply OptStream.IsInf.coinduct (fun xs? =>
      xs? = s3? ∨ xs? = (.scons 1 $ .stail s3?) ∨ xs? = (.stail s3?)
    )
    · rintro xs? (rfl|rfl|rfl)
      · refine ⟨0, ?_⟩
        simp only [exists_eq_or_imp, exists_eq_left]
        right; left
        conv => lhs; unfold s3?
      · refine ⟨1, s3?.stail, ?_⟩
        simp
      · refine ⟨1, s3?.stail, ?_⟩
        simp only [or_true, true_and]
        conv => lhs; unfold s3?
        rfl
    · simp


theorem s3_head :
  Stream.shead s3 = 0 := by
    unfold s3 s3?; rfl

def s3' : OptStream Nat :=
  .stail s3'
partial_fixpoint

def OptStream.filter (P : α → Bool) (xs : OptStream α) : OptStream α :=
  match xs.unfold with
  | .scons x (xs : OptStream _) =>
      let xs := filter P xs
      if P x then .scons x xs else xs
  | .none => .none
partial_fixpoint

def OptStream.nats : OptStream Nat :=
  .scons 0 <| .map (· + 1) nats
partial_fixpoint

@[simp, grind =]
theorem OptStream.map_map (xs : OptStream α) (f : α → β) (g : β → γ) :
    (xs.map f).map g = xs.map (g <| f ·) := by
  sorry

def Stream.nats : Stream Nat :=
  OptStream.nats.toStream <| by
    unfold OptStream.nats
    apply OptStream.IsInf.coinduct (fun xs? =>
      ∃ n,
        xs? = .scons n (OptStream.nats.map (· + (n + 1)))
        ∨ xs? = OptStream.nats.map (· + (n + 1))
    )
    · rintro xs? ⟨n, (rfl|rfl)⟩
      · exact ⟨n, OptStream.map (fun x => x + (n + 1)) OptStream.nats, ⟨⟨n, Or.inr rfl⟩, rfl⟩⟩
      · refine ⟨n+1, OptStream.map (fun x => x + (n + 2)) OptStream.nats, ⟨⟨n+1, Or.inr rfl⟩, ?_⟩⟩
        conv => lhs; unfold OptStream.nats
        grind
    · exact ⟨0, Or.inl rfl⟩

def OptStream.take (xs : OptStream α) : Nat → List (Option α)
  | 0 => []
  | n+1 => xs.shead? :: xs.stail.take n

def Stream.take (xs : Stream α) : Nat → List α
  | 0 => []
  | n+1 => xs.shead :: xs.stail.take n


#eval OptStream.nats.take 1

-- -- test universe polymorphism
-- def univpoly : Stream PUnit.{u + 1} := .scons ⟨⟩ univpoly
-- partial_fixpoint
