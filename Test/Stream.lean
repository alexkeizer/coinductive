import Coinductive

namespace Stream
open Coinductive Lean.Order

inductive StreamF (α : Type w) (Stream : Type w) : Type w where
  | snil
  | scons (x : α) (tl : Thunk Stream)

inductive StreamF.In (α : Type u) : Type u where
  | snil
  | scons (x : α)

@[simp, grind =] theorem Thunk.get_mk (fn : Unit → α) : Thunk.get ⟨fn⟩ = fn () := by rfl

@[simp] theorem Thunk.mk_get (x : Thunk α) : Thunk.mk (fun _ => x.get) = x := by
  simp [Thunk.ext_iff]

instance (α : Type u) : PF (StreamF α) where
  P := ⟨StreamF.In α, fun
    | .snil => PEmpty
    | .scons _ => PUnit⟩
  unpack
    | .snil => .obj (.snil) nofun
    | .scons hd tl => .obj (.scons hd) λ _ => tl.get
  pack
    | .obj (.snil) _ => .snil
    | .obj (.scons hd) tl => .scons hd (tl ⟨⟩)
  unpack_pack := by rintro _ (_|_) <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev Stream (α : Type u) : Type u := CoInd (StreamF α)

def Stream.fold (t : StreamF α (Stream α)) : Stream α := CoInd.fold _ t
def Stream.snil {α : Type u} : Stream α := Stream.fold (.snil)
def Stream.scons {α : Type u} (hd : α) (tl : Thunk (Stream α)) : Stream α := Stream.fold (.scons hd tl)

@[simp]
theorem snil_approx_1 α n :
  (Stream.snil (α:=α)).approx (n + 1) = StreamF.snil := by
    simp [Stream.snil, Stream.fold, CoInd.fold, PF.map, PF.pack]

@[simp]
theorem scons_approx_1 α i (s : Stream α) n :
  (Stream.scons i s).approx (n + 1) = StreamF.scons i (Thunk.mk (fun _ => s.approx n)) := by
    simp [Stream.scons, Stream.fold, CoInd.fold, PF.map, PF.pack]

@[simp]
theorem unfold_snil α :
  CoInd.unfold _ Stream.snil = StreamF.snil (α:=α) := by
    simp [Stream.snil, Stream.fold]

@[simp]
theorem unfold_scons α (i : α) s:
  CoInd.unfold _ (Stream.scons i s) = StreamF.scons i s := by
    simp [Stream.scons, Stream.fold]

instance : Inhabited (StreamF α PUnit) where default := .snil

@[simp]
theorem Stream.bot_eq α :
  CoInd.bot (StreamF α) = Stream.snil := by
    rw [CoInd.bot_eq]
    simp [PF.map, PF.pack, Stream.snil, Stream.fold]


theorem Stream.le_unfold α (s1 s2 : Stream α) :
  (s1 ⊑ s2) = (s1 = .snil ∨
    ∃ i s1' s2', s1 = .scons i s1' ∧ s2 = .scons i s2' ∧ s1'.get ⊑ s2'.get) := by
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

theorem scons_monoN α i (s1 s2 : Thunk (Stream α)) n :
  CoIndN.le _ (s1.get.approx n) (s2.get.approx n) →
  CoIndN.le _ ((Stream.scons i s1).approx (n + 1))
    ((Stream.scons i s2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

instance [PartialOrder α] : PartialOrder (Thunk α) where
  rel x y       := x.get ⊑ y.get
  rel_refl      := by grind [PartialOrder.rel_refl]
  rel_trans     := by grind [PartialOrder.rel_trans]
  rel_antisymm  := by grind [PartialOrder.rel_antisymm, Thunk.ext]

@[partial_fixpoint_monotone]
theorem scons_mono β α [PartialOrder β] i (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.scons i (Thunk.mk fun _ => f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply scons_monoN
    grind [CoInd.leN_le, monotone]

def Stream.map {α} (f : α → β) (s : Stream α) : Stream β :=
  match s.unfold with
  | .snil => .snil
  | .scons hd tl => .scons (f hd) (Stream.map f tl.get)
partial_fixpoint

@[partial_fixpoint_monotone]
theorem map_mono α β γ [PartialOrder γ] (f : α → β) (g : γ → Stream α) :
  monotone g →
  monotone (λ x => Stream.map f (g x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hs : (g t1) ⊑ (g t2) := by grind [monotone]
    generalize g t1 = s1, g t2 = s2 at hs
    induction n generalizing s1 s2; simp [CoIndN.le]
    unfold Stream.map
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    stop
    apply scons_monoN
    grind


def Stream.stail {α} (s : Stream α) : Stream α :=
  match s.unfold with
  | .snil => .snil
  | .scons _ tl => tl.get

@[partial_fixpoint_monotone]
theorem stail_mono β α [PartialOrder β] (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.stail (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    cases n; simp [CoIndN.le]
    have hs : (f t1) ⊑ (f t2) := by grind [monotone]
    generalize f t1 = s1, f t2 = s2 at hs
    unfold Stream.stail
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    grind [CoInd.leN_le]

def Stream.shead {α} (s : Stream α) : Option α :=
  match s.unfold with
  | .snil => none
  | .scons hd _ => some hd

def s3 : Stream Nat :=
  .scons 0 $ Stream.scons 1 $ Stream.stail s3
partial_fixpoint

theorem s3_head :
  Stream.shead s3 = some 0 := by
    unfold s3
    simp [Stream.shead]

def s3' : Stream Nat :=
  .stail s3'
partial_fixpoint

-- test universe polymorphism
def univpoly : Stream PUnit.{u + 1} := .scons ⟨⟩ univpoly
partial_fixpoint

def Stream.nats (n := 0) : Stream Nat :=
  scons n (nats (n+1))
partial_fixpoint

def Stream.take (xs : Stream α) : Nat → List (Option α)
  | 0 => []
  | n+1 => xs.shead :: xs.stail.take n

def Stream.get (xs : Stream α) : Nat → Option α
  | 0  => xs.shead
  | n+1 => xs.stail.get n

#time
  #eval Stream.nats.get 10

#time
  #eval Stream.nats.get 1000

#time
  #eval Stream.nats.get 2000

#time
  #eval Stream.nats.get 1000
