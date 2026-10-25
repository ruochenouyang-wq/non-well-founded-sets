import EquivariantEmbeddingExtensions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure CodedMaskIsomorphism (base : BaseCollection s) {w : U}
    (A B : CodedMaskAction base w) (f : U) where
  iso : MembershipIsoCode s A.domain B.domain f
  intertwines : ∀ i x y X Y, CodedRelation s (A.maps i) x y →
    CodedRelation s f x X → CodedRelation s f y Y → CodedRelation s (B.maps i) X Y

def CodedMaskIsomorphism.toEmbedding (base : BaseCollection s) {w f : U}
    {A B : CodedMaskAction base w} (I : CodedMaskIsomorphism base A B f) :
    CodedMaskEmbedding base A B f :=
  ⟨B.domain, B.transitive, fun _ h => h, I.iso, I.intertwines⟩

theorem coded_mask_isomorphism_inverse (base : BaseCollection s) {w f : U}
    {A B : CodedMaskAction base w} (I : CodedMaskIsomorphism base A B f) :
    ∃ g, Nonempty (CodedMaskIsomorphism base B A g) ∧
      ∀ x X, CodedRelation s g X x ↔ CodedRelation s f x X := by
  obtain ⟨g, hg, hgi, hgr, hgv⟩ := coded_bijection_inverse base I.iso.1 I.iso.2.1 I.iso.2.2.1
  have hmem : MembershipIsoCode s B.domain A.domain g := by
    refine ⟨hg, hgi, hgr, ?_⟩
    intro X Y x y hx hy
    exact (I.iso.2.2.2 x y X Y ((hgv X x).mp hx) ((hgv Y y).mp hy)).symm
  refine ⟨g, ⟨⟨hmem, ?_⟩⟩, fun x X => hgv X x⟩
  intro i X Y x y hXY hx hy
  exact (coded_mask_embedding_action_iff base (I.toEmbedding base) i
    ((hgv X x).mp hx) ((hgv Y y).mp hy)).mpr hXY

/-- Compose two actual coded embeddings; the resulting transitive range is
    constructed as a source image, rather than assumed as external data. -/
theorem coded_mask_embeddings_compose (base : BaseCollection s) {w f g : U}
    {A B C : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (F : CodedMaskEmbedding base B C g) :
    ∃ h, Nonempty (CodedMaskEmbedding base A C h) ∧
      ∀ x Z, CodedRelation s h x Z ↔ ∃ X, CodedRelation s f x X ∧ CodedRelation s g X Z := by
  obtain ⟨h, hh, hhr⟩ := coded_functions_compose base E.iso.1 F.iso.1
    (fun _ _ hx => coded_mask_embedding_value base E hx)
  obtain ⟨T, hT⟩ := coded_image_set_exists base h A.domain
  have hi : InjectiveCode s h := by
    intro x y Z hx hy
    obtain ⟨X, hxX, hXZ⟩ := (hhr x Z).mp hx
    obtain ⟨Y, hyY, hYZ⟩ := (hhr y Z).mp hy
    have hXY := F.iso.2.1 X Y Z hXZ hYZ
    exact E.iso.2.1 x y Y (hXY ▸ hxX) hyY
  have ht : TransitiveCode s T := by
    intro Z hZ z hzZ
    obtain ⟨x, hx, hxZ⟩ := (hT Z).mp hZ
    obtain ⟨X, hxX, hXZ⟩ := (hhr x Z).mp hxZ
    have hZr := (F.iso.2.2.1 Z).mpr ⟨X, coded_mask_embedding_value base E hxX, hXZ⟩
    obtain ⟨Y, _, hYz⟩ := (F.iso.2.2.1 z).mp (F.transitive Z hZr z hzZ)
    have hYX := (F.iso.2.2.2 X Y Z z hXZ hYz).mpr hzZ
    have hXr := (E.iso.2.2.1 X).mpr ⟨x, hx, hxX⟩
    obtain ⟨y, hy, hyY⟩ := (E.iso.2.2.1 Y).mp (E.transitive X hXr Y hYX)
    exact (hT z).mpr ⟨y, hy, (hhr y z).mpr ⟨Y, hyY, hYz⟩⟩
  have hTC : Subset s T C.domain := by
    intro Z hZ
    obtain ⟨x, _, hxZ⟩ := (hT Z).mp hZ
    obtain ⟨X, _, hXZ⟩ := (hhr x Z).mp hxZ
    exact coded_mask_embedding_value base F hXZ
  have hmem : MembershipIsoCode s A.domain T h := by
    refine ⟨hh, hi, hT, ?_⟩
    intro x y X Y hx hy
    obtain ⟨xx, hxx, hxxX⟩ := (hhr x X).mp hx
    obtain ⟨yy, hyy, hyyY⟩ := (hhr y Y).mp hy
    exact (E.iso.2.2.2 x y xx yy hxx hyy).trans (F.iso.2.2.2 xx yy X Y hxxX hyyY)
  refine ⟨h, ⟨⟨T, ht, hTC, hmem, ?_⟩⟩, hhr⟩
  intro i x y X Y hxy hx hy
  obtain ⟨xx, hxx, hxxX⟩ := (hhr x X).mp hx
  obtain ⟨yy, hyy, hyyY⟩ := (hhr y Y).mp hy
  exact F.intertwines i xx yy X Y (E.intertwines i x y xx yy hxy hxx hyy) hxxX hyyY

theorem coded_mask_isomorphisms_compose (base : BaseCollection s) {w f g : U}
    {A B C : CodedMaskAction base w} (I : CodedMaskIsomorphism base A B f)
    (K : CodedMaskIsomorphism base B C g) :
    ∃ h, Nonempty (CodedMaskIsomorphism base A C h) ∧
      ∀ x Z, CodedRelation s h x Z ↔ ∃ X, CodedRelation s f x X ∧ CodedRelation s g X Z := by
  obtain ⟨h, ⟨E⟩, hr⟩ := coded_mask_embeddings_compose base (I.toEmbedding base) (K.toEmbedding base)
  have hdom : E.range = C.domain := by
    apply base.extensional
    intro Z
    constructor
    · exact E.subset Z
    · intro hZ
      obtain ⟨Y, hY, hYZ⟩ := (K.iso.2.2.1 Z).mp hZ
      obtain ⟨x, hx, hxY⟩ := (I.iso.2.2.1 Y).mp hY
      exact (E.iso.2.2.1 Z).mpr ⟨x, hx, (hr x Z).mpr ⟨Y, hxY, hYZ⟩⟩
  exact ⟨h, ⟨⟨hdom ▸ E.iso, E.intertwines⟩⟩, hr⟩

#print axioms coded_mask_embeddings_compose
#print axioms coded_mask_isomorphism_inverse
end FullBridge
