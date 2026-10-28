// Object definition, private records, and the Spec/Proj input boundary.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

declare type FinFlatCov;
declare attributes FinFlatCov:
    Degree, Model, CoefficientRing, ProjectiveBase, Embedding, Twisted,
    StructureConstants, Discriminant, DefiningPolynomials, UnderlyingScheme, _Data;

FFCPresentation := recformat<
    Kind, Polynomials, Flatness
>;

FFCBundle := recformat<
    Variables, Equations, Rows, Twist,
    Algebra, Tschirnhausen, FirstSyzygy
>;

FFCAlgebra := recformat<
    Matrices, Traces, Pairing, TraceDiscriminant,
    Associative, BasisChange, DiscriminantRecipe, Pending
>;

FFCGeometry := recformat<
    Ambient, ModelScheme, ModelAmbient, AlgebraEquations,
    CoxModel, CoxAlgebra, AffineScheme, ScrollEmbedding,
    LocalEquations
>;

FFCResolution := recformat<
    Maps, Weights, Exact, Betti,
    FirstSyzygies, Slices, Brackets, Pending
>;

FFCResolvents := recformat<
    Standard, Conjectural, Minors, Verified,
    SourceDegree, Normalization, BasisChange, Inclusion,
    DiscriminantFactor, Certificate, DiscriminantVerified, Atlas,
    Pending, PendingConjectural
>;

FFCData := recformat<Presentation, Bundle, Algebra, Geometry, Resolution, Resolvents>;

function FFCNewCover()
    C := New(FinFlatCov);
    C`_Data := rec<FFCData |
        Presentation := rec<FFCPresentation | >,
        Bundle       := rec<FFCBundle | >,
        Algebra      := rec<FFCAlgebra | >,
        Geometry     := rec<FFCGeometry | >,
        Resolution   := rec<FFCResolution | >,
        Resolvents   := rec<FFCResolvents | >
    >;
    return C;
end function;
