// Complete native regression suite. Run from the package directory.
AttachSpec("spec");
load "tests/model_accessor.m";
load "tests/laziness.m";
load "tests/presentation_selection.m";
load "tests/projective_weights.m";
load "tests/names.m";
load "tests/projective_prime_fibre.m";
load "tests/geometry_and_fibres.m";
load "tests/resolutions.m";
load "tests/twisted_actions.m";
load "tests/monogenic.m";
load "tests/resolvents.m";
load "tests/conjectural_resolvent.m";
load "tests/fractional_actions.m";
print "All native Magma tests passed.";
quit;
