# Finite flat covers of degree 5

This is a Jupyter notebook of a talk given at the ICEAGE 2026 conference in Lleida. 

- The main Jupyter notebook file is `26-10_Quintics.ipynb`. 
- The directory `finite-flat-covers/` provides intrinsics for working with finite flat covers (after Casnati--Ekedahl, Bhargava, Wood, Fisher--Radicevic). 

## Generative AI usage

The code in the `finite-flat-covers/` directory was written with an AI coding assistant. 

I supplied the assistant with many old scripts (human-written code-slop) of mine performing these computations in many settings. In particular the "scratch work" for previous papers of mine (particularly my paper on 12-congruences and my PhD thesis) performing minimisation of degree 2, 3, 4, and 5 covers over 2-variable function fields. I also suggested the agent include work of Fisher--Radicevic so that we can use this for arbitrary degree covers. The AI was also prompted with various works of Bhargava, Wood, Fisher--Radicevic, and Radicevic. 

The output is some "unified" code which gives helper functions for such minimisation calculations, in rather greater generality than my original scripts. 

## Caveats

While I believe (and have tested) much of the functionality in `finite-flat-covers/` it should not be treated as rigorously tested and working at this stage. 

Any computations made using this package should be sanity checked and proved by a direct arguement. 
