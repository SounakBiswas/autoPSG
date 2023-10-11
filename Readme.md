## Introduction

This is an attempt to classify PSG (projective symmetry groups), corresponding to a given space group and an IGG. The idea is to use symbolic manipulations to automate the steps required to achieve such a classification. This project is under construction. The broad workflow plan is as follows:
- [x] set up symmetry group inputs: in terms of a finite presentation and action on sites and sublattices.
- [x] solve for IGG z2 
- [ ] solve for IGG u1
- [ ] solve for IGG su2
- [ ] bosons (?)
- [ ] input for lattice bonds
- [ ] calculate ansatzes 


## Methods and Software 

Everything is written in the Wolfram Language (WL) so far. The Wolfram Language engine is free (though not open-source), and can be used with Jupyter Notebook, though the experience is nowhere close to Mathematica Notebook. The work so far uses almost no use of  *Computer Algebra*, and makes no use of the the WL's exceptional capabilities of dealing with special functions or Mathematical equations. However, it does make use of WL's powerful pattern matching functions. This, I optimistically believe, can be later translated to an open-source language like *Haskell*.   


## Demo
Demos to be added in form of notebook screenshots here.

## Documentation 
 Ideally tex file in the same folder --- to later become draft. 

The Code has almost no comments, must be rectified as soon as possible.