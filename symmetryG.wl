(* ::Package:: *)

BeginPackage["psgSolver`symmetryG`"]
Remove["psgSolver`symmetryG`*"]
(*Needs["SU2Utils"]*)
(*List of Symmetries*)
Needs["psgSolver`definitions`"]



(*Coordinates*)
x; y; z;

(*Set of Relations*)
SGSet::usage = "set of Symmetry Group Relations";
nrel::usage = "integer, number of etas to start with";
initSG::usage="calculate inverses, pad for missing dimensions and sublattices"
makeInverse::usage="dfsd"
noBasis;
twoDim;
defaultCoords;
defaultCoordsPattern;

<<"psgSolver/input.wl"

Begin["Private`"]

formatInputRelator[x_] :=
Module[{y},
   y = x //. {z_ /; MemberQ[symGenSet, z] -> z,
      Plus[z_ /; MemberQ[symGenSet, z], -1] -> Inv[z]};
   gmult @@ y
];


addZ[T_]:= (T[{x_,y_,z_}]:=Append[T[{x,y}],z];);
addSlat[T_]:= (T[{x_,y_,z_,slat_}]:=Append[T[{x,y,z}],slat];);

initSG[]:= (
If[twoDim,
   (addZ[#]&/@symGenSet;
   defaultCoords=Sequence[x, y, None];
   defaultCoordsPattern=Sequence[x_,y_,None];
   ),
   (defaultCoords=Sequence[x,y,z];
   defaultCoordsPattern=Sequence[x_,y_,z_];)
  ];
  If[noBasis,
     addSlat[#]&/@symGenSet;
  ];
  makeInverse[#]&/@ (Distribute[{symGenSet,slatList},List]);
)

makeInverse[{A_,slat_}] := Module[
{coord1, coord2, func, xp, yp, zp},
   coord1 = {x, y, z,slat};
   coord2 = A[coord1];
   SetDelayed@@{func[(m_: 1) (c : x | y | z) + k_: 0, c2_] ,
    Switch[c,
     x,
     (xp = (1/m)*(c2 - k);),
     y,
     (yp = (1/m)*(c2 - k);),
     z,
     (zp = (1/m)*(c2 - k);)
     ]};
   MapThread[func, {Take[coord2,3], Take[coord1,3]}];
   SetDelayed@@{Inv[A][{x_, y_, z_,coord2[[4]]}], {xp, yp, zp,slat}};
];

(***init***)

initSG[];
SGSet=formatInputRelator/@inputRelators;

nrel=Length[SGSet]
End[]
EndPackage[]

