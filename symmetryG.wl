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

(*makeInverse[{A_,slat_}] := Module[
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
extractCoeffs[rp_] := Module[{xp, ax, ay, az, ak},
   xp = ExpandAll[rp];
   ax = Cases[xp, Times[(p_ : 1 ), x] ->  p, {0, 1} ];
   ay = Cases[xp, Times[(p_ : 1 ), y ] -> p, {0, 1}];
   az = Cases[xp, Times[(p_ : 1 ), z ] -> p, {0, 1}];
   If[ax === {}, ax = 0, ax = ax[[1]]];
   If[ay === {}, ay = 0, ay = ay[[1]]];
   If[az === {}, az = 0, az = az[[1]]];
   ak=xp-ax x-ay y-az z;
   {ax, ay, az, ak}
   ];*)
extractCoeffs[rp_] := Module[{xp, cxp,ax, ay, az, ak},
   xp = ExpandAll[rp];
   cxp = Cases[xp, (Verbatim[Plus][a___] | Times[a__] | x_?AtomQ) -> a, {0}] ;
   ax = Cases[cxp, Times[(p_ : 1), x] -> p, {1}];
   ay = Cases[cxp, Times[(p_: 1), y] -> p, {1}];
   az = Cases[cxp, Times[(p_ : 1), z] -> p, {1}];
   If[ax === {}, ax = 0, ax = ax[[1]]];
   If[ay === {}, ay = 0, ay = ay[[1]]];
   If[az === {}, az = 0, az = az[[1]]];
   ak = rp - ax x - ay y - az z;
   {ax, ay, az, ak}
   ];
makeInverse[{A_, slat_}] := 
Module[{coord1, coord2, func, rpp},
   coord1 = {x, y, z, slat};
   coord2 = A[coord1];
   func[{xp_, yp_, zp_}] :=
   Module[{m, mI, rp, a, b, c},
      rp = {Null, Null, Null};
      a = extractCoeffs[xp];
      b = extractCoeffs[yp];
      c = extractCoeffs[zp];
      m = {Take[a, 3], Take[b, 3], Take[c, 3]};
      mI = Inverse[m];
      rp = mI . {x - a[[4]], y - b[[4]], z - c[[4]]};
      rp
   ];
   rpp = func[Take[coord2, 3]];
   SetDelayed @@ {Inv[A][{x_, y_, z_, coord2[[4]]}], {rpp[[1]], 
   rpp[[2]], rpp[[3]], slat}};
];


(***init***)

initSG[];
SGSet=formatInputRelator/@inputRelators;

nrel=Length[SGSet]
End[] 

EndPackage[]

