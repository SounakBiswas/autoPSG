(* ::Package:: *)

BeginPackage["psgSolver`symmetryG`"]
Remove["psgSolver`symmetryG`*"]
(*Needs["SU2Utils"]*)
(*List of Symmetries*)
Needs["psgSolver`definitions`"]

symGenSet={Tx, Ty, Px, Py, Pxy};
(*symGenSet={Tx, Ty, Tz,ga,gb,gc};*)
slatList={None};
(*slatList={\[Alpha],\[Beta]}*)
(*slatList={\[Alpha],\[Beta], \[Gamma], \[Delta]}*)


(*Coordinates*)
x; y; z;

(*Set of Relations*)
SGset::usage = "set of Symmetry Group Relations";
nrel::usage = "integer, number of etas to start with";
initSG::usage="calculate inverses, pad for missing dimensions and sublattices"
makeInverse::usage="dfsd"
noBasis;
twoDim;
defaultCoords;
defaultCoordsPattern;


Begin["Private`"]


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

noBasis=True;
twoDim =True;


(*Define and Transformations, Inverses, Relators*)
Tx [{x_, y_}] := {x - 1, y};
Ty [{x_, y_}] := {x, y - 1};
Px [{x_, y_}] := {-x, y};
Py [{x_, y_}] := {x, -y};
Pxy[{x_, y_}] := {y, x};


(*Tx[{x_,y_,z_,s_}]={x-1,y,z,s}
Ty[{x_,y_,z_,s_}]={x,y-1,z,s}
Tz[{x_,y_,z_,s_}]={x,y,z-1,s}
ga[{x_,y_,z_,\[Alpha]}]={-x,-y-1,z,\[Delta]}
ga[{x_,y_,z_,\[Beta]}]={-x-1,-y-1,z+1,\[Gamma]}
ga[{x_,y_,z_,\[Gamma]}]= {-x-1, -y-1,z,\[Beta]}
ga[{x_,y_,z_,\[Delta]}]={-x,-y-1,z+1,\[Alpha]}

gb[{x_,y_,z_,\[Alpha]}]={-x-1,y,-z,\[Gamma]}
gb[{x_,y_,z_,\[Beta]}]={-x-1,y,-z,\[Delta]}
gb[{x_,y_,z_,\[Gamma]}]={-x-1,y+1,-z,\[Alpha]}
gb[{x_,y_,z_,\[Delta]}]={-x-1,y+1,-z-1,\[Beta]}

gc[{x_,y_,z_,\[Alpha]}]={z,x,y,\[Alpha]}
gc[{x_,y_,z_,\[Beta]}]= {z,x,y,\[Gamma]}
gc[{x_,y_,z_,\[Gamma]}]= {z,x,y,\[Delta]}
gc[{x_,y_,z_,\[Delta]}]={z,x,y,\[Beta]}*)


SGset = {gmult[Inv[Tx], Inv[Ty], Tx, Ty], 
         gmult[Inv[Px], Inv[Ty], Px, Ty],
         gmult[Inv[Px], Tx, Px, Tx],
         gmult[Inv[Py], Inv[Tx], Py, Tx],
         gmult[Inv[Py], Ty, Py, Ty],
         gmult[Inv[Pxy], Inv[Tx], Pxy, Ty],
         (*gmult[Pxy, Inv[Tx], Pxy, Ty],*)
         gmult[Inv[Pxy], Inv[Ty], Pxy, Tx],
         (*gmult[Pxy, Inv[Ty], Pxy, Tx],*)
         gmult[Inv[Py],Pxy,Px,Pxy],
         gmult[Inv[Px],Inv[Py],Px,Py],
         gmult[Py, Py],
         gmult[Px, Px],
         gmult[Pxy, Pxy]
         };
(*SGset= {gmult[Inv[Tx], Inv[Ty], Tx, Ty],
gmult[Inv[Ty], Inv[Tz], Ty, Tz],
gmult[Inv[Tz], Inv[Ty], Ty, Tz]
};*)

nrel=Length[SGset]
End[]
EndPackage[]

