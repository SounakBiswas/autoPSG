(*bieri unit vecs*)
twoDim=True
noBasis=False
symGenSet={T1, T2, C6, \[Sigma]};

slatList={\[ScriptA],\[ScriptB],\[ScriptC]}

xtok = {{1, 1/Sqrt[3]}, {0, 2/Sqrt[3]}};
ktox = {{1, -1/2}, {0, Sqrt[3]/2}};
C6m = {{Cos[Pi/3], -Sin[Pi/3]}, {Sin[Pi/3], Cos[Pi/3]}};
\[Sigma]m = {{Cos[2 Pi/3], Sin[2 Pi/3]}, {Sin[2 Pi/3], -Cos[2 Pi/3]}};
Mat[C6] = xtok . C6m . ktox;
Mat[\[Sigma]] = xtok . \[Sigma]m . ktox;

c2slat[{1, 0}] = \[ScriptA];
c2slat[{1, 1}] = \[ScriptB];
c2slat[{0, 1}] = \[ScriptC];
slat2c[\[ScriptA]] = {1, 0};
slat2c[\[ScriptB]] = {1, 1};
slat2c[\[ScriptC]] = {0, 1};
transform[{x_, y_}] := {Quotient[x, 2], Quotient[y, 2], 
   c2slat[{Mod[x, 2], Mod[y, 2]}]};
Itransform[{x_, y_, s_}] := 2*{x, y} + slat2c[s];

addRelation[{T_,s_}]:=(T[{x_,y_,s}]:= FullSimplify[transform[Mat[T].Itransform[{x,y,s}]],Assumptions->{x \[Element] Integers, y \[Element] Integers}];)


T1 [{x_, y_,s_}] := {x + 1, y,s};
T2 [{x_, y_,s_}] := {x, y + 1,s};

addRelation[#]&/@(Distribute[{{C6,\[Sigma]},slatList},List]);




inputRelators = {
         {T1-1, T2-1, T1, T2}, 
         {C6-1, T1, C6, T2},
         {T1-1,T2-1,C6-1,T2,C6},
         {\[Sigma]-1, T1-1, \[Sigma], T2},
         {\[Sigma],\[Sigma]},
         {C6,C6, C6, C6, C6,C6},
         {C6,\[Sigma],C6,\[Sigma]}
         };
RelatorNames={xy,C6T1,C6T2,\[Sigma]T1,\[Sigma],C6,\[Sigma]C6}
