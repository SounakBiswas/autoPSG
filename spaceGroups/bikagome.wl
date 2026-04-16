twoDim=True
noBasis=False
symGenSet={T1, T2, C3, \[ScriptCapitalI], \[Sigma],\[ScriptCapitalT]};

slatList={\[ScriptA],\[ScriptB],\[ScriptC],\[ScriptD],\[ScriptE],\[ScriptF]};

C3slat[s_]=Switch[s,\[ScriptA],\[ScriptC],\[ScriptB],\[ScriptA],\[ScriptC],\[ScriptB],\[ScriptD],\[ScriptE],\[ScriptE],\[ScriptF],\[ScriptF],\[ScriptD]];
Islat[s_]=Switch[s,\[ScriptA],\[ScriptF],\[ScriptB],\[ScriptE],\[ScriptC],\[ScriptD],\[ScriptD],\[ScriptC],\[ScriptE],\[ScriptB],\[ScriptF],\[ScriptA]];

Sslat[s_]=Switch[s,\[ScriptA],\[ScriptB],\[ScriptB],\[ScriptA],\[ScriptC],\[ScriptC],\[ScriptD],\[ScriptD],\[ScriptE],\[ScriptF],\[ScriptF],\[ScriptE]];

T1 [{x_, y_,s_}] := {x + 1, y,s};
T2 [{x_, y_,s_}] := {x, y + 1,s};
C3[{x_, y_,s_}] := { -x-y,x,C3slat[s]};
\[ScriptCapitalI][{x_, y_,s_}] := {-x, -y,Islat[s]};
\[Sigma][{x_, y_,s_}] := {y, x,Sslat[s]};
\[ScriptCapitalT][{x_,y_,s_}]:={x,y,s};

inputRelators = {
         {T1-1, T2-1, T1, T2}, 
         {T2,C3-1,T1,C3},
         {T1,C3,T1,C3-1,T2-1},
         {\[Sigma]-1,T2-1,\[Sigma],T1},
         {\[Sigma]-1,T1-1,\[Sigma],T2},
         {T1,\[ScriptCapitalI]-1,T1,\[ScriptCapitalI]},
         {T2,\[ScriptCapitalI]-1,T2,\[ScriptCapitalI]},
         {C3,C3,C3},
         {\[Sigma],\[Sigma]},
         {\[ScriptCapitalI],\[ScriptCapitalI]},
         {\[Sigma]-1,C3,\[Sigma],C3},
         {\[Sigma]-1,\[ScriptCapitalI]-1,\[Sigma],\[ScriptCapitalI]},
         {C3-1,\[ScriptCapitalI]-1,C3,\[ScriptCapitalI]},
         {\[ScriptCapitalT],\[ScriptCapitalT]},
         {\[ScriptCapitalT]-1, T1-1,\[ScriptCapitalT],T1},
         {\[ScriptCapitalT]-1, T2-1,\[ScriptCapitalT],T2},
         {\[ScriptCapitalT]-1, C3-1,\[ScriptCapitalT],C3},
         {\[ScriptCapitalT]-1, \[ScriptCapitalI]-1,\[ScriptCapitalT],\[ScriptCapitalI]},
         {\[ScriptCapitalT]-1, \[Sigma]-1,\[ScriptCapitalT],\[Sigma]}
         };
RelatorNames={xy,C3T2,C3T1,\[Sigma]T2,\[Sigma]T1,T1\[ScriptCapitalI],T2\[ScriptCapitalI],C3,\[Sigma],\[ScriptCapitalI],\[Sigma]C3,\[Sigma]\[ScriptCapitalI],C3\[ScriptCapitalI],\[ScriptCapitalT],\[ScriptCapitalT]T1,\[ScriptCapitalT]T2,\[ScriptCapitalT]C3,\[ScriptCapitalT]\[ScriptCapitalI],\[ScriptCapitalT]\[Sigma]}

