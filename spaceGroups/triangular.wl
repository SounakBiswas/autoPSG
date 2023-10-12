slatList={None}
twoDim=True
noBasis=True
symGenSet={Tx, Ty, R, Pxy};

Tx [{x_, y_}] := {x + 1, y};
Ty [{x_, y_}] := {x, y + 1};
Pxy[{x_, y_}] := {y, x};
R[{x_,y_}] := {x-y,x};

inputRelators = {
         {Tx-1, Ty-1, Tx, Ty}, 
         {Pxy-1, Tx-1, Pxy, Ty},
         {R-1, Ty-1, R, Ty, Tx},
         {Pxy,Pxy},
         {R,R, R, R, R,R},
         {R,Pxy,R,Pxy}
         };
