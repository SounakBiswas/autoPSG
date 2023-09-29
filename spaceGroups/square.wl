slatList={None}
twoDim=True
noBasis=True
symGenSet={Tx, Ty, Px, Py, Pxy};

Tx [{x_, y_}] := {x - 1, y};
Ty [{x_, y_}] := {x, y - 1};
Px [{x_, y_}] := {-x, y};
Py [{x_, y_}] := {x, -y};
Pxy[{x_, y_}] := {y, x};

inputRelators = {
         {Tx-1, Ty-1, Tx, Ty}, 
         {Px-1, Ty-1, Px, Ty},
         {Px-1, Tx, Px, Tx},
         {Py-1, Tx-1, Py, Tx},
         {Py-1, Ty, Py, Ty},
         {Pxy-1, Tx-1, Pxy, Ty},
         {Pxy-1, Ty-1, Pxy, Tx},
         {Py-1,Pxy,Px,Pxy},
         {Px-1,Py-1,Px,Py},
         {Py, Py},
         {Px, Px},
         {Pxy, Pxy}
         };
