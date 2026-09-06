
### Prima Versione
Prima versione : Delete e Update separati. Essendo molto simili e dovendo definire due volte tutti i lemmi necessari per le dimostrazioni, abbiamo pensato di creare un unica relazione che catturi entrambe, sfruttando la definizione a lista di contesto. Quindi nel Delete semplicemente si passa un contesto vuoto ([]), mentre nell'update un singoletto ([ A ]). 

### Seconda versione
Andando avanti nel deadlock freedom, è stato riscontrato il problema del case.
```
case→thread : ∀{Γ A B Δ Δ` P Q} 
      → (U : Update (A & B) [ A ] Γ Δ) 
      → (U` : Update (A & B) [ B ] Γ Δ`) 
      → Thread (case U U` P Q)​
```

ho notato che Agda, giustamente, richiede le prove dei casi misti:

```
case→thread here (next U`) = {!   !}​
case→thread (next U) here = {!   !}​
```

casi che in realtà semanticamente errati. Cercando di capire l’origine del problema, credo sia scaturito dal fatto che nella definizione di Proc le due ipotesi Update sono scollegate, ovvero non è detto che debbano agire sullo stesso elemento del contesto.

Dunque, se ipotizzassimo un contesto `(A&B) :: (A&B) :: []`​ , il caso 
```
case→thread here (next U`) = {!   !}​
```
è, per Agda, corretto, in quanto il primo Update agisce sull’elemento in testa, mentre il secondo sul secondo elemento.
Sarebbe come dire che il ramo sinistro del case consuma la prima risorsa, il ramo destro consuma la seconda risorsa, il che è errato.

La seconda versione è risultata corretta

### Terza versione

La terza versione riguarda l'aggiunta dei tipi all , ex , client, server var e rav per analizzare il modello completo (a partire dalla verisone unificata)


