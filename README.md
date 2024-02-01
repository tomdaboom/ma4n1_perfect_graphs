# For Damiano
The `perfect_graphs` directory has 3 elements:
- `MASTER_FILE.lean`, which contains all the main definitions, lemmas and theorems,
- `graph_redefinition.lean`, which contains a more convenient redefinition of graphs for most combinatorial applications, and
- `OLD`, which is another directory containing other `.lean` files we used while we were working on the project. We strongly advise that you don't look in there - the vast majority of content there has been copied to the master file where needed, and the rest is unused.

Also, we have been using LEAN live (LEAN's online editor) and so have not been updating Mathlib - there may be several problems if you try and run this without updating Mathlib by yourself.

# ma4n1_perfect_graphs

Things we already have :
- fromRel : induce a simple graph from a relation. It symmetrizes the relation and makes it irreflexive.
- complete graph, empty graph
- complete bipartite
- IsSubgraph and IsSubraph_eq_le - input two graphs returns a bool if one is a subgraph of the other
- Sup : union of two graphs



Things we need to do:
- ✔ define perfect graphs
- ✔ define cycles
- ✔ define Complement (Complements already defined Mathlib.Combinatorics.SimpleGraph.hasCompl
- ✔ define induced subgraphs? 
- state strong perfect graph theorem
- state weak perfect graph theorem
- ✔ define bipartite graphs
- ✔ (goal has now changed to just showing specific properties are hereditary) define heriditary graphs
- ✔ (have non-computable version) define clique number
  

Examples: 
- edgeless
- complete
- bipartite
- complement of bipartite

PROGRESS SUMMARY 16/11

Things we have
- definitions for "is empty", "is complete", "is induced"
- statement of empty and complete being hereditary properties (proof to follow)
- colouring for specific examples (e.g. bipartite?)
- skeleton definition for perfect
- non-computable clique number

  Areas of expertise
  - Dan: subgraphs (esp. induced), cliques
  - Susie: subgraphs, hereditary properties
  - Alex: colourings and multipartite
 
  Working on:
  - Dan: computable clique number
  - Susie: proving hereditary properties
  - Alex: colouring



HOLIDAY PLANS 8/12
susie
-prove hereditary things
-write up perfect statements/ theorems from graph theory module
-nice simple example SPGT

dan
-find clique number for as many graphs as possible (empty, complete, etc.)

tom
-can colour odd cycle in 2 colours
-nice little colourings and cliques theorems
-colouring numbers for as many graphs as possible

alex
-embeddings and homomorphisms
