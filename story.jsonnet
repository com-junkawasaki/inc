// This story represents the project to formalize, implement, and publish
// the "Recursive Incidence Foundation" (Inc), a proposed fourth foundation of mathematics.
// The concepts are derived from the 'Incidence_Foundation_Canvas.md' document.

local foundation = {
  // Merkle-ID: foundation
  // Defines the theoretical groundwork for Inc.
  description: 'Formalize the theoretical foundations of Inc.',

  nodes: {
    // Merkle-ID: foundation.axiomatization
    axiomatization: {
      description: 'Define the core axioms of Inc (A1-A17).',
      details: 'Refine axioms with: boundaries as Multiset of Endpoint(I,R,Sign,Multiplicity); observational equivalence as greatest bisimulation (boundary multiset isomorphism + recursive matching); two modes: well-founded (induction/normalization) and guarded coinductive (corecursion).',
      deps: [],
    },

    // Merkle-ID: foundation.logic
    logic: {
      description: 'Develop Incidence Logic (IL) and its proof theory.',
      details: 'Sequent calculus, induction/corecursion rules aligned with modes; bisimulation principles for ≈; normalization preserving ≈; conditions ensuring gluing respects typing/guards. Optional: Incidence-Univalence (equating bisimilar normalized incidences).',
      status: 'in_progress',
      deps: ['foundation.nodes.axiomatization'],
    },

    // Merkle-ID: foundation.models
    models: {
      description: 'Establish semantic models to prove relative consistency.',
      details: 'Models in: (a) ZF (incidences as sets with encoded boundaries), (b) adhesive categories (gluing ≅ pushouts; Van Kampen), (c) HoTT (inductive/coinductive families). Prove that ≈ is bisimulation in each model and invariant under relabeling of endpoints.',
      deps: ['foundation.nodes.logic'],
    },

    // Merkle-ID: foundation.comparison
    comparison: {
      description: 'Formalize the translation to/from Set, Category, and Type theories.',
      details: 'Embeddings: Sets as nullary incidences; Categories via gluing-based composition with unit/associativity under typing/guard preconditions; Types as (co)inductive incidence families. Show conservative extension and preservation of operations.',
      deps: ['foundation.nodes.models'],
    },
  },
};

local implementation = {
  // Merkle-ID: implementation
  // A reference implementation of Inc for computational use.
  description: 'Create a reference library for Inc.',

  nodes: {
    // Merkle-ID: implementation.core
    core: {
      description: 'Implement core Inc data structures and operators.',
      details: 'Introduce Endpoint (i, role, sign, mult) and boundary as Multiset Endpoint; define Sign ∈ {neg, zero, pos}. Implement typed, guarded gluing glue : I → I → Option I with unit; provide normalization and equivalence (≈) as bisimulation checker over boundary multiset isomorphisms.',
      status: 'completed',
      deps: ['foundation.nodes.axiomatization', 'implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.api_freeze
    api_freeze: {
      description: 'Freeze A1–A17 in a canonical Incidence API (Lean names/fields/invariants).',
      details: 'Consolidate duplicated structures, normalize naming (boundary/typeFunc/gluing/unit), and encode invariants as fields/axioms with minimal surface.',
      status: 'completed',
      deps: ['foundation.nodes.axiomatization'],
    },

    // Merkle-ID: implementation.linear_algebra
    linear_algebra: {
      description: 'Implement the linear-algebraic semantics.',
      details: 'Define boundaryMatrix and laplacian with typed indices (Matrix (Fin n) (Fin n) α). Ensure invariance under endpoint relabeling; provide spectral tools (eigen, clustering), Hodge decompositions, and checks that linear invariants are preserved by ≈.',
      deps: ['implementation.nodes.core', 'implementation.nodes.lin_alg_signatures'],
    },

    // Merkle-ID: implementation.lin_alg_signatures
    lin_alg_signatures: {
      description: 'Specify boundary matrix (B) and Laplacian (L) types and signatures.',
      details: 'Define abstract matrix interfaces and identify minimal requirements for downstream analysis without committing to a backend.',
      deps: ['implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.proof_assistant
    proof_assistant: {
      description: 'Formalize Inc in a proof assistant.',
      details: 'Target: Lean 4. Refactor Incidence API (typeFunc naming, remove Nat.inf); implement Multiset boundaries and Endpoint; restate A2/A3 over Multiset; define ≈ as greatest bisimulation; prove unit/associativity under typing/guard hypotheses; implement boundaryMatrix/laplacian and their invariance lemmas.',
      deps: ['foundation.nodes.logic', 'implementation.nodes.core'],
    },

    // Merkle-ID: implementation.il_skeleton
    il_skeleton: {
      description: 'Incidence Logic (IL) sequent skeleton and (co)induction rules.',
      details: 'Provide a minimal sequent calculus and proof rules needed to derive core equivalences and (co)inductive reasoning.',
      deps: ['foundation.nodes.logic', 'implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.graph_model
    graph_model: {
      description: 'Provide concrete model graphIncidence and discharge remaining obligations.',
      details: 'Use simple graph roles to instantiate Incidence; eliminate placeholders/sorries and validate axioms in the model.',
      status: 'completed',
      deps: ['implementation.nodes.proof_assistant', 'implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.core_refactor
    core_refactor: {
      description: 'Refactor Lean modules to single public API; remove duplicate Incidence defs.',
      details: 'Unify `Incidence` definitions, re-export from a single module, and enforce a stable import surface.',
      status: 'completed',
      deps: ['implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.lean_green
    lean_green: {
      description: 'Make Lean build green by removing sorries and proving approx/glue laws.',
      details: 'Close remaining proof gaps and ensure CI build success before publication steps.',
      status: 'completed',
      deps: ['implementation.nodes.graph_model', 'implementation.nodes.core_refactor'],
    },

    // Merkle-ID: implementation.visualization_stub
    visualization_stub: {
      description: 'Minimal visualization/CLI stub for incidences.',
      details: 'Provide a small CLI or IO demo to inspect boundaries and gluing results; optional for paper.',
      deps: ['implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.visualization
    visualization: {
      description: 'Develop tools for visualizing Inc structures.',
      details: 'Provide projections to 2D/3D graphs, hypergraphs, and bipartite V–I graphs with boundary multiset rendering, role/sign styling, and overlays for ≈-classes and spectral features.',
      deps: ['implementation.nodes.core'],
    },
  },
};

local publication = {
  // Merkle-ID: publication
  // Disseminate the theory through academic papers.
  description: 'Publish the theory in relevant academic venues.',
  nodes: {
    // Merkle-ID: publication.abstract
    abstract: {
      description: 'Write a compelling abstract for the foundational paper.',
      details: 'Tailor to math.LO, cs.LO, math.CT; emphasize: multiset boundaries, bisimulation-based ≈, guarded gluing, and typed linear layer. Title: "Theory of Incidence — Toward a Unified Foundation of Set, Category, and Type".',
      deps: ['foundation.nodes.comparison'],
    },
    // Merkle-ID: publication.paper
    paper: {
      description: 'Write the main foundational paper.',
      details: 'Structure: Intro; Axioms with multiset/Endpoint, ≈ as bisimulation; Logic (induction/corecursion, normalization); Models (ZF/adhesive/HoTT); Linear layer (B/L, invariants); Comparison; Applications; Conclusion. Target: LMCS, MSCS.',
      deps: ['publication.nodes.abstract', 'implementation.nodes.proof_assistant', 'implementation.nodes.lean_green'],
    },
    // Merkle-ID: publication.arxiv
    arxiv: {
      description: 'Publish a preprint to ArXiv.',
      details: 'Category: math.LO / cs.LO. Title: "Theory of Incidence — A Fourth Foundation Beyond Set, Category, and Type". Sync artifacts and Lean proofs to the updated axioms and semantics.',
      deps: ['publication.nodes.paper'],
    },
  },
};

local application = {
  // Merkle-ID: application
  // Validate the theory through case studies.
  description: 'Apply Inc to solve problems in various domains.',
  nodes: {
    // Merkle-ID: application.case_study_cs
    case_study_cs: {
      description: 'Case Study: Model a computational system.',
      details: 'Represent π-calculus with parallel composition as guarded gluing and communication via shared endpoints; verify safety/liveness via ≈ and spectral criteria.',
      deps: ['implementation.nodes.core'],
    },
    // Merkle-ID: application.case_study_math
    case_study_math: {
      description: 'Case Study: Reconstruct a mathematical theory.',
      details: 'Graph/hypergraph isomorphism via ≈; rewrite systems via pushout; small homology-style invariants via B/L on incidence structures.',
      deps: ['implementation.nodes.proof_assistant'],
    },
    // Merkle-ID: application.case_study_medicine
    case_study_medicine: {
      description: 'Case Study: Model a biological network.',
      details: 'Model metabolic pathways: reactions as incidences; use L to detect cycles/flows; compare pathway variants up to ≈.',
      deps: ['implementation.nodes.linear_algebra'],
    },
  },
};

{
  story: {
    title: 'Project Inc: The Recursive Incidence Foundation',
    description: 'The complete process network for establishing Inc as a fourth foundation of mathematics.',
    // The overall process is a DAG. Dependencies are defined within each node.
    stages: {
      foundation: foundation,
      implementation: implementation,
      publication: publication,
      application: application,
    },
    // A manually-defined topological sort of all nodes for execution planning.
    // A real build system would compute this from the dependency graph.
    execution_path: [
      'foundation.axiomatization',
      'implementation.api_freeze',
      'foundation.logic',
      'implementation.il_skeleton',
      'foundation.models',
      'implementation.core',
      'implementation.core_refactor',
      'foundation.comparison',
      'implementation.lin_alg_signatures',
      'implementation.linear_algebra',
      'implementation.proof_assistant',
      'implementation.graph_model',
      'implementation.lean_green',
      'implementation.visualization_stub',
      'implementation.visualization',
      'publication.abstract',
      'application.case_study_cs',
      'application.case_study_math',
      'application.case_study_medicine',
      'publication.paper',
      'publication.arxiv',
    ],
  },
}
