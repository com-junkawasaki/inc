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
      details: 'Based on the final axiomatic system defined in the canvas, including modes (Well-founded vs. Coinductive), gluing, and equivalence.',
      deps: [],
    },

    // Merkle-ID: foundation.logic
    logic: {
      description: 'Develop Incidence Logic (IL) and its proof theory.',
      details: 'Formalize the sequent calculus, (co)induction principles, and the optional Incidence-Univalence axiom.',
      deps: ['foundation.nodes.axiomatization'],
    },

    // Merkle-ID: foundation.models
    models: {
      description: 'Establish semantic models to prove relative consistency.',
      details: 'Construct models in ZF Set Theory, Adhesive Categories (for gluing semantics), and Homotopy Type Theory (for (co)inductive aspects).',
      deps: ['foundation.nodes.logic'],
    },

    // Merkle-ID: foundation.comparison
    comparison: {
      description: 'Formalize the translation to/from Set, Category, and Type theories.',
      details: 'Show how Inc can conservatively extend or embed existing foundations, establishing it as a unified framework.',
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
      details: 'Includes Incidence, Boundary Operator (∂), Gluing, and Equivalence Checking (≈). Language choice: Lean/Agda for formal veIncication, Julia/Python for numerical computation.',
      deps: ['foundation.nodes.axiomatization', 'implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.api_freeze
    api_freeze: {
      description: 'Freeze A1–A17 in a canonical Incidence API (Lean names/fields/invariants).',
      details: 'Consolidate duplicated structures, normalize naming (boundary/typeFunc/gluing/unit), and encode invariants as fields/axioms with minimal surface.',
      deps: ['foundation.nodes.axiomatization'],
    },

    // Merkle-ID: implementation.linear_algebra
    linear_algebra: {
      description: 'Implement the linear-algebraic semantics.',
      details: 'Sparse matrix representation for Boundary Matrix (B) and Laplacian (L). Provide functions for spectral analysis, Hodge decomposition, and diffusion models.',
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
      details: 'Target: Lean 4 or Agda. Implement the axioms, proof rules of IL, and the standard library of foundational structures (N, Lists, etc.).',
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
      deps: ['implementation.nodes.proof_assistant', 'implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.core_refactor
    core_refactor: {
      description: 'Refactor Lean modules to single public API; remove duplicate Incidence defs.',
      details: 'Unify `Incidence` definitions, re-export from a single module, and enforce a stable import surface.',
      deps: ['implementation.nodes.api_freeze'],
    },

    // Merkle-ID: implementation.lean_green
    lean_green: {
      description: 'Make Lean build green by removing sorries and proving approx/glue laws.',
      details: 'Close remaining proof gaps and ensure CI build success before publication steps.',
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
      details: 'Since Inc structures are abstract, provide projections to 2D/3D graphs, hypergraphs, or bipartite V-I graphs.',
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
      details: 'Tailor abstracts for different venues (math.LO, cs.LO, math.CT). Finalize title: "Theory of Incidence — Toward a Unified Foundation of Set, Category, and Type".',
      deps: ['foundation.nodes.comparison'],
    },
    // Merkle-ID: publication.paper
    paper: {
      description: 'Write the main foundational paper.',
      details: 'Structure: Introduction, Axioms of Inc, Models, Comparison with other foundations, Applications, Conclusion. Target journals: LMCS, MSCS.',
      deps: ['publication.nodes.abstract', 'implementation.nodes.proof_assistant', 'implementation.nodes.lean_green'],
    },
    // Merkle-ID: publication.arxiv
    arxiv: {
      description: 'Publish a preprint to ArXiv.',
      details: 'Category: math.LO / cs.LO. Title: "Theory of Incidence — A Fourth Foundation Beyond Set, Category, and Type".',
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
      details: 'Represent a process calculus (like pi-calculus) or a dynamic network topology using Inc to demonstrate its expressive power for dynamic structures.',
      deps: ['implementation.nodes.core'],
    },
    // Merkle-ID: application.case_study_math
    case_study_math: {
      description: 'Case Study: Reconstruct a mathematical theory.',
      details: 'Re-formalize a portion of graph theory or simplicial homology within Inc to show its unifying power.',
      deps: ['implementation.nodes.proof_assistant'],
    },
    // Merkle-ID: application.case_study_medicine
    case_study_medicine: {
      description: 'Case Study: Model a biological network.',
      details: 'Use Inc to model a metabolic pathway or a neural network, leveraging its ability to handle dynamic changes in topology and its connection to linear analysis (Laplacian).',
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
      'foundation.logic',
      'foundation.models',
      'implementation.core',
      'foundation.comparison',
      'implementation.linear_algebra',
      'implementation.proof_assistant',
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
