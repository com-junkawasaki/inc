---
layout: default
title: Incidence Theory
description: A Fourth Foundation for Mathematics and Computation
---

# 🧮 Incidence Theory

**A Fourth Foundation Beyond Set, Category, and Type**

[![CI Status](https://github.com/com-junkawasaki/inc/actions/workflows/ci.yml/badge.svg)](https://github.com/com-junkawasaki/inc/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17345516.svg)](https://doi.org/10.5281/zenodo.17345516)

## 🌟 Live Demonstration

<div style="margin: 1rem 0; display: flex; gap: .5rem; flex-wrap: wrap;">
  <a class="btn" href="https://live.lean-lang.org/" target="_blank" rel="noopener">Open in Lean4 Web ▶</a>
  <a class="btn btn-secondary" href="https://github.com/leanprover-community/lean4web" target="_blank" rel="noopener">lean4web Repo</a>
</div>

<div style="margin: 1rem 0;">
  <details>
    <summary><strong>Lean4 Web Inline Playground (live.lean-lang.org)</strong></summary>
    <div style="margin-top: .75rem;">
      <iframe
        src="https://live.lean-lang.org/"
        title="Lean 4 Web Playground"
        style="width: 100%; height: 70vh; border: 1px solid #e0e0e0; border-radius: 8px;"
        loading="lazy"
      ></iframe>
      <p style="font-size: .9rem; color: #666; margin-top: .5rem;">
        This embeds the official Lean 4 web editor. Use it to try small Lean4 snippets.
      </p>
    </div>
  </details>
</div>

Experience Incidence Theory in action with our interactive examples:

### 🔍 Triangle Graph Analysis
Our flagship example demonstrating ∂²=0 and boundary matrix computation.

<div class="demo-container">
  <div class="triangle-visualization">
    <div class="graph-display">
      <h4>Triangle Graph Structure</h4>
      <div class="graph-diagram">
        <svg width="300" height="200" viewBox="0 0 300 200">
          <!-- Triangle nodes -->
          <circle cx="50" cy="150" r="20" fill="#4CAF50" stroke="#2E7D32" stroke-width="2"/>
          <circle cx="150" cy="50" r="20" fill="#4CAF50" stroke="#2E7D32" stroke-width="2"/>
          <circle cx="250" cy="150" r="20" fill="#4CAF50" stroke="#2E7D32" stroke-width="2"/>

          <!-- Triangle edges -->
          <line x1="70" y1="140" x2="130" y2="70" stroke="#2196F3" stroke-width="3"/>
          <line x1="170" y1="70" x2="230" y2="140" stroke="#2196F3" stroke-width="3"/>
          <line x1="70" y1="140" x2="230" y2="140" stroke="#2196F3" stroke-width="3"/>

          <!-- Labels -->
          <text x="50" y="157" text-anchor="middle" fill="white" font-weight="bold">A</text>
          <text x="150" y="57" text-anchor="middle" fill="white" font-weight="bold">B</text>
          <text x="250" y="157" text-anchor="middle" fill="white" font-weight="bold">C</text>

          <text x="100" y="105" text-anchor="middle" fill="#2196F3" font-weight="bold">AB</text>
          <text x="200" y="105" text-anchor="middle" fill="#2196F3" font-weight="bold">BC</text>
          <text x="150" y="175" text-anchor="middle" fill="#2196F3" font-weight="bold">CA</text>
        </svg>
      </div>
    </div>

    <div class="computation-results">
      <h4>Boundary Matrix ∂ (Live Computation)</h4>
      <div class="matrix-display" id="boundary-matrix">
        <!-- Matrix will be populated by JavaScript -->
        <table class="matrix-table">
          <thead>
            <tr>
              <th>∂</th>
              <th>N₀(A)</th>
              <th>N₁(B)</th>
              <th>N₂(C)</th>
              <th>E₁(AB)</th>
              <th>E₂(BC)</th>
              <th>E₃(CA)</th>
            </tr>
          </thead>
          <tbody id="boundary-matrix-body">
            <!-- Dynamic content -->
          </tbody>
        </table>
      </div>

      <h4>Laplacian L = ∂ᵀ∂ (Live Computation)</h4>
      <div class="matrix-display" id="laplacian-matrix">
        <table class="matrix-table">
          <thead>
            <tr>
              <th>L</th>
              <th>N₀</th>
              <th>N₁</th>
              <th>N₂</th>
              <th>E₁</th>
              <th>E₂</th>
              <th>E₃</th>
            </tr>
          </thead>
          <tbody id="laplacian-matrix-body">
            <!-- Dynamic content -->
          </tbody>
        </table>
      </div>

      <div class="verification-status">
        <h4>Verification Results</h4>
        <div id="verification-results">
          <p>🔄 Computing verification...</p>
        </div>
      </div>
    </div>
  </div>
</div>

<script>
// Triangle graph boundary matrix computation
const triangleData = {
  nodes: ['A', 'B', 'C'],
  edges: ['AB', 'BC', 'CA'],
  boundary: {
    // ∂(AB) = -A + B, ∂(BC) = -B + C, ∂(CA) = -C + A
    'AB': {'A': -1, 'B': 1},
    'BC': {'B': -1, 'C': 1},
    'CA': {'C': -1, 'A': 1}
  }
};

function computeBoundaryMatrix() {
  const tbody = document.getElementById('boundary-matrix-body');
  const allElements = [...triangleData.nodes, ...triangleData.edges];

  allElements.forEach(row => {
    const tr = document.createElement('tr');
    const th = document.createElement('th');
    th.textContent = row;
    tr.appendChild(th);

    allElements.forEach(col => {
      const td = document.createElement('td');
      let value = 0;

      if (triangleData.edges.includes(row)) {
        // Edge rows in boundary matrix
        const boundary = triangleData.boundary[row];
        value = boundary[col] || 0;
      }

      td.textContent = value;
      td.className = value !== 0 ? 'non-zero' : 'zero';
      tr.appendChild(td);
    });

    tbody.appendChild(tr);
  });
}

function computeLaplacianMatrix() {
  const tbody = document.getElementById('laplacian-matrix-body');
  const allElements = [...triangleData.nodes, ...triangleData.edges];

  allElements.forEach(row => {
    const tr = document.createElement('tr');
    const th = document.createElement('th');
    th.textContent = row;
    tr.appendChild(th);

    allElements.forEach(col => {
      const td = document.createElement('td');
      let value = 0;

      // L[i,j] = sum_k ∂[k,i] * ∂[k,j] (actual ∂ᵀ∂ computation)
      // This computes the Laplacian as boundary matrix transpose times boundary matrix

      triangleData.edges.forEach(edge => {
        const boundary = triangleData.boundary[edge];
        const bik = boundary[row] || 0;  // ∂[k,i]
        const bjk = boundary[col] || 0;  // ∂[k,j]
        value += bik * bjk;
      });

      td.textContent = value;
      td.className = value !== 0 ? 'non-zero' : 'zero';
      tr.appendChild(td);
    });

    tbody.appendChild(tr);
  });
}

function runVerification() {
  const results = document.getElementById('verification-results');

  // These entries describe the checked Lean core, not unformalized research goals.
  const checks = [
    { name: 'Triangle ∂² = 0', status: '✓ VERIFIED', detail: 'Finite triangle calculation checked by Lean' },
    { name: 'Boundary invariants', status: '✓ VERIFIED', detail: 'Finite boundaries, signs, and positive multiplicities' },
    { name: 'Gluing laws', status: '✓ VERIFIED', detail: 'Unit, type preservation, and conditional associativity' },
    { name: 'Bisimilarity', status: '✓ VERIFIED', detail: 'Reflexive, symmetric, and transitive' },
    { name: 'Linear data', status: '✓ VERIFIED', detail: 'Boundary matrices and Laplacians are computed from boundaries' }
  ];

  let html = '<div class="verification-list">';
  checks.forEach(check => {
    html += `<div class="verification-item ${check.status.includes('VERIFIED') ? 'verified' : 'failed'}">
               <span class="status">${check.status}</span>
               <span class="name">${check.name}</span>
               <span class="detail">${check.detail}</span>
             </div>`;
  });
  html += '</div>';

  results.innerHTML = html;
}

// Initialize on page load
document.addEventListener('DOMContentLoaded', function() {
  computeBoundaryMatrix();
  computeLaplacianMatrix();
  runVerification();
});
</script>

## 📚 Checked Lean core

The formalization currently checks the boundary, gluing, bisimulation, and
triangle-linear results shown above. Pushout universality, generic `∂² = 0`,
linear completeness, and translation preservation remain conditional research
goals: their required categorical or linear hypotheses are not yet encoded.

<div class="verification-summary">
  <div class="metric">
    <div class="number">6</div>
    <div class="label">Checked triangle matrix entries</div>
  </div>
  <div class="metric">
    <div class="number">3</div>
    <div class="label">Checked Laplacian diagonal entries</div>
  </div>
  <div class="metric">
    <div class="number">0</div>
    <div class="label">Unproved Lean declarations</div>
  </div>
  <div class="metric">
    <div class="number">✅</div>
    <div class="label">CI/CD Verified</div>
  </div>
</div>

## 🔗 Learn More

- **[Formal status](verification.html)** - Checked scope and open research goals
- **[ArXiv Preprint](https://arxiv.org/)** - Academic paper (coming soon)
- **[Lean Formalization](https://github.com/com-junkawasaki/inc/tree/main/incidence-theory)** - Checked core proofs in Lean 4
- **[Validation Script](https://github.com/com-junkawasaki/inc#one-command-verification)** - One-command verification

## 🎯 Status: active formalization

The checked core and the broader theory are being developed together. The Lean
source defines the currently verified scope.

---

*Built with Lean 4, Jekyll, and mathematics. View source on [GitHub](https://github.com/com-junkawasaki/inc).*
