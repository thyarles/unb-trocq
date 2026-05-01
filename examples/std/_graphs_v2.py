"""
ROI Analysis — Trocq vs Copy-Paste Proof Transfer
Based on bs_a1.v (Phase 2 and Phase 3 tactic-step counts).

Output files (saved to _graphs_v2/ subdirectory):
  graph_01_cost.png  — Cost lines: C_manual vs C_trocq
  graph_02_roi.png   — ROI curve
"""

import os
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# ── Output directory ────────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(SCRIPT_DIR, "_graphs_v2")
os.makedirs(OUT, exist_ok=True)

# ── Shared style ────────────────────────────────────────────────────────────
BLUE   = "#1f77b4"
ORANGE = "#ff7f0e"
GREEN  = "#2ca02c"
RED    = "#d62728"
GREY   = "#aaaaaa"

plt.rcParams.update({
    "font.family":  "serif",
    "axes.spines.top":   False,
    "axes.spines.right": False,
    "axes.grid":    True,
    "grid.alpha":   0.3,
    "figure.dpi":   150,
})

# ── Constants from bs_a1.v ──────────────────────────────────────────────────
#
#   Phase 2 (copy-paste):
#     plength_papp_manual = 5, papp_assoc_manual = 5, prev_papp_manual = 7
#     P_PASTE = (5 + 5 + 7) / 3 = 17/3 ≈ 5.67 steps/theorem
#     C_manual(n) = P_PASTE * n
#
#   Phase 3 (Trocq):
#     S_bij = plist_nlist_iso(4) + nlist_plist_iso(4) + R_NatList(5)
#             + shared Trocq Use x3(3) = 13
#     Per-function: _plength(11) + _papp(14) + _prev(12) = 37
#     S_SETUP = S_bij + per-function = 50
#     C_trocq(n) = S_SETUP + 2*n
#
#   Break-even: (17/3)*n = 50 + 2*n  =>  n* = 150/11 ≈ 13.6
#   ROI_inf = (P_PASTE - 2) / 2 = (11/3) / 2 = 11/6 ≈ 1.83
#
P_PASTE = 17 / 3     # avg tactic steps per copy-paste theorem
S_SETUP = 50         # one-time Trocq setup cost (steps)
N_STAR  = 150 / 11   # break-even point ≈ 13.6
ROI_INF = 11 / 6     # long-run ROI asymptote ≈ 1.83


# ══════════════════════════════════════════════════════════════════════════
# graph_01_cost
# C_manual(n) = (17/3)*n    (copy-paste, no setup)
# C_trocq(n)  = 50 + 2*n   (full Trocq bureaucracy)
# Break-even: n* = 150/11 ≈ 13.6
# ══════════════════════════════════════════════════════════════════════════
def graph_01_cost():
    n = np.linspace(0, 30, 600)
    c_manual = P_PASTE * n
    c_trocq  = S_SETUP + 2 * n
    y_star   = P_PASTE * N_STAR

    fig, ax = plt.subplots(figsize=(9, 5.5))

    # Shaded regions
    ax.fill_between(n, c_manual, c_trocq,
                    where=(n < N_STAR),
                    alpha=0.12, color=ORANGE, label="_nolegend_")
    ax.fill_between(n, c_manual, c_trocq,
                    where=(n >= N_STAR),
                    alpha=0.12, color=BLUE, label="_nolegend_")

    # Cost lines
    ax.plot(n, c_manual, color=ORANGE, lw=2.5,
            label=r"$C_{\mathrm{manual}}(n) = \frac{17}{3}\,n \approx 5.67n$"
                  r"  (copy-paste, setup $= 0$)")
    ax.plot(n, c_trocq, color=BLUE, lw=2.5,
            label=r"$C_{\mathrm{trocq}}(n) = 50 + 2n$  (full setup)")

    # Setup-cost annotation
    ax.axhline(S_SETUP, color=BLUE, lw=1.0, ls=":", alpha=0.5)
    ax.text(0.4, S_SETUP + 1.5,
            r"$S_{\mathrm{setup}} = 50$",
            fontsize=8.5, color=BLUE, alpha=0.8)

    # Break-even marker
    ax.axvline(N_STAR, color=GREY, lw=1.4, ls="--")
    ax.scatter([N_STAR], [y_star], color="black", zorder=5, s=60)
    ax.annotate(r"Break-even $n^* \approx 13.6$",
                xy=(N_STAR, y_star),
                xytext=(N_STAR + 1.0, y_star + 6),
                fontsize=10,
                arrowprops=dict(arrowstyle="->", color="black", lw=1))

    # Region labels
    ax.text(3,  110, "Manual cheaper",  fontsize=9, color=ORANGE, alpha=0.9)
    ax.text(19,  30, "Trocq cheaper",   fontsize=9, color=BLUE,   alpha=0.9)

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel("Total proof obligations (tactic steps)", fontsize=11)
    ax.set_title(
        "Cost Comparison: Copy-Paste vs. Trocq  (from bs_a1.v)\n"
        r"$C_M = \frac{17}{3}n$ (no setup),  "
        r"$C_T = 50 + 2n$ (full bureaucracy);  "
        r"$n^* = \frac{150}{11} \approx 13.6$",
        fontsize=11,
    )
    ax.legend(fontsize=9, loc="upper left")
    ax.set_xlim(0, 30)
    ax.set_ylim(0, 175)

    fig.tight_layout()
    path = os.path.join(OUT, "graph_01_cost.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# graph_02_roi
# ROI(n) = ((11/3)*n - 50) / (50 + 2*n)
# Zero crossing: n* = 150/11 ≈ 13.6
# Asymptote:     ROI_inf = 11/6 ≈ 1.83
# ══════════════════════════════════════════════════════════════════════════
def graph_02_roi():
    n = np.linspace(0, 60, 800)
    roi = ((11 / 3) * n - 50) / (50 + 2 * n)

    fig, ax = plt.subplots(figsize=(9, 5))

    # Shaded regions
    ax.fill_between(n, roi, 0,
                    where=(roi < 0), alpha=0.15, color=RED,
                    label="Manual cheaper (ROI < 0)")
    ax.fill_between(n, roi, 0,
                    where=(roi >= 0), alpha=0.15, color=GREEN,
                    label="Trocq cheaper (ROI > 0)")

    # ROI curve
    ax.plot(n, roi, color=BLUE, lw=2.5, label=r"$\mathrm{ROI}(n)$")

    # Reference lines
    ax.axhline(0,        color="black", lw=1.0, ls="-")
    ax.axhline(ROI_INF,  color=GREY,    lw=1.4, ls="--")
    ax.axvline(N_STAR,   color=GREY,    lw=1.4, ls="--")

    # Break-even annotation
    ax.scatter([N_STAR], [0], color="black", zorder=5, s=60)
    ax.annotate(r"Break-even $n^* \approx 13.6$",
                xy=(N_STAR, 0),
                xytext=(N_STAR + 2.0, -0.25),
                fontsize=10,
                arrowprops=dict(arrowstyle="->", color="black", lw=1))

    # Asymptote label
    ax.text(50, ROI_INF + 0.05,
            r"Asymptote $\to 1.83\times$",
            fontsize=9, color=GREY, va="bottom")

    # Formula box
    ax.annotate(
        r"$\mathrm{ROI}_\infty = \dfrac{P_{\mathrm{paste}} - 2}{2}"
        r"= \dfrac{11}{6} \approx 1.83\times$",
        xy=(35, 1.15),
        fontsize=10,
        ha="center",
        bbox=dict(boxstyle="round,pad=0.4", fc="white", ec=GREY, lw=1),
    )

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel(r"$\mathrm{ROI}(n) = \dfrac{C_M - C_T}{C_T}$", fontsize=11)
    ax.set_title(
        "ROI Curve: Trocq vs. Copy-Paste  (from bs_a1.v)\n"
        r"$\mathrm{ROI}(n) = \dfrac{\frac{11}{3}n - 50}{50 + 2n}$;  "
        r"break-even $n^* \approx 13.6$;  asymptote $\to 1.83\times$",
        fontsize=11,
    )
    ax.legend(fontsize=10, loc="upper left")
    ax.set_xlim(0, 60)
    ax.set_ylim(-1.2, 2.5)
    ax.yaxis.set_major_formatter(
        ticker.FuncFormatter(lambda y, _: f"{y:.1f}x"))

    fig.tight_layout()
    path = os.path.join(OUT, "graph_02_roi.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ── bs_a2.v constants ───────────────────────────────────────────────────────
#
#   Phase 3  (Manual — Ctrl+C / Ctrl+V, 4 theorems):
#     plength_papp_manual = 5, papp_assoc_manual = 5,
#     prev_papp_manual = 7,  psum_papp_manual = 8  (2 Typeclass divergences)
#     P_PASTE_A2 = (5 + 5 + 7 + 8) / 4 = 6.25 steps/theorem
#     C_manual_a2(n) = P_PASTE_A2 * n
#
#   Phase 4+5  (Trocq):
#     S_bij = 13  (same)
#     Bridge lemmas: 5 + 6 + 6 + 6 = 23
#     R__ wrappers:  5 + 7 + 5 + 5 = 22
#     Trocq Use x4 (per-function) = 4
#     S_SETUP_A2 = 13 + 23 + 22 + 4 = 62
#     C_trocq_a2(n) = 62 + 2*n
#
#   Break-even: 6.25n = 62 + 2n  =>  4.25n = 62  =>  n* = 62/4.25 ≈ 14.6
#   ROI_inf_a2 = (6.25 - 2) / 2 = 4.25/2 = 2.125
#
P_PASTE_A2 = 6.25
S_SETUP_A2 = 62
N_STAR_A2  = 62 / 4.25     # ≈ 14.6
ROI_INF_A2 = 4.25 / 2      # = 2.125


# ══════════════════════════════════════════════════════════════════════════
# graph_03_cost_comparison
# All four cost lines on one plot:
#   C_manual_a1(n) = (17/3)*n ≈ 5.67n   C_trocq_a1(n) = 50 + 2n
#   C_manual_a2(n) = 6.25*n              C_trocq_a2(n) = 62 + 2n
# Both break-even points marked.
# ══════════════════════════════════════════════════════════════════════════
def graph_03_cost_comparison():
    n = np.linspace(0, 30, 600)

    c_m_a1 = P_PASTE    * n
    c_t_a1 = S_SETUP    + 2 * n
    c_m_a2 = P_PASTE_A2 * n
    c_t_a2 = S_SETUP_A2 + 2 * n

    ORANGE2 = "#e6820e"   # darker orange for a2 manual
    BLUE2   = "#0a4f8c"   # darker blue  for a2 trocq

    fig, ax = plt.subplots(figsize=(9, 5.5))

    ax.plot(n, c_m_a1, color=ORANGE, lw=2.5, ls="-",
            label=r"$C_M^{a1}(n)=\frac{17}{3}n\approx5.67n$  (bs\_a1, copy-paste)")
    ax.plot(n, c_t_a1, color=BLUE,   lw=2.5, ls="-",
            label=r"$C_T^{a1}(n)=50+2n$  (bs\_a1, Trocq)")
    ax.plot(n, c_m_a2, color=ORANGE2, lw=2.5, ls="--",
            label=r"$C_M^{a2}(n)=6.25n$  (bs\_a2, copy-paste)")
    ax.plot(n, c_t_a2, color=BLUE2,   lw=2.5, ls="--",
            label=r"$C_T^{a2}(n)=62+2n$  (bs\_a2, Trocq)")

    # Break-even markers
    for n_star, p_paste, s_setup, color, label in [
        (N_STAR,    P_PASTE,    S_SETUP,    "black",  r"$n^*_{a1}\approx13.6$"),
        (N_STAR_A2, P_PASTE_A2, S_SETUP_A2, "#444444", r"$n^*_{a2}\approx14.6$"),
    ]:
        y_star = p_paste * n_star
        ax.axvline(n_star, color=GREY, lw=1.2, ls=":")
        ax.scatter([n_star], [y_star], color=color, zorder=5, s=55)
        ax.annotate(label,
                    xy=(n_star, y_star),
                    xytext=(n_star + 0.8, y_star + 7),
                    fontsize=9,
                    arrowprops=dict(arrowstyle="->", color=color, lw=1))

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel("Total tactic steps", fontsize=11)
    ax.set_title(
        "Cost Comparison: bs\_a1.v vs bs\_a2.v\n"
        "Solid = bs\_a1 (PList nat, 3 theorems), "
        "Dashed = bs\_a2 (PList A + Typeclass, 4 theorems)",
        fontsize=11,
    )
    ax.legend(fontsize=8.5, loc="upper left")
    ax.set_xlim(0, 30)
    ax.set_ylim(0, 190)

    fig.tight_layout()
    path = os.path.join(OUT, "graph_03_cost_comparison.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# graph_04_roi_comparison
# Two ROI curves on one axes:
#   ROI_a1(n) = ((11/3)*n - 50) / (50 + 2n)   asymptote 1.83x
#   ROI_a2(n) = (4.25*n  - 62) / (62 + 2n)    asymptote 2.125x
# Both zero-crossings and both asymptotes marked.
# ══════════════════════════════════════════════════════════════════════════
def graph_04_roi_comparison():
    n = np.linspace(0, 60, 800)

    roi_a1 = ((P_PASTE    - 2) * n - S_SETUP)    / (S_SETUP    + 2 * n)
    roi_a2 = ((P_PASTE_A2 - 2) * n - S_SETUP_A2) / (S_SETUP_A2 + 2 * n)

    fig, ax = plt.subplots(figsize=(9, 5))

    ax.fill_between(n, roi_a1, 0,
                    where=(roi_a1 >= 0), alpha=0.08, color=GREEN)
    ax.fill_between(n, roi_a2, 0,
                    where=(roi_a2 >= 0), alpha=0.08, color=BLUE)

    ax.plot(n, roi_a1, color=ORANGE, lw=2.5,
            label=r"$\mathrm{ROI}_{a1}(n)$  (bs\_a1, $P_M\approx5.67$, $S=50$)")
    ax.plot(n, roi_a2, color=BLUE,   lw=2.5, ls="--",
            label=r"$\mathrm{ROI}_{a2}(n)$  (bs\_a2, $P_M=6.25$, $S=62$)")

    ax.axhline(0, color="black", lw=1.0)

    # Asymptote lines
    ax.axhline(ROI_INF,    color=ORANGE, lw=1.2, ls=":", alpha=0.7)
    ax.axhline(ROI_INF_A2, color=BLUE,   lw=1.2, ls=":", alpha=0.7)
    ax.text(53, ROI_INF    + 0.05, r"$\to1.83\times$ (a1)", fontsize=8.5, color=ORANGE)
    ax.text(53, ROI_INF_A2 + 0.05, r"$\to2.125\times$ (a2)", fontsize=8.5, color=BLUE)

    # Zero-crossing markers
    for n_star, color in [(N_STAR, ORANGE), (N_STAR_A2, BLUE)]:
        ax.axvline(n_star, color=GREY, lw=1.2, ls=":")
        ax.scatter([n_star], [0], color=color, zorder=5, s=55)

    ax.annotate(r"$n^*_{a1}\approx13.6$", xy=(N_STAR, 0),
                xytext=(N_STAR + 1.5, -0.28), fontsize=9,
                arrowprops=dict(arrowstyle="->", color=ORANGE, lw=1))
    ax.annotate(r"$n^*_{a2}\approx14.6$", xy=(N_STAR_A2, 0),
                xytext=(N_STAR_A2 + 1.5, -0.45), fontsize=9,
                arrowprops=dict(arrowstyle="->", color=BLUE, lw=1))

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel(r"$\mathrm{ROI}(n) = (C_M - C_T)\,/\,C_T$", fontsize=11)
    ax.set_title(
        "ROI Comparison: bs\_a1.v vs bs\_a2.v\n"
        "True polymorphism raises both $P_M$ and $S_{\\rm setup}$, "
        "but lifts the long-run ceiling from 1.83× to 2.125×",
        fontsize=11,
    )
    ax.legend(fontsize=9.5, loc="upper left")
    ax.set_xlim(0, 60)
    ax.set_ylim(-1.4, 2.8)
    ax.yaxis.set_major_formatter(
        ticker.FuncFormatter(lambda y, _: f"{y:.2g}x"))

    fig.tight_layout()
    path = os.path.join(OUT, "graph_04_roi_comparison.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ── Entry point ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    graph_01_cost()
    graph_02_roi()
    graph_03_cost_comparison()
    graph_04_roi_comparison()
    print("\nAll graphs generated successfully.")
