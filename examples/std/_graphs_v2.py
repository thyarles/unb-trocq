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


# ── Entry point ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    graph_01_cost()
    graph_02_roi()
    print("\nAll graphs generated successfully.")
