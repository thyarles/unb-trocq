"""
ROI Analysis — Trocq vs Manual Proof Transfer
Generates 5 publication-quality PNG graphs for the presentation slides.

Output files (saved in the same directory as this script):
  graph_01_cost.png   — First Try:  cost lines  C_manual vs C_trocq
  graph_02_roi.png    — First Try:  ROI curve
  graph_03_revised_cost.png — Second Try: revised fixed-vs-variable model
  graph_04_family.png — Third Try:  family of C_manual curves per c_avg
"""

import os
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# ── Output directory (same folder as this script) ─────────────────────────
OUT = os.path.dirname(os.path.abspath(__file__))

# ── Shared style ──────────────────────────────────────────────────────────
BLUE   = "#1f77b4"
ORANGE = "#ff7f0e"
GREEN  = "#2ca02c"
RED    = "#d62728"
GREY   = "#aaaaaa"
PALETTE = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

plt.rcParams.update({
    "font.family":  "serif",
    "axes.spines.top":   False,
    "axes.spines.right": False,
    "axes.grid":    True,
    "grid.alpha":   0.3,
    "figure.dpi":   150,
})


# ══════════════════════════════════════════════════════════════════════════
# Graph 01 — First Try: Cost Lines
# C_manual(n) = 7n          (purely variable, no fixed cost — First Try model)
# C_trocq(n)  = 17 + 2n     (12d+5 with d=1, c=1 ⟹ 17; 2cn with c=1 ⟹ 2n)
# Break-even:  7n = 17 + 2n  ⟹  n* = 17/5 = 3.4
# ══════════════════════════════════════════════════════════════════════════
def graph_01():
    n = np.linspace(0, 15, 300)
    c_manual = 7 * n
    c_trocq  = 17 + 2 * n
    n_star   = 17 / 5          # 3.4

    fig, ax = plt.subplots(figsize=(8, 5))

    # Shaded regions
    ax.fill_between(n, c_manual, c_trocq,
                    where=(n < n_star),
                    alpha=0.12, color=ORANGE, label="_nolegend_")
    ax.fill_between(n, c_manual, c_trocq,
                    where=(n >= n_star),
                    alpha=0.12, color=BLUE, label="_nolegend_")

    # Cost lines
    ax.plot(n, c_manual, color=ORANGE, lw=2.5,
            label=r"$C_{\mathrm{manual}}(n) = 7n$")
    ax.plot(n, c_trocq,  color=BLUE,   lw=2.5,
            label=r"$C_{\mathrm{trocq}}(n) = 17 + 2n$")

    # Break-even marker
    y_star = 7 * n_star
    ax.axvline(n_star, color=GREY, lw=1.4, ls="--")
    ax.scatter([n_star], [y_star], color="black", zorder=5, s=60)
    ax.annotate(r"Break-even $n^* \approx 3.4$",
                xy=(n_star, y_star),
                xytext=(n_star + 0.6, y_star + 8),
                fontsize=10,
                arrowprops=dict(arrowstyle="->", color="black", lw=1))

    # Region labels
    ax.text(1.2, 75,  "Manual cheaper",  fontsize=9, color=ORANGE, alpha=0.9)
    ax.text(7.5, 20,  "Trocq cheaper",   fontsize=9, color=BLUE,   alpha=0.9)

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel("Total proof obligations (tactic steps)", fontsize=11)
    ax.set_title("First Try — Proof Obligations vs. Theorems\n"
                 r"($c = 1$, $d = 1$)", fontsize=12)
    ax.legend(fontsize=10)
    ax.set_xlim(0, 15)
    ax.set_ylim(0, 115)

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_01_cost.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# Graph 02 — First Try: ROI Curve
# ROI(n) = (C_manual - C_trocq) / C_trocq = (5n - 17) / (17 + 2n)
# Zero crossing:  n* = 17/5 = 3.4
# Asymptote:      lim_{n→∞} ROI(n) = 5/2 = 2.5
# ══════════════════════════════════════════════════════════════════════════
def graph_02():
    n = np.linspace(0, 25, 600)
    roi = (5 * n - 17) / (17 + 2 * n)
    n_star = 17 / 5
    asymptote = 2.5

    fig, ax = plt.subplots(figsize=(8, 5))

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
    ax.axhline(0,          color="black", lw=1.0, ls="-")
    ax.axhline(asymptote,  color=GREY,    lw=1.4, ls="--")
    ax.axvline(n_star,     color=GREY,    lw=1.4, ls="--")

    # Annotations
    ax.scatter([n_star], [0], color="black", zorder=5, s=60)
    ax.annotate(r"Break-even $n \approx 3.4$",
                xy=(n_star, 0),
                xytext=(n_star + 1.0, -0.4),
                fontsize=10,
                arrowprops=dict(arrowstyle="->", color="black", lw=1))
    ax.text(20, asymptote + 0.08,
            r"Asymptote $\to 2.5$",
            fontsize=9, color=GREY, va="bottom")

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel(r"$\mathrm{ROI}(n) = \dfrac{C_M - C_T}{C_T}$", fontsize=11)
    ax.set_title("First Try — ROI Curve", fontsize=12)
    ax.legend(fontsize=10, loc="upper left")
    ax.set_xlim(0, 25)
    ax.set_ylim(-1.2, 3.0)
    ax.yaxis.set_major_formatter(
        ticker.FuncFormatter(lambda y, _: f"{y:.1f}×"))

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_02_roi.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# Graph 03 — Second Try: Revised Fixed-vs-Variable Cost Model
# Numbers derived from bs_p5.v (length + append, f = 2 functions):
#
#   Shared base (both pay once):
#     isos (plist_nlist_iso, nlist_plist_iso)   ≈  6 steps
#     bridge lemmas (_plength_eq_nlength,
#                    plist_2_nlist_app)         ≈  6 steps
#     C_base ≈ 12
#
#   Manual per-theorem (rewrite chain):         ≈  7 steps
#     C_manual(n) = 12 + 7n
#
#   Trocq overhead (R_NatList + R__plength +
#                   R__papp + 5× Trocq Use):    ≈ 22 steps
#     C_trocq(n)  = 12 + 22 + 2n = 34 + 2n
#
#   Break-even: 12 + 7n = 34 + 2n  ⟹  n* = 22/5 ≈ 4.4
# ══════════════════════════════════════════════════════════════════════════
def graph_03():
    n = np.linspace(0, 20, 400)

    C_base   = 12
    c_manual_var = 7      # per-theorem slope (manual)
    trocq_overhead = 22   # R__ wrappers + Trocq Use
    c_trocq_var  = 2      # per-theorem slope (Trocq)

    cm = C_base + c_manual_var * n
    ct = C_base + trocq_overhead + c_trocq_var * n

    n_star = trocq_overhead / (c_manual_var - c_trocq_var)  # 22/5 = 4.4
    y_star = C_base + c_manual_var * n_star

    fig, ax = plt.subplots(figsize=(8, 5))

    # Shaded regions
    ax.fill_between(n, cm, ct, where=(n < n_star),
                    alpha=0.12, color=ORANGE)
    ax.fill_between(n, cm, ct, where=(n >= n_star),
                    alpha=0.12, color=BLUE)

    # Cost lines
    ax.plot(n, cm, color=ORANGE, lw=2.5,
            label=r"$C_{\mathrm{manual}}(n) = 12 + 7n$")
    ax.plot(n, ct, color=BLUE,   lw=2.5,
            label=r"$C_{\mathrm{trocq}}(n) = 34 + 2n$")

    # Fixed cost annotation (base)
    ax.axhline(C_base,           color=ORANGE, lw=1.0, ls=":", alpha=0.6)
    ax.axhline(C_base + trocq_overhead, color=BLUE, lw=1.0, ls=":", alpha=0.6)
    ax.annotate("", xy=(0.3, C_base + trocq_overhead),
                xytext=(0.3, C_base),
                arrowprops=dict(arrowstyle="<->", color=GREY, lw=1.2))
    ax.text(0.5, (C_base + C_base + trocq_overhead) / 2,
            r"$f \cdot W_{\mathrm{trocq}} = 22$",
            fontsize=8.5, color=GREY, va="center")

    # Break-even
    ax.axvline(n_star, color=GREY, lw=1.4, ls="--")
    ax.scatter([n_star], [y_star], color="black", zorder=5, s=60)
    ax.annotate(r"Break-even $n^* \approx 4.4$",
                xy=(n_star, y_star),
                xytext=(n_star + 0.8, y_star + 8),
                fontsize=10,
                arrowprops=dict(arrowstyle="->", color="black", lw=1))

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel("Total proof obligations (tactic steps)", fontsize=11)
    ax.set_title("Second Try — Fixed Setup + Variable Per-Theorem Cost\n"
                 r"($f = 2$ functions: $\mathtt{plength}$, $\mathtt{papp}$)",
                 fontsize=12)
    ax.legend(fontsize=10)
    ax.set_xlim(0, 20)
    ax.set_ylim(0, 165)

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_03_revised_cost.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# Graph 04 — Third Try: Family of C_manual curves per c_avg
# Numbers from bs_p6.v ROI table (f = 1 new function: _prev / nrev):
#
#   Shared:         C_base = 13 steps
#   Manual bridge:  5 steps  →  C_manual offset = 18
#   Trocq setup:   11 steps  →  C_trocq  offset = 24
#   k ≈ 1.5 tactics per function application in a manual proof
#
#   C_manual(n, c) = 18 + k·c·n
#   C_trocq(n)     = 24 + 2·n   (c_avg does NOT appear here)
#
#   Break-even per c_avg:
#     c=2: n* = 6.0       c=3: n* = 2.4
#     c=4: n* = 1.5       c=5: n* = 1.1
#     c=6: n* = 0.86
# ══════════════════════════════════════════════════════════════════════════
def graph_04():
    n = np.linspace(0, 12, 400)

    C_M_offset = 18   # 13 shared + 5 manual bridge
    C_T_offset = 24   # 13 shared + 11 Trocq setup
    k = 1.5           # tactics per function application (manual)

    c_values = [2, 3, 4, 5, 6]
    ct = C_T_offset + 2 * n

    fig, ax = plt.subplots(figsize=(9, 5.5))

    # Trocq baseline
    ax.plot(n, ct, color=BLUE, lw=3.0, ls="-",
            label=r"$C_{\mathrm{trocq}}(n) = 24 + 2n$  (any $c_{\mathrm{avg}}$)")

    # Manual family
    for c, color in zip(c_values, PALETTE):
        cm = C_M_offset + k * c * n
        n_star = (C_T_offset - C_M_offset) / (k * c - 2)  # 6 / (1.5c - 2)
        y_star = C_T_offset + 2 * n_star

        ax.plot(n, cm, color=color, lw=2.0, ls="--",
                label=fr"$C_M$, $c_{{\mathrm{{avg}}}}={c}$"
                      fr"  (break-even $n^*={n_star:.1f}$)")

        # Mark break-even only if within plot range
        if 0 < n_star <= 12:
            ax.scatter([n_star], [y_star],
                       color=color, zorder=5, s=55, marker="o")

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel("Total proof obligations (tactic steps)", fontsize=11)
    ax.set_title(
        "Third Try — Break-Even Shifts Earlier as Theorem Complexity Grows\n"
        r"($f = 1$, $k = 1.5$ tacts/app;  $C_M = 18 + k \cdot c_{\mathrm{avg}} \cdot n$,"
        r"  $C_T = 24 + 2n$)",
        fontsize=11,
    )
    ax.legend(fontsize=9, loc="upper left")
    ax.set_xlim(0, 12)
    ax.set_ylim(0, 155)

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_04_family.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# Graph 02_const — Second Try Insights: ROI converges to a finite constant
#
# Corrects the "exponentially more efficient" flaw by showing that ROI(n)
# for the revised Second Try model converges to a BOUNDED constant as n→∞.
#
# Second Try model (f=2, C_base=12, trocq_overhead=22):
#   ROI(n) = (C_manual - C_trocq) / C_trocq
#          = (12 + P*n - 34 - 2n) / (34 + 2n)
#          = ((P-2)*n - 22) / (34 + 2n)
#   Asymptote: (P-2)/2
#
# We plot three plausible P_manual values (5, 7, 9) to show that every
# curve converges to its own finite ceiling — none grows without bound.
# ══════════════════════════════════════════════════════════════════════════
def graph_02_const():
    n = np.linspace(0, 80, 800)

    # Three representative per-theorem manual costs
    configs = [
        (5, PALETTE[0], r"$P_{\mathrm{manual}} = 5$"),
        (7, PALETTE[1], r"$P_{\mathrm{manual}} = 7$  (bs_p5 observed)"),
        (9, PALETTE[2], r"$P_{\mathrm{manual}} = 9$  (bs_p6 observed)"),
    ]

    C_base         = 12
    trocq_overhead = 22

    fig, ax = plt.subplots(figsize=(9, 5))

    for P, color, label in configs:
        roi = ((P - 2) * n - trocq_overhead) / (C_base + trocq_overhead + 2 * n)
        asymptote = (P - 2) / 2

        ax.plot(n, roi, color=color, lw=2.2, label=label)
        ax.axhline(asymptote, color=color, lw=1.1, ls="--", alpha=0.6)
        ax.text(81, asymptote,
                fr"  $\to {asymptote:.1f}\times$",
                va="center", fontsize=9, color=color)

    # Zero line
    ax.axhline(0, color="black", lw=0.9, ls="-")
    ax.text(1, 0.08, "break-even (ROI = 0)", fontsize=8.5, color="black", alpha=0.6)

    # Annotation box emphasising the asymptote formula
    ax.annotate(
        r"$\mathrm{ROI}_\infty = \dfrac{P_{\mathrm{manual}} - 2}{2}$  (finite!)",
        xy=(60, 3.2),
        fontsize=10.5,
        ha="center",
        bbox=dict(boxstyle="round,pad=0.4", fc="white", ec=GREY, lw=1),
    )

    ax.set_xlabel("Number of theorems transferred  ($n$)", fontsize=11)
    ax.set_ylabel(r"$\mathrm{ROI}(n) = \dfrac{C_M - C_T}{C_T}$", fontsize=11)
    ax.set_title(
        "Second Try — ROI Converges to a Finite Constant, Not Exponentially\n"
        r"($C_M = 12 + P \cdot n$,  $C_T = 34 + 2n$;  asymptote $= (P-2)/2$)",
        fontsize=11,
    )
    ax.legend(fontsize=10, loc="lower right")
    ax.set_xlim(0, 80)
    ax.set_ylim(-1.5, 4.5)
    ax.yaxis.set_major_formatter(
        ticker.FuncFormatter(lambda y, _: f"{y:.1f}×"))

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_02_const.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ══════════════════════════════════════════════════════════════════════════
# Graph 05 — Third Try: ROI 3D Surface  (three-variable cost equation)
#
# Full ROI equation (slide 365):
#
#   ROI(n, f, c_avg) = [ n·(k·c_avg − 2) − f·W_trocq ]
#                      ─────────────────────────────────
#                      C_base(f) + f·W_trocq + 2n
#
# Here we fix f = 1 and sweep (n, c_avg) to visualise how the two
# remaining variables jointly drive ROI.  The surface makes explicit that
# c_avg multiplies n — a single complex theorem (large c_avg, small n)
# can immediately push ROI above zero.
#
# Parameters (consistent with bs_p6.v / graph_04):
#   k        = 2.2   tactics per function application in a manual proof
#                     (empirical: 11 steps / 5 applications in bs_p6.v)
#   W_trocq  = 11    Trocq setup cost per function
#   C_base   = 13    fixed shared proof obligations (both approaches pay)
#   f        = 1     number of transferred functions (held constant)
#
#   C_trocq_fixed = C_base + f·W_trocq = 24
#   ROI(n, c_avg) = (n·(k·c_avg − 2) − 11) / (24 + 2n)
#   Asymptote (n→∞): (k·c_avg − 2) / 2
#     at c_avg=6: (2.2×6 − 2)/2 = 5.6   (matches slide)
# ══════════════════════════════════════════════════════════════════════════
def graph_05_roi_3d():
    from mpl_toolkits.mplot3d import Axes3D  # noqa: F401 (registers 3D projection)
    from matplotlib import cm as mpl_cm

    # Parameter values (f = 1, consistent with bs_p6.v / graph_04)
    k       = 2.2
    W_trocq = 11
    C_base  = 13
    f       = 1

    C_T_fixed = C_base + f * W_trocq   # 24

    # Grid axes — extend n to ~50 so the asymptotic plateau is visible
    n_vals    = np.linspace(0.5, 50,  180)   # theorems transferred
    c_vals    = np.linspace(1.0,  8,  120)   # average theorem complexity
    N, C = np.meshgrid(n_vals, c_vals)

    ROI = (N * (k * C - 2) - f * W_trocq) / (C_T_fixed + 2 * N)

    # Colour limits: floor at -1; ceiling = actual surface max (rounded up)
    roi_max = float(np.nanmax(ROI))
    vmax = np.ceil(roi_max)          # e.g. 8.0 for k=2.2, c_avg_max=8

    # ── Figure ────────────────────────────────────────────────────────────
    fig = plt.figure(figsize=(11, 7))
    ax  = fig.add_subplot(111, projection="3d")

    surf = ax.plot_surface(
        N, C, ROI,
        cmap=mpl_cm.RdYlGn,      # red (negative) → yellow → green (positive)
        vmin=-1.0, vmax=vmax,
        alpha=0.88,
        linewidth=0,
        antialiased=True,
    )

    # Zero-ROI contour projected onto the ROI plane (z = 0)
    ax.contour(N, C, ROI, levels=[0], colors=["black"], linewidths=1.8, offset=0)

    # Colour bar
    cbar = fig.colorbar(surf, ax=ax, shrink=0.55, aspect=14, pad=0.08)
    cbar.set_label(r"$\mathrm{ROI}(n,\,c_{\mathrm{avg}})$", fontsize=10)
    cbar.ax.yaxis.set_major_formatter(
        ticker.FuncFormatter(lambda y, _: f"{y:.1f}×"))

    # Reference plane at ROI = 0
    n_plane = np.array([[n_vals[0], n_vals[-1]],
                         [n_vals[0], n_vals[-1]]])
    c_plane = np.array([[c_vals[0], c_vals[0]],
                         [c_vals[-1], c_vals[-1]]])
    ax.plot_surface(n_plane, c_plane,
                    np.zeros_like(n_plane),
                    alpha=0.18, color="grey")

    # Labels & title
    ax.set_xlabel(r"Theorems  ($n$)",         fontsize=10, labelpad=8)
    ax.set_ylabel(r"Complexity  ($c_{\mathrm{avg}}$)", fontsize=10, labelpad=8)
    ax.set_zlabel(r"$\mathrm{ROI}$",          fontsize=10, labelpad=6)
    ax.set_title(
        "Third Try — ROI 3D Surface over $(n,\\,c_{\\mathrm{avg}})$\n"
        r"$\mathrm{ROI} = \dfrac{n(k\,c_{\mathrm{avg}}-2) - f\,W_{\mathrm{trocq}}}"
        r"{C_{\mathrm{base}} + f\,W_{\mathrm{trocq}} + 2n}$"
        r"  ($f=1,\ k=2.2,\ W_{\mathrm{trocq}}=11$)",
        fontsize=11,
        pad=14,
    )

    ax.view_init(elev=28, azim=-55)

    fig.tight_layout()
    path = os.path.join(OUT, "_graphs/graph_05_roi_3d.png")
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


# ── Entry point ───────────────────────────────────────────────────────────
if __name__ == "__main__":
    graph_01()
    graph_02()
    graph_02_const()
    graph_03()
    graph_04()
    graph_05_roi_3d()
    print("\nAll graphs generated successfully.")
