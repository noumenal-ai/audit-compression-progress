# Examples

The measurement applied to results that were published without it.

- **[`lambada-openai/`](lambada-openai/README.md)**: GPT-2's published LAMBADA table and four
  released revisions of Pythia-160m, scored on one 5,153-passage sealed panel and reported in the
  five numbers. Route (c), `delta = 0.05`, probability floor 0.01, one audit unit per passage.

Each example directory carries the same five things: a `README.md` stating the target, the route and
what the measurement adds; a `panel_declaration.json` fixing the panel, the unit, the loss and the
route, hashed before any state is scored; a script that scores the model states and writes the
per-audit-unit losses; those losses, each file stamped with the declaration hash and the panel hash
it was produced under; and a script that turns them into `report.json`.

The reports are not computed here. Each example executes the core of
[`../notebooks/audit_cp_report.ipynb`](../notebooks/audit_cp_report.ipynb) and calls its functions,
so the notebook stays the single definition of the five numbers.
