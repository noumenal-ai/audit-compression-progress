#!/usr/bin/env python3
"""Score the LAMBADA-OpenAI panel under six pinned model states and write per-item losses.

Every state, every revision and the panel file are pinned by commit sha in
panel_declaration.json, which was written and hashed before this script was run.

Output: raw/per_item_losses.npz, one block of arrays per state, all of length n = 5153
(one entry per independent audit unit, never per token).

Run:  python3 score_states.py            # all six states, ~10 min on Apple Silicon MPS
      python3 score_states.py --states gpt2 gpt2-medium
"""

import argparse
import hashlib
import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np
import torch

HERE = Path(__file__).resolve().parent
DECL = json.loads((HERE / "panel_declaration.json").read_text())

PANEL_REPO = DECL["panel"]["source_repo"]
PANEL_REV = DECL["panel"]["source_revision"]
PANEL_FILE = DECL["panel"]["file"]
ALPHA = float(DECL["quote_construction"]["alpha"])

STATES = {s["id"]: s for s in DECL["states"]}
ORDER = [s["id"] for s in DECL["states"]]


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_panel():
    from huggingface_hub import hf_hub_download

    path = hf_hub_download(PANEL_REPO, PANEL_FILE, repo_type="dataset", revision=PANEL_REV)
    rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
    texts = [r["text"] for r in rows]
    assert len(texts) == DECL["panel"]["expected_n"], (
        "panel size %d does not match the declared %d" % (len(texts), DECL["panel"]["expected_n"])
    )
    return texts, path, sha256_file(path)


def pick_device():
    if torch.backends.mps.is_available():
        return "mps"
    return "cpu"


@torch.no_grad()
def score_state(state_id, texts, device, batch_size=16):
    """Return per-audit-unit arrays for one model state.

    Scored positions: every token of the passage except position 0, which has no left context.
    The final word's tokens are flagged separately. Sub-token values are reduced to one number
    per passage before they leave this function.
    """
    from transformers import AutoModelForCausalLM, AutoTokenizer

    spec = STATES[state_id]
    repo, rev = spec["repo"], spec["revision"]
    tok = AutoTokenizer.from_pretrained(repo, revision=rev)
    kw = {}
    if repo.startswith("EleutherAI/"):
        kw["use_safetensors"] = False  # the .bin shard is half the size on this repo
    model = AutoModelForCausalLM.from_pretrained(repo, revision=rev, torch_dtype=torch.float32, **kw)
    model.eval().to(device)
    V = int(model.get_output_embeddings().weight.shape[0])
    floor = ALPHA / V
    R = math.log(V / ALPHA)

    n = len(texts)
    enc_full, enc_ctx = [], []
    for t in texts:
        ctx, _word = t.rsplit(" ", 1)
        enc_full.append(tok.encode(t))
        enc_ctx.append(tok.encode(ctx))

    out = {k: np.zeros(n, dtype=np.float64) for k in
           ("loss_target", "loss_passage", "sum_logp_target", "sum_logp_passage")}
    out["n_tgt_tok"] = np.zeros(n, dtype=np.int32)
    out["n_pass_tok"] = np.zeros(n, dtype=np.int32)
    out["greedy_ok"] = np.zeros(n, dtype=bool)

    order = np.argsort([len(e) for e in enc_full])  # length-sorted batching, results written by index
    t0 = time.time()
    for bstart in range(0, n, batch_size):
        idx = order[bstart:bstart + batch_size]
        seqs = [enc_full[i] for i in idx]
        L = max(len(s) for s in seqs)
        ids = torch.zeros(len(seqs), L, dtype=torch.long)
        mask = torch.zeros(len(seqs), L, dtype=torch.long)
        for j, s in enumerate(seqs):
            ids[j, : len(s)] = torch.tensor(s)
            mask[j, : len(s)] = 1
        ids, mask = ids.to(device), mask.to(device)
        logits = model(input_ids=ids, attention_mask=mask).logits.float()
        logprobs = torch.log_softmax(logits[:, :-1, :], dim=-1)          # predicts positions 1..L-1
        tgt = ids[:, 1:]
        lp_true = logprobs.gather(-1, tgt.unsqueeze(-1)).squeeze(-1)     # [B, L-1]
        argmax_ok = (logprobs.argmax(-1) == tgt)
        lp_true = lp_true.cpu().numpy()
        argmax_ok = argmax_ok.cpu().numpy()

        for j, i in enumerate(idx):
            T = len(enc_full[i])
            n_ctx = len(enc_ctx[i])
            lp = lp_true[j, : T - 1].astype(np.float64)                  # positions 1..T-1
            ok = argmax_ok[j, : T - 1]
            # continuation tokens are the passage positions >= n_ctx; their prediction slots are
            # offset by one because slot k predicts position k+1
            k0 = max(n_ctx - 1, 0)
            lp_t = lp[k0:]
            floored_all = -np.log((1.0 - ALPHA) * np.exp(lp) + floor)
            floored_tgt = -np.log((1.0 - ALPHA) * np.exp(lp_t) + floor)
            out["loss_passage"][i] = floored_all.mean()
            out["loss_target"][i] = floored_tgt.mean()
            out["sum_logp_passage"][i] = lp.sum()
            out["sum_logp_target"][i] = lp_t.sum()
            out["n_pass_tok"][i] = lp.size
            out["n_tgt_tok"][i] = lp_t.size
            out["greedy_ok"][i] = bool(ok[k0:].all())

        if (bstart // batch_size) % 40 == 0:
            done = bstart + len(idx)
            print("    %5d/%d  %.1fs" % (done, n, time.time() - t0), flush=True)

    assert np.all(out["n_tgt_tok"] >= 1) and np.all(out["n_pass_tok"] >= 1)
    assert out["loss_target"].max() <= R + 1e-9 and out["loss_passage"].max() <= R + 1e-9
    del model
    if device == "mps":
        torch.mps.empty_cache()
    return out, {"state": state_id, "repo": repo, "revision": rev, "V": V, "R": R,
                 "alpha": ALPHA, "seconds": round(time.time() - t0, 1),
                 "mean_tgt_tokens_per_unit": float(out["n_tgt_tok"].mean()),
                 "mean_passage_tokens_per_unit": float(out["n_pass_tok"].mean())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--states", nargs="*", default=ORDER)
    ap.add_argument("--batch-size", type=int, default=16)
    ap.add_argument("--out", default=str(HERE / "raw" / "per_item_losses.npz"))
    args = ap.parse_args()

    decl_sha = hashlib.sha256((HERE / "panel_declaration.json").read_bytes()).hexdigest()
    print("declaration sha256:", decl_sha)
    texts, panel_path, panel_sha = load_panel()
    print("panel: %d units, sha256 %s" % (len(texts), panel_sha))
    device = pick_device()
    print("device:", device, "| torch", torch.__version__)

    blocks, meta = {}, {"declaration_sha256": decl_sha, "panel_sha256": panel_sha,
                        "panel_file": PANEL_FILE, "panel_repo": PANEL_REPO,
                        "panel_revision": PANEL_REV, "n_units": len(texts),
                        "torch": torch.__version__, "device": device, "states": []}
    for sid in args.states:
        print("\nscoring", sid, "(%s @ %s)" % (STATES[sid]["repo"], STATES[sid]["revision"][:10]))
        out, m = score_state(sid, texts, device, batch_size=args.batch_size)
        meta["states"].append(m)
        for k, v in out.items():
            blocks["%s/%s" % (sid, k)] = v
        print("  V=%d  R=%.6f  mean loss_target=%.4f  mean loss_passage=%.4f  acc=%.4f  (%.1fs)"
              % (m["V"], m["R"], out["loss_target"].mean(), out["loss_passage"].mean(),
                 out["greedy_ok"].mean(), m["seconds"]))

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(args.out, meta=np.array(json.dumps(meta)), **blocks)
    print("\nwrote", args.out, "(%.2f MB)" % (os.path.getsize(args.out) / 1e6))


if __name__ == "__main__":
    sys.exit(main())
