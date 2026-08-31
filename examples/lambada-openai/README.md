# A published perplexity table, re-expressed as audit compression progress

This example takes a real published result, reproduces it on this machine, and reports it in the
five numbers of *Signed Compression Progress on a Sealed Audit is Goodhart-Resistant*. Everything is
in **nats**. `Gamma` is the **slack**; `G - Gamma` is the **lower bound on improvement**.

The point of the exercise is the last section: what a reader is entitled to say after this
measurement that they were not entitled to say after the original table.

---

## 1. The target and why it fits

**Radford, Wu, Child, Luan, Amodei and Sutskever. *Language Models are Unsupervised Multitask
Learners*. OpenAI technical report, 2019. Table 3, LAMBADA columns.**

| model | LAMBADA (PPL) | LAMBADA (ACC) |
|---|---|---|
| 117M | 35.13 | 45.99 |
| 345M | 15.60 | 55.48 |
| 762M | 10.87 | 60.12 |
| 1542M | 8.63 | 63.24 |

Table 3's caption reads, in part, that no training or fine-tuning was performed for any of these
results. The table reports no interval, no seed spread, and no statement of what the evaluation
could have resolved.

It satisfies the constraints:

- **It is real and citable.** The claim under test is the 117M-to-345M step, PPL 35.13 to 15.60 and
  accuracy 45.99 to 55.48 percent.
- **Per-item log-probabilities are obtainable at two model states.** LAMBADA is scored by the log
  probability of a passage's final word, so the benchmark's own unit is already a log loss. The two
  states are the released `gpt2` and `gpt2-medium` weights.
- **It runs here.** Two checkpoints of 124M and 355M parameters, a 1.8 MB evaluation file, Apple
  Silicon MPS in float32.

A second comparison uses the same panel to measure **one training run rather than two model sizes**:

**Biderman et al. *Pythia: A Suite for Analyzing Large Language Models Across Training and Scaling*.
ICML 2023, arXiv:2304.01373.** Pythia releases 154 checkpoints per model at fixed step intervals
with a fixed data order, so `p_0` and `p_T` can be two revisions of the same 160M model rather than
two different models. That is the setting audit compression progress is actually about, and it lets
the increments be checked against the endpoints on a real published trajectory.

### Exact pins

| role | repo | revision | note |
|---|---|---|---|
| panel | `EleutherAI/lambada_openai` (dataset) | `900124bf3b8235c6daf21033af9948b3f07346c4` | `data/lambada_test_en.jsonl`, sha256 `4aa8d02cd17c719165fc8a7887fddd641f43fcafa4b1c806ca8abc31fabdb226`, 5153 records |
| `p_0` (Q1, Q2) | `gpt2` | `607a30d783dfa663caf39e06633721c8d4cfcd7e` | 124M |
| `p_T` (Q1, Q2) | `gpt2-medium` | `6dcaa7a952f72f9298047fd5137cd6e4f05f41da` | 355M |
| `p_0` (Q3, Q4) | `EleutherAI/pythia-160m` | `f711eaa4e5158955f6fcdff84a2145158b739f77` | `step1000` |
| intermediate | `EleutherAI/pythia-160m` | `13af86250de4e88e9c788ba8d7fb5b0e8a4afb7a` | `step16000` |
| intermediate | `EleutherAI/pythia-160m` | `aac0de458f9106a48f9e58f4ad7ba03f86753932` | `step64000` |
| `p_T` (Q3, Q4) | `EleutherAI/pythia-160m` | `b56d9bee36300031aeea723b73c4d62ac7fa71a2` | `step143000`; its weight blob is byte-identical to `main` (LFS sha256 `8d856725c4a8266f10568cc1269948fc851e2aed1fb230036af2eac68e9df072`), so this is the final released model |

Split: the LAMBADA-OpenAI **test** file in full, unfiltered, in file order. No subsetting.

---

## 2. The three quotes

**`p_0` and `p_T`** are the two model states above. Each model's next-token distribution is made
full-support before scoring:

```
q(t | prefix) = (1 - alpha) * p_model(t | prefix) + alpha / V,   alpha = 0.01
```

so `0 <= -ln q <= R` with `R = ln(V / alpha)`. That gives `R = 15.430075` for the GPT-2 vocabulary
(`V = 50257`) and `R = 15.431010` for the Pythia softmax (`V = 50304`). Without the floor a single
unlucky unit produces an infinite loss and no concentration argument applies.

**`p_ref`, the benchmark-owned reference quote, is the uniform code over the same `V`.** This is the
defensible default the task allows, and it is the right default here for three reasons: it is
model-independent, so no released model is privileged; it is the no-knowledge code on the declared
label set, so the terminal level `B = L_Q(p_ref) - L_Q(p_T)` reads as *nats of description length
saved against knowing nothing*; and the floor leaves it unchanged, since mixing a uniform quote with
a uniform quote returns the same quote. Hence `L_Q(p_ref) = ln V` exactly on every unit:
10.824856 nats for GPT-2, 10.825791 for Pythia.

**The audit unit is one LAMBADA passage.** Not one token. The panel holds 5153 passages and about
425,000 GPT-2 tokens; tokens inside a passage are dependent, so `n = 5153`. Section 7 prices exactly
what the other choice would have bought.

Two loss functions are declared on the panel, and both are reported for both comparisons:

- **final word** (`loss_target`): the mean, over the BPE tokens of the passage's final word, of
  `-ln q`. This is the bounded analogue of the metric the paper reports.
- **whole passage** (`loss_passage`): the same mean over every token of the passage at positions
  1 to T-1. Position 0 has no left context and is excluded.

The two model families use different tokenizers, so per-token levels are **not** comparable across
families. Levels and gains are read within a target. The discrimination ratio is dimensionless and
is the only quantity compared across families.

### Pre-registration

`panel_declaration.json` fixes the panel, the unit, both loss functions, `alpha`, `delta`, the route
and the six states. It was written and hashed to
`867eb86c76d2e69c3c1f9b1a0200f35c5f5e01a02b9985e649764c8b65f6caf1` before any state was scored, and
`score_states.py` stamps that hash into every output file. Nothing here selects `alpha`, the metric
or the state pair after seeing a number.

---

## 3. The route, declared honestly

**Route (c), fixed panel**, for both comparisons, with `delta = 0.05` and `N` equal to the number of
model states scored on that target's panel: `N = 2` for the GPT-2 targets and `N = 4` for the Pythia
targets.

All five steering channels are answered `False`, and the grounds differ in strength:

| channel | GPT-2 | Pythia-160m |
|---|---|---|
| reward | False: WebText language-modelling loss only | False: Pile language-modelling loss only |
| early stopping | False: Table 3's caption states no training or fine-tuning was performed for these results | False: a fixed 143,000-step budget declared in advance |
| checkpoint selection | False, *on the paper's account only* | False: checkpoints saved at fixed step intervals and all released |
| hyperparameter selection | False on the same account | False: the suite fixes hyperparameters across the size ladder |
| data selection | False | False: identical data in identical order |

The Pythia declaration is the stronger one. Its whole design is that no downstream score can have
chosen which state is reported, because every state is reported. The GPT-2 declaration rests on the
paper's own description and cannot be checked against the released artifacts, so Section 6 prices
what a violation would cost instead of assuming it away.

`N` is where this study's own reuse of the panel is charged. The panel was scored at several states;
route (c)'s uniform-deviation event has to cover all of them. Section 6 also prices the stricter
union over every quote in this document.

**What route (c) does not cover.** LAMBADA is built from BookCorpus, and the Pile contains
BookCorpus2 and Books3, so the Pythia panel is probably not disjoint from Pythia's training corpus.
That is target validity, not audit steering: the bound is a statement about `Q` as declared, and it
carries no claim about behaviour on text the model has not seen. The same caveat applies to WebText,
whose overlap with evaluation sets the GPT-2 paper analyses in its own Section 4.

---

## 4. The five numbers

Computed by the functions in `notebooks/audit_cp_report.ipynb`; `report.py` executes the notebook's
Sections 1 to 8 and calls `declare_panel`, `compute_slack`, `five_numbers`, `audit_cp_report`,
`reconcile_increments`, `check_independent_units` and `panel_size_for_resolution` directly.

| | Q1 GPT-2, final word | Q2 GPT-2, passage | Q3 Pythia, final word | Q4 Pythia, passage |
|---|---|---|---|---|
| `p_0` | `gpt2` | `gpt2` | `pythia-160m@step1000` | `pythia-160m@step1000` |
| `p_T` | `gpt2-medium` | `gpt2-medium` | `pythia-160m@step143000` | `pythia-160m@step143000` |
| `L_Q(p_ref)` | 10.8249 | 10.8249 | 10.8258 | 10.8258 |
| `L_Q(p_0)` | 3.2249 | 3.5979 | 6.5211 | 4.3400 |
| `L_Q(p_T)` | 2.5449 | 3.3587 | 3.0343 | 3.3967 |
| **1. terminal level `B`** | **+8.2800** | **+7.4662** | **+7.7915** | **+7.4291** |
| **2. signed gain `G`** | **+0.6799** | **+0.2392** | **+3.4868** | **+0.9433** |
| **3. slack `Gamma`** | **0.636342** | **0.636342** | **0.684865** | **0.684865** |
| **4. lower bound `G - Gamma`** | **+0.0436** | **-0.3971** | **+2.8019** | **+0.2584** |
| **5. ratio `G / Gamma`** | **1.07** | **0.38** | **5.09** | **1.38** |
| verdict | improvement demonstrated, barely | **no improvement demonstrated at this resolution** | improvement demonstrated | improvement demonstrated |

Route (c) parameters: `n = 5153`, `delta = 0.05`; `R = 15.430075`, `N = 2`, `Delta = 0.318171` for
Q1 and Q2; `R = 15.431010`, `N = 4`, `Delta = 0.342432` for Q3 and Q4.

### The published metrics, reproduced

The same forward passes also produce the benchmark's own quantities: per-word LAMBADA perplexity
(`exp` of the mean unfloored negative log likelihood of the final word) and teacher-forced greedy
exact match.

| state | our PPL | our ACC | paper |
|---|---|---|---|
| `gpt2` | 40.055 | 32.56% | 35.13 / 45.99% (117M) |
| `gpt2-medium` | 18.265 | 42.98% | 15.60 / 55.48% (345M) |
| `pythia-160m@1k` | 2591.689 | 6.48% | figure only |
| `pythia-160m@16k` | 37.930 | 34.15% | figure only |
| `pythia-160m@64k` | 28.069 | 37.07% | figure only |
| `pythia-160m@143k` | 37.255 | 35.38% | figure only |

The absolute levels do not match the paper, and the paper says why. Its Section 3.1 reports the use
of invertible de-tokenizers worth 2.5 to 5 perplexity points, which are not part of the released
`lambada_test.jsonl`. Its Section 3.3 states that the accuracy column adds a stop-word filter, which
raises the 1542M accuracy from 52.66 to 63.24 percent. Neither is released.

The interesting part is what survives that. In log space the paper's gain is
`ln(35.13) - ln(15.60) = 0.8118` nats and ours is `ln(40.055) - ln(18.265) = 0.7853`, a difference of
0.027 nats, while the two levels differ from the paper's by 0.131 and 0.158 nats. Undisclosed
preprocessing moves the level by five times what it moves the difference. That is an argument for
reporting the signed gain and not only the level, and it is visible only because the unit is nats.

Our reproduction is not loose. The standard evaluation harness for this file reports a LAMBADA
perplexity of about 40 for stock `gpt2`, against the paper's 35.13, and discussion of that gap on the
harness's own issue tracker attributes it to the missing preprocessing. Our 40.055 sits on the
harness value, not on the paper's.

---

## 5. The trajectory: increments against endpoints

The Pythia revision ladder, in audit level `B = L_Q(p_ref) - L_Q(p_t)`. Higher is better.

**Final word (Q3):**

| state | `L_Q` | `B` | increment |
|---|---|---|---|
| `step1000` | 6.5211 | +4.3047 | |
| `step16000` | 3.0461 | +7.7798 | **+3.4751** |
| `step64000` | 2.7978 | +8.0281 | **+0.2483** |
| `step143000` | 3.0343 | +7.7915 | **-0.2366** |

**Whole passage (Q4):** increments `+0.8986`, `+0.0689`, `-0.0243`.

Two things follow.

**The final leg is negative on both metrics.** The released final Pythia-160m is worse on this panel
than its own step-64000 checkpoint: 2.7978 to 3.0343 nats on the final word, 37.07 to 35.38 percent
accuracy. The weights at `step143000` are byte-identical to `main`, so this is the shipped model.
The reported `G = 3.4868` is already net of that regression, because the increments are signed.
Neither paper reports the sign structure of its own trajectory; both report endpoints.

Being scrupulous: `|-0.2366| < Gamma = 0.6849`, so **the regression is inside the panel's
resolution and is not demonstrated either**. The honest statement is that this panel demonstrates a
large gain over the whole run and cannot resolve any of the last three legs individually. Both legs
after the first are inside `Gamma`.

**The increments reconcile to the endpoints exactly.** `reconcile_increments` returns a residual of
`0.00e+00` on both ladders: `+3.4751 + 0.2483 - 0.2366 = +3.486808`, which is `B(p_T) - B(p_0)` to
the last digit. A third party checks the reported total against two levels, without the intermediate
states and without a term that grows with trajectory length.

---

## 6. Sensitivities, priced rather than waved at

**Union over everything in this document.** All four targets share one panel. A reader who wants a
single 95 percent statement covering every number here needs `N = 12`, the total number of
(state, target) quotes scored:

| | `Gamma` union | lower bound union | |
|---|---|---|---|
| Q1 | 0.7553 | **-0.0754** | **flips to non-positive** |
| Q2 | 0.7553 | -0.5161 | still non-positive |
| Q3 | 0.7554 | +2.7314 | positive |
| Q4 | 0.7554 | +0.1879 | positive |

**Q1 does not survive it.** Read across all four reported targets at once, GPT-2's published LAMBADA
improvement is *not* demonstrated at this panel's resolution. Read on its own declared target with
its own `N = 2`, it is, by 0.0436 nats. Both statements are in this document and the second does not
replace the first.

**Route (d): how much feedback would erase each bound.** If any audit-derived signal had in fact
reached training, route (d) applies with an honest bit count. The largest transcript budget `B` that
still leaves a positive lower bound:

| target | bits |
|---|---|
| Q1 | **2.9** |
| Q2 | none; there is no positive bound to protect |
| Q3 | **185.5** |
| Q4 | 9.6 |

Three bits. If three bits of LAMBADA-derived signal had influenced which GPT-2 checkpoint was
released, Q1's bound is gone. Q3, measured on a run whose checkpoint schedule is fixed and public,
absorbs 185 bits. That difference is a statement about how much eval-driven iteration each claim can
carry, and neither paper is in a position to make it.

**How much the worst-case slack costs.** `Gamma` is a Hoeffding radius at `R = 15.43`, and the
empirical paired spread is far smaller. Reported as a diagnostic only, with no claim resting on it:

| target | paired sd of per-unit gain | normal-approximation 95% half-width | `Gamma` / half-width |
|---|---|---|---|
| Q1 | 1.2682 | 0.0346 | 18.4 |
| Q2 | 0.1151 | 0.0031 | 202.6 |
| Q3 | 2.4563 | 0.0671 | 10.2 |
| Q4 | 0.2042 | 0.0056 | 122.8 |

The worst-case slack is 10 to 200 times a variance-based interval. That is the price of a bound that
holds without a distributional assumption, and Q2 is where it bites hardest: a 0.24-nat gain with a
0.115-nat paired spread is unmistakable to a t-test and invisible to this panel.

---

## 7. The independent-unit rule, priced

`n` is the passage count, 5153, not the token count. Substituting tokens:

| target | tokens | per record | `Gamma` correct | `Gamma` with tokens | bound correct | bound with tokens |
|---|---|---|---|---|---|---|
| Q1 | 6,573 | 1.3 | 0.6363 | 0.5634 | +0.0436 | +0.1165 |
| **Q2** | **425,077** | **82.5** | **0.6363** | **0.0701** | **-0.3971** | **+0.1692** |
| Q3 | 7,054 | 1.4 | 0.6849 | 0.5854 | +2.8019 | +2.9015 |
| Q4 | 413,491 | 80.2 | 0.6849 | 0.0765 | +0.2584 | +0.8668 |

Counting tokens instead of passages converts Q2 from *no improvement demonstrated* into *improved by
at least 0.169 nats*, and inflates Q4's bound by a factor of 3.4. Tokens inside one passage are not
independent draws, so that bound is not one the panel supports. This is the single easiest way to
manufacture a positive result from this data, and it costs nothing to check.

---

## 8. WHAT NEW CLAIMS ARE AVAILABLE

The original table says: *going from 117M to 345M parameters lowers LAMBADA perplexity from 35.13 to
15.60 and raises accuracy from 45.99 to 55.48 percent.* It is a pair of point estimates on one
evaluation set with no uncertainty attached. Here is what this measurement adds, claim by claim.

### 8.1 A lower bound on improvement, in nats, with no horizon or size term

> On the declared target (LAMBADA-OpenAI final word, GPT-2 BPE, probability floor 0.01), with
> probability at least 0.95 over the draw of the panel, `gpt2-medium` is at least **0.0436 nats per
> passage** better than `gpt2`.
>
> On the declared target (LAMBADA-OpenAI whole passage, NeoX BPE, floor 0.01), Pythia-160m improved
> by at least **0.2584 nats per passage** between step 1,000 and step 143,000, and by at least
> **2.8019 nats** on the final-word target.

`Gamma = 2 * R * sqrt(ln(2N/delta) / (2n))` contains `n`, `R`, `delta` and `N`. It contains no term
in the parameter count, the number of training steps, the optimizer, the architecture, or the
trajectory taken. The same panel prices a 1,000-step run and a 143,000-step run identically, and a
160M model and a 355M model identically. That is why the Pythia claim above covers a 143,000-step
adaptive trajectory without a union bound over steps, and why the GPT-2 claim would read the same if
the two states were 1.5B and 175B.

The original table cannot make this claim in any form. A perplexity of 15.60 is not a bound; it is a
sample mean with no stated confidence, on a panel of unstated resolving power.

### 8.2 A resolution, available before the run

> This panel can demonstrate an improvement no smaller than **0.6363 nats** (GPT-2 targets) or
> **0.6849 nats** (Pythia targets). Anything smaller is inside its slack.

`Gamma` depends on nothing about the model, so it is computable the moment the panel is fixed and
before a single gradient step. LAMBADA-OpenAI at `delta = 0.05` with a 0.01 floor resolves 0.64 nats
and no better. To resolve 0.25 nats the GPT-2 target would need 33,386 independent passages; to resolve 0.10 nats,
**208,661**. The Pythia target, carrying `N = 4`, needs 38,672 and **241,697**. The panel has 5,153.

This converts an open question into a design constraint. The measured gain on Q1, 0.6799 nats,
clears the panel's resolution by 7 percent. Had the paper compared two adjacent checkpoints instead
of two model sizes, or reported the whole-passage loss instead of the final word, the same panel
would have resolved nothing, which is precisely what Q2 shows.

### 8.3 A discrimination ratio, comparable across substrates

> `G / Gamma` = **1.07** for the GPT-2 size step, **5.09** for the Pythia training run, on the same
> panel, at the same confidence, against the same benchmark.

This is the one quantity here that crosses the tokenizer boundary. `L_Q(p_T) = 2.5449` for
`gpt2-medium` and `3.0343` for the final Pythia-160m, and those two numbers may not be compared:
they are means over different tokenizations of the same strings, against different reference codes.
`1.07` and `5.09` may be. They say that the published size step is a *marginal* signal on this
evaluation while the training run of a model with a third as many parameters is a strong one, and
they say it without either level having to be transportable.

The ratio exceeds 1 exactly when the lower bound is positive, so it also carries the verdict, and it
is the number to quote when two systems are audited on panels that do not share a unit.

### 8.4 A statement that is already net of regression

> Pythia-160m's improvement of 3.4868 nats over its released trajectory is net of a 0.2366-nat
> regression in its final leg, and the three increments sum to the endpoint difference exactly.

The signed increments make the reported total auditable from two levels: `+3.4751`, `+0.2483`,
`-0.2366`, residual `0.00e+00` against `B(p_T) - B(p_0)`. Neither source paper reports this. The
Pythia paper's LAMBADA trajectory appears as a line in a figure with no resolution attached, so the
dip cannot be told from ink. Here it is a signed number with a slack next to it, and the honest
verdict is that the dip is real in the sample and **not demonstrated** at this panel's resolution.

### 8.5 The accuracy delta, against its own worst-case paired radius

The task asks specifically whether the reported accuracy delta exceeds its own worst-case paired
radius. Pairing the two states on the same 5,153 items, the per-item difference lies in `{-1, 0, +1}`,
and a Hoeffding radius on its mean at `delta = 0.05` is

```
2 * sqrt(ln(2/0.05) / (2 * 5153)) = 0.037838,  that is 3.78 percentage points.
```

| comparison | delta | radius | verdict |
|---|---|---|---|
| paper, 117M to 345M | **+9.49 pp** | 3.78 pp | **exceeds** |
| our reproduction, `gpt2` to `gpt2-medium` | **+10.42 pp** (801 items up, 264 down) | 3.78 pp | **exceeds** |
| Pythia, step 1k to step 143k | +28.90 pp (1540 up, 51 down) | 3.78 pp | exceeds |

So the paper's accuracy claim does survive its own worst-case paired radius, with margin, even
though its stop-word filter is unreleased and our raw reproduction lands 13 points lower. The
accuracy delta is on firmer ground than the whole-passage nats claim, and the reason is exactly one
number: the 0/1 loss has range `R = 1` while the floored log loss has `R = 15.43`, so on the same
5,153 items this panel resolves accuracy about fifteen times more finely. Asking for calibrated
probabilities instead of a hit rate costs a factor of `R`, and that trade is now a number rather than
an intuition.

### 8.6 What none of this licenses

The bound is a statement about the declared `Q`, under the declared masking policy, in nats per
passage. It is not a forecast of behaviour on other text, it says nothing about capability, safety or
values, and it does not transfer across the two tokenizers. Levels are comparable only within a
target version. The panel is not disjoint from either model's training corpus, so even the `Q`
statement is a statement about a target the models may have partly memorized.

---

## 9. Where this came out weaker than hoped

Reported because it is more informative than a tidied-up positive.

1. **Q2 is negative.** The whole-passage log-loss gain from `gpt2` to `gpt2-medium` is 0.2392 nats
   against a slack of 0.6363. **No improvement is demonstrated at this resolution.** The gain is
   almost certainly real, with a paired standard deviation of 0.115 nats over 5,153 items, but this
   panel at this loss range cannot demonstrate it, and that is the reportable fact.
2. **Q1 is thin and does not survive the union.** At `N = 2` the bound is `+0.0436` with a ratio of
   1.07. At the `N = 12` union covering everything in this document it is `-0.0754`. The headline
   GPT-2 result therefore sits on the boundary, and its sign depends on an accounting choice that is
   declared rather than derived.
3. **Q1's bound absorbs 2.9 bits.** If the released GPT-2 checkpoints were chosen with even a few
   bits of LAMBADA-derived information, the bound is gone. The declaration rests on the paper's
   caption and cannot be verified from the artifacts.
4. **The worst-case slack is 10 to 200 times a variance-based interval.** Hoeffding at `R = 15.43`
   against paired spreads of 0.115 to 2.46 is very loose. A bounded-loss log-probability audit over
   a 50,000-token vocabulary is intrinsically expensive, and `n` has to be large before it stops
   dominating.
5. **The levels do not reproduce the paper's.** 40.06 against 35.13, and 32.56 percent against
   45.99. The paper documents both causes and releases neither the de-tokenizers nor the stop-word
   filter. The gain reproduces to 0.027 nats, the level does not, so the terminal level `B` reported
   here is only as portable as the released preprocessing.
6. **`alpha` was not optimized.** It was fixed at 0.01 in the pre-registered declaration. A larger
   floor would shrink `R` and improve every ratio, and choosing it after seeing the sweep would be
   the adaptivity that route (c) does not cover. It was left alone.

---

## 10. Files and how to reproduce

```
panel_declaration.json   pre-registered; sha256 867eb86c76d2e69c3c1f9b1a0200f35c5f5e01a02b9985e649764c8b65f6caf1
score_states.py          downloads the pinned panel and states, scores them, writes raw/
raw/part_gpt2.npz        per-audit-unit losses for the two GPT-2 states (0.29 MB)
raw/part_pythia.npz      per-audit-unit losses for the four Pythia revisions (0.58 MB)
report.py                executes the notebook's core and emits report.json
report.json              the computed report objects, all five numbers, every sensitivity
README.md                this file
```

`raw/*.npz` hold one value per audit unit per state, never per token: the floored losses under both
metrics, the unfloored summed log likelihood of the final word, the greedy exact-match flag, and the
token counts. Each part carries the declaration hash and the panel file hash it was produced under,
and `report.py` refuses parts that disagree.

```bash
pip install "transformers==4.46.3" tokenizers safetensors        # torch and numpy assumed
python3 score_states.py        # about 42 minutes of MPS compute for all six states
python3 report.py              # prints the tables above and writes report.json
```

Measured on Apple Silicon, torch 2.8.0, MPS, float32: 73 s for `gpt2`, 269 to 326 s for each Pythia
revision, and 1291 s for `gpt2-medium` while sharing the device with a second scoring process.
Downloads total about 3.3 GB across six checkpoints and are cached.

`report.py` does not reimplement the measurement. It locates `notebooks/audit_cp_report.ipynb`,
executes its Sections 1 to 8, and calls the notebook's own `declare_panel`, `compute_slack`,
`five_numbers`, `audit_cp_report`, `reconcile_increments`, `check_independent_units` and
`panel_size_for_resolution`. Changing the notebook changes these numbers.
