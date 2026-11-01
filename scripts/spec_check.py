#!/usr/bin/env python3
"""The acceptance check of armada-lean. Design record: `docs/spec-module-design.md`.

Usage: python3 scripts/spec_check.py [--json [THEOREM_NAME]]
Run from the repo root. Exit 0 means every check passed.

The check is `lake build` plus one computed report (`scripts/spec_report.lean`). It
reads no stored list of names, counts or signatures. Every set below is computed
from the checked environment on each run.

- build_ok: `lake build` exits 0. The build checks every proof and runs
  `#check_spec_bindings` in each `ArmadaLean/Spec/` module.
- signatures_ok: every spec theorem has its spec definition `N.Spec.x`, and the
  theorem's type is definitionally equal to it; every spec definition belongs to a
  spec theorem.
- axioms_ok: every axiom of every spec theorem and witness is a Lean core axiom
  (module `Init`), `sorryAx` (an open proof, reported in `sorry`), or a declared
  primitive of the model: an axiom whose type is not a proposition
  (`writing-lean.md` §11: "It never asserts a property").
- reach_ok: a spec entry with a binder of a machine state type also has a
  `ReachableState` binder, or its spec definition says "Every state: REASON".
- nonvacuity_ok: every spec entry with a hypothesis has its witness
  `N.Spec.x.witness : spec_premise% N.Spec.x`, with allowed axioms. A witness
  proved by `sorry` is open required work (`witness_open`).
- sorry: the spec theorems whose axioms include `sorryAx`.
- vacuous_defs: no `def … := True` / `:= False` body (`verification.md` §5).
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import spec_lib  # noqa: E402
import gate_extra  # noqa: E402

ROOT = Path.cwd()


def say(json_mode: bool, msg: str) -> None:
    print(msg, file=sys.stderr if json_mode else sys.stdout)


def main() -> int:
    t0 = time.monotonic()
    argv = sys.argv[1:]
    json_mode = bool(argv) and argv[0] == "--json"
    theorem = argv[1] if json_mode and len(argv) > 1 else ""

    out_dir = ROOT / ".scratch" / "check"
    out_dir.mkdir(parents=True, exist_ok=True)
    build = subprocess.run([spec_lib.LAKE, "build"], cwd=ROOT, capture_output=True, text=True)
    (out_dir / "build.log").write_text(build.stdout + build.stderr, encoding="utf-8")
    build_ok = build.returncode == 0
    say(json_mode, ("PASS" if build_ok else "FAIL") + " build"
        + ("" if build_ok else f" (exit {build.returncode}, see .scratch/check/build.log)"))

    fails: dict[str, list[str]] = {k: [] for k in ("signatures", "axioms", "reach", "nonvacuity")}
    members: list[dict] = []
    helpers: list[dict] = []
    sorry: list[str] = []
    witness_open: list[str] = []
    every_state: list[str] = []
    vacuous: list[str] = []
    if build_ok:
        report = spec_lib.run_report(ROOT)
        (out_dir / "report.json").write_text(json.dumps(report), encoding="utf-8")
        members, helpers = spec_lib.classify(spec_lib.source_theorems(ROOT, report))
        ax_info = report["axiom_info"]

        def bad_axioms(axs: list[str]) -> list[str]:
            bad = []
            for a in axs:
                info = ax_info[a]
                if a == "sorryAx" or info["core"] or not info["prop"]:
                    continue
                bad.append(a)
            return bad

        member_specs = set()
        for t in members:
            name = t["name"]
            if "sorryAx" in t["axioms"]:
                sorry.append(name)
            for a in bad_axioms(t["axioms"]):
                fails["axioms"].append(f"{name} depends on the axiom {a}, which asserts a property")
            spec = t["spec"]
            if spec is None:
                fails["signatures"].append(f"{name} has no spec definition")
                continue
            member_specs.add(spec["name"])
            if spec["binding_error"]:
                fails["signatures"].append(spec["binding_error"])
            if spec["raw_state"] and not spec["reach_state"]:
                reason = spec_lib.every_state_reason(spec["doc"])
                if reason:
                    every_state.append(name)
                else:
                    fails["reach"].append(f"{name} takes a raw state and no ReachableState, and "
                                          f"{spec['name']} has no 'Every state:' line")
            if spec["needs_witness"]:
                w = spec["witness"]
                if w is None:
                    fails["nonvacuity"].append(f"{name} has hypotheses and no witness "
                                               f"{spec['name']}.witness")
                elif not w["type_ok"]:
                    fails["nonvacuity"].append(f"{w['name']} does not prove spec_premise% "
                                               f"{spec['name']}")
                else:
                    for a in bad_axioms(w["axioms"]):
                        fails["nonvacuity"].append(f"{w['name']} depends on the axiom {a}, "
                                                   "which asserts a property")
                    if "sorryAx" in w["axioms"]:
                        witness_open.append(name)
        for d in report["spec_defs"]:
            if d not in member_specs:
                fails["signatures"].append(f"{d} belongs to no spec theorem")
        member_witnesses = {m["spec"]["name"] + ".witness" for m in members
                            if m["spec"] and m["spec"]["needs_witness"]}
        for w in report["witnesses"]:
            if w not in member_witnesses:
                fails["nonvacuity"].append(f"{w} witnesses no spec entry with hypotheses")
        for path in sorted((ROOT / "ArmadaLean").rglob("*.lean")):
            for k, line in enumerate(path.read_text(encoding="utf-8").split("\n"), 1):
                if re.search(r":=\s*(True|False)\s*$", line):
                    vacuous.append(f"{path.relative_to(ROOT)}:{k}")
    else:
        for k in fails:
            fails[k].append("not run: the build failed")

    if build_ok:
        try:
            lint_result = gate_extra.check_lint(ROOT)
        except RuntimeError as e:
            lint_result = {"lint_ok": False, "lint_error": str(e)}
        try:
            decision_result = gate_extra.check_decision_scope(ROOT)
        except RuntimeError as e:
            decision_result = {"decision_ok": False, "decision_error": str(e)}
        try:
            counterexamples_result = gate_extra.check_counterexamples(ROOT)
        except RuntimeError as e:
            counterexamples_result = {"counterexamples_ok": False, "counterexamples_error": str(e)}
        (out_dir / "lint.json").write_text(json.dumps(lint_result), encoding="utf-8")
        (out_dir / "decision_scope.json").write_text(json.dumps(decision_result), encoding="utf-8")
        (out_dir / "counterexamples.json").write_text(json.dumps(counterexamples_result), encoding="utf-8")
    else:
        lint_result = {"lint_ok": False, "lint_error": "not run: the build failed"}
        decision_result = {"decision_ok": False, "decision_error": "not run: the build failed"}
        counterexamples_result = {"counterexamples_ok": False,
                                  "counterexamples_error": "not run: the build failed"}

    ok = {k: build_ok and not v for k, v in fails.items()}
    for k, v in fails.items():
        say(json_mode, ("PASS " if ok[k] else "FAIL ") + k)
        for line in v:
            say(json_mode, f"  {line}")
    say(json_mode, ("PASS" if not vacuous else "FAIL") + " no vacuous body")
    for v in vacuous:
        say(json_mode, f"  {v}")
    say(json_mode, ("PASS" if lint_result["lint_ok"] else "FAIL") + " lint")
    for f in lint_result.get("lint_regressions", []):
        say(json_mode, f"  {f} higher than the baseline")
    for f in lint_result.get("lint_lowered_fields", []):
        say(json_mode, f"  {f} lower than the baseline (run scripts/update_gate_baseline.py)")
    if "lint_error" in lint_result:
        say(json_mode, f"  {lint_result['lint_error']}")
    say(json_mode, ("PASS" if decision_result["decision_ok"] else "FAIL") + " decisionScope")
    for f in decision_result.get("decision_new_findings", []):
        say(json_mode, f"  new: {f['file']}:{f['line']} {f['declaration']} ({f['kind']})")
    for f in decision_result.get("decision_larger_findings", []):
        say(json_mode,
            f"  larger: {f['file']}:{f['line']} {f['declaration']} ({f['kind']}) size {f['size']}")
    if "decision_error" in decision_result:
        say(json_mode, f"  {decision_result['decision_error']}")
    say(json_mode, ("PASS" if counterexamples_result["counterexamples_ok"] else "FAIL")
        + " counterexamples")
    for c in counterexamples_result.get("counterexamples", []):
        if not c["ok"]:
            say(json_mode, f"  {c['file']} (exit {c['exit_code']}, sorryAx={c['sorryAx']})")
    if "counterexamples_error" in counterexamples_result:
        say(json_mode, f"  {counterexamples_result['counterexamples_error']}")
    say(json_mode, f"SPEC {len(members)} spec theorems, {len(helpers)} helpers")
    for n in sorted(sorry):
        say(json_mode, f"SORRY {n}")
    say(json_mode, f"SORRY_COUNT {len(sorry)}")
    for n in sorted(witness_open):
        say(json_mode, f"WITNESS_OPEN {n}")
    runtime = round(time.monotonic() - t0, 1)
    say(json_mode, f"RUNTIME {runtime}s")

    passed = (build_ok and all(ok.values()) and not vacuous
              and lint_result["lint_ok"] and decision_result["decision_ok"]
              and counterexamples_result["counterexamples_ok"])
    if json_mode:
        print(json.dumps({
            "build_ok": build_ok,
            "sorry": sorted(sorry),
            "sorry_count": len(sorry),
            "axioms_ok": ok["axioms"],
            "signatures_ok": ok["signatures"],
            "nonvacuity_ok": ok["nonvacuity"],
            "reach_ok": ok["reach"],
            "theorem_under_test": theorem,
            "theorem_in_sorry": bool(theorem) and any(
                n == theorem or n.endswith("." + theorem) for n in sorry),
            "spec_count": len(members),
            "helper_count": len(helpers),
            "witness_open": sorted(witness_open),
            "every_state": sorted(every_state),
            "vacuous_defs": vacuous,
            "failures": {k: v for k, v in fails.items() if v},
            "lint_ok": lint_result["lint_ok"],
            "lint_summary": lint_result.get("lint_summary"),
            "lint_baseline_summary": lint_result.get("lint_baseline_summary"),
            "lint_regressions": lint_result.get("lint_regressions", []),
            "lint_lowered_fields": lint_result.get("lint_lowered_fields", []),
            "lint_seconds": lint_result.get("lint_seconds"),
            "decision_ok": decision_result["decision_ok"],
            "decision_findings_count": len(decision_result.get("decision_findings", [])),
            "decision_new_findings": decision_result.get("decision_new_findings", []),
            "decision_larger_findings": decision_result.get("decision_larger_findings", []),
            "decision_files_scanned": decision_result.get("decision_files_scanned", []),
            "decision_seconds": decision_result.get("decision_seconds"),
            "counterexamples_ok": counterexamples_result["counterexamples_ok"],
            "counterexamples": counterexamples_result.get("counterexamples", []),
            "counterexamples_seconds": counterexamples_result.get("counterexamples_seconds"),
            "runtime_seconds": runtime,
        }))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
