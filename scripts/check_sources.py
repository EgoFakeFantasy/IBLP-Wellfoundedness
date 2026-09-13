"""Check exact audited Lean sources, imports, and forbidden proof shortcuts."""
import hashlib
import json
import pathlib
import re

root = pathlib.Path(__file__).resolve().parents[1]
record = json.loads((root / "verification/stage9-final-result.json").read_text(encoding="utf-8-sig"))
expected = {entry["path"].replace("\\", "/"): entry["sha256"].lower() for entry in record["sourceFiles"]}
actual = {p.relative_to(root).as_posix() for p in (root / "IBLP").rglob("*.lean")}
actual |= {"IBLP.lean", "CheckMilestones.lean", "Audit.lean"}
assert actual == set(expected), "Source inventory differs from the final audited proof"
for name in sorted(actual):
    data = (root / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected[name], f"Audited source changed: {name}"
    text = data.decode("utf-8-sig")
    assert not re.search(r"\b(sorry|admit|native_decide|sorryAx|unsafe)\b|^\s*(axiom|constant)\s", text, re.M), name

modules = {name[:-5].replace("/", "."): name for name in actual if name.startswith("IBLP")}
seen, pending = set(), ["IBLP"]
while pending:
    module = pending.pop()
    if module in seen:
        continue
    assert module in modules, f"Missing imported module: {module}"
    seen.add(module)
    source = (root / modules[module]).read_text(encoding="utf-8-sig")
    pending.extend(re.findall(r"^\s*import\s+(IBLP(?:\.[A-Za-z0-9_]+)*)", source, re.M))
assert seen == set(modules), f"Modules outside root audit: {set(modules) - seen}"
print(f"Verified {len(actual)} exact source hashes and {len(modules) - 1} project modules; no proof gaps.")
