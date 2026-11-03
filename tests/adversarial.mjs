// Adversarial regression tests for the publishing tools: each case is a copy of the
// repository with one hostile change, and `lemmata.mjs validate` must refuse it (or, for
// the positive controls, accept it). From a security review on 2026-10-22; run by
// tools/check.sh. Usage: node tests/adversarial.mjs
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TOOL = path.join(REPO, "tools", "lemmata.mjs");
const entry = "implication-composition";          // a real entry to plant changes in
const page = `docs/${entry}/index.md`;

// A fresh copy of the tracked files for each case.
function copy() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lemmata-adv-"));
  const files = execFileSync("git", ["-C", REPO, "ls-files", "-z"]).toString().split("\0").filter(Boolean);
  for (const f of files) { const d = path.join(dir, f); fs.mkdirSync(path.dirname(d), { recursive: true }); fs.copyFileSync(path.join(REPO, f), d); }
  return dir;
}
function validate(dir) {
  const r = spawnSync(process.execPath, [TOOL, "validate"], { env: { ...process.env, LEMMATA_ROOT: dir }, encoding: "utf8" });
  return { ok: r.status === 0, out: (r.stdout + r.stderr).trim() };
}
const append = (dir, f, text) => fs.appendFileSync(path.join(dir, f), text);

let failed = 0;
function expect(name, change, { refused = true, match } = {}) {
  const dir = copy();
  try {
    change(dir);
    const r = validate(dir);
    const good = refused ? !r.ok && (!match || match.test(r.out)) : r.ok;
    console.log(`${good ? "ok  " : "FAIL"} ${name}`);
    if (!good) { failed++; console.log("     " + r.out.split("\n").slice(0, 3).join("\n     ")); }
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}

// Finding 2: file-reading directives must stay inside the entry's own files.
expect("backtick literalinclude outside the repository",
  (d) => append(d, page, "\n```{literalinclude} ../../../../etc/hosts\n```\n"), { match: /escapes the repository|unsafe path/ });
expect("colon-fenced literalinclude outside the repository",
  (d) => append(d, page, "\n:::{literalinclude} ../../../etc/hosts\n:::\n"), { match: /escapes|unsafe/ });
expect("include with :literal: outside the repository",
  (d) => append(d, page, "\n```{include} ../../../etc/hosts\n:literal:\n```\n"), { match: /escapes|unsafe/ });
expect("absolute include path",
  (d) => append(d, page, "\n:::{include} /etc/hosts\n:::\n"), { match: /unsafe path/ });
expect("include of another entry's files",
  (d) => append(d, page, "\n```{include} ../lagrangian-duality-gap/index.md\n```\n"), { match: /outside this page's files/ });
expect("include of a repository file outside docs/ and the entry's Lean",
  (d) => append(d, page, "\n```{literalinclude} ../../tools/lemmata.mjs\n```\n"), { match: /outside this page's files/ });
expect("four-backtick fence",
  (d) => append(d, page, "\n````{literalinclude} ../../../etc/hosts\n````\n"), { match: /escapes|unsafe/ });
expect("csv-table reading a file outside",
  (d) => append(d, page, "\n```{csv-table}\n:file: ../../../etc/passwd\n```\n"), { match: /escapes|unsafe/ });
expect("figure from a file outside",
  (d) => append(d, page, "\n```{figure} ../../../etc/hosts\n```\n"), { match: /escapes|unsafe/ });
expect("raw html", (d) => append(d, page, "\n```{raw} html\n<script>alert(1)</script>\n```\n"), { match: /not allowed/ });
expect("positive control: the entry's own Lean file is allowed",
  (d) => append(d, page, "\n```{literalinclude} ../../lean/Lemmata/ImplicationComposition/Main.lean\n```\n"), { refused: false });
expect("positive control: a web figure is allowed",
  (d) => append(d, page, "\n```{figure} https://example.org/a.png\n```\n"), { refused: false });

// Finding 3: an entry id that names an Object.prototype property.
// A complete, consistent entry under that id: only the id itself may be the problem.
function renameEntry(d, to) {
  fs.renameSync(path.join(d, "docs", entry), path.join(d, "docs", to));
  for (const f of [`docs/${to}/contribution.yml`, `docs/${to}/index.md`]) {
    const p = path.join(d, f); fs.writeFileSync(p, fs.readFileSync(p, "utf8").replaceAll(entry, to));
  }
}
expect("positive control: a consistently renamed entry is accepted", (d) => renameEntry(d, "composition-of-implications"), { refused: false });
for (const id of ["constructor", "prototype", "hasownproperty", "valueof", "tostring"])
  expect(`entry id '${id}' is refused (it names an Object.prototype property)`, (d) => renameEntry(d, id), { match: /reserved/ });

// Finding 1: the Lean statement shown next to a result must be that declaration's, found
// by syntax, not text: not one inside a comment or string, not a same-named declaration
// in another namespace, and a definition must not be cut at a blank line.
const SRC = fs.readFileSync(TOOL, "utf8");
const leanStatement = new Function("fs", "path", "ROOT",
  SRC.slice(SRC.indexOf("const DECL_KW"), SRC.indexOf("function forgeLinks")) + "; return leanStatement;");
function statementCase(name, lean, fullName, check) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lemmata-adv-"));
  try {
    fs.writeFileSync(path.join(dir, "Main.lean"), lean);
    const st = leanStatement(fs, path, dir)("Main.lean", fullName);
    const good = check(st);
    console.log(`${good ? "ok  " : "FAIL"} ${name}`);
    if (!good) { failed++; console.log("     got: " + JSON.stringify(st?.text ?? st)); }
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}
statementCase("a decoy theorem in a block comment is not shown",
  "namespace Lemmata.X\n/-\ntheorem main : 1 = 2\n-/\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a nested block comment is not shown",
  "namespace Lemmata.X\n/- outer /- inner -/\ntheorem main : 1 = 2\n-/\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a line comment is not shown",
  "namespace Lemmata.X\n-- theorem main : 1 = 2\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a string is not shown",
  "namespace Lemmata.X\ndef s : String := \"\ntheorem main : 1 = 2\"\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a same-named theorem in another namespace is not shown",
  "namespace Lemmata.Other\ntheorem main : 1 = 2 := sorry\nend Lemmata.Other\nnamespace Lemmata.X\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a definition is not cut at a blank line",
  "namespace Lemmata.X\ndef f (n : Nat) : Nat :=\n  n + 1\n\n  -- still the body after a blank line\n  |> id\ntheorem t : True := trivial\nend Lemmata.X\n",
  "Lemmata.X.f", (st) => st && /\|> id/.test(st.text) && !/theorem t/.test(st.text));
statementCase("a missing declaration gives no statement (not some other one)",
  "namespace Lemmata.X\n-- theorem gone : 1 = 2\ntheorem other : True := trivial\nend Lemmata.X\n",
  "Lemmata.X.gone", (st) => st === null);

// Computations (2026-10-26): native_decide and friends only in an entry that declares
// native_computation: true; hand-written axioms and swapped-in compiled code nowhere.
const lean = `lean/Lemmata/ImplicationComposition/Main.lean`, mf = `docs/${entry}/contribution.yml`;
const addLean = (d, text) => append(d, lean.replace("Main.lean", "Extra.lean"), "module\n\npublic section\n\nnamespace Lemmata.ImplicationComposition\n" + text + "\nend Lemmata.ImplicationComposition\n");
const withUmbrella = (d) => fs.writeFileSync(path.join(d, "lean/Lemmata.lean"),
  fs.readFileSync(path.join(d, "lean/Lemmata.lean"), "utf8").replace("Lemmata.ImplicationComposition.Main", "Lemmata.ImplicationComposition.Extra\npublic import Lemmata.ImplicationComposition.Main"));
const flag = (d) => append(d, mf, "native_computation: true\n");
expect("native_decide without native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by native_decide"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("decide +native without native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by decide +native"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("bv_decide without native_computation: true",
  (d) => { addLean(d, "theorem t : True := by bv_decide"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("positive control: native_decide in an entry with native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by native_decide"); withUmbrella(d); flag(d); }, { refused: false });
expect("positive control: native_decide in a comment or string is no computation",
  (d) => { addLean(d, "-- by native_decide\n/- native_decide -/\ndef s : String := \"native_decide\""); withUmbrella(d); }, { refused: false });
expect("positive control: plain decide and decide +kernel need no flag",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by decide\ntheorem u : 2 + 2 = 4 := by decide +kernel"); withUmbrella(d); }, { refused: false });
expect("native_decide in lean/Lemmata/Shared",
  (d) => append(d, "lean/Lemmata/Shared/Basic.lean", "\ntheorem lemmata_shared_t : 2 + 2 = 4 := by native_decide\n"), { match: /lean\/Lemmata\/Shared must stay kernel-checked/ });
expect("a hand-written axiom, even in a flagged entry",
  (d) => { addLean(d, "axiom fake : (1 : Nat) = 2"); withUmbrella(d); flag(d); }, { match: /an axiom is not allowed/ });
expect("an axiom named like a computation",
  (d) => { addLean(d, "axiom t._native.native_decide.ax_1_1 : decide ((1 : Nat) = 2) = true"); withUmbrella(d); flag(d); }, { match: /an axiom is not allowed/ });
expect("@[implemented_by]",
  (d) => { addLean(d, "def f (n : Nat) : Nat := n\n@[implemented_by f] def g (n : Nat) : Nat := n + 1"); withUmbrella(d); flag(d); }, { match: /implemented_by.*not allowed/ });
expect("@[extern] after another attribute",
  (d) => { addLean(d, "@[inline, extern \"lean_nat_add\"] def h (n : Nat) : Nat := n"); withUmbrella(d); }, { match: /extern.*not allowed/ });
expect("native_computation must be true", (d) => append(d, mf, "native_computation: false\n"), { match: /must be true or left out/ });

// Computation rules after the simplification of 2026-10-27: only the flag is checked from
// the source (the verifier decides what is a computation, from the compiled files). A flagged
// entry may use metaprogramming and `meta import` of Mathlib -- native_decide on Mathlib's
// definitions needs it. Every Lean file is a module; none sits directly in lean/Lemmata/.
expect("decide with native options on the next lines needs the flag",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by\n  decide (config := {\n    native := true })"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("bv_check is a computation tactic too",
  (d) => { addLean(d, "theorem t : True := by bv_check \"x.lrat\""); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("positive control: a flagged entry may meta import Mathlib (native_decide on Mathlib definitions)",
  (d) => { append(d, lean.replace("Main.lean", "Extra.lean"), "module\n\npublic meta import Mathlib.Data.Nat.Prime.Defs\npublic section\nnamespace Lemmata.ImplicationComposition\ntheorem p : Nat.Prime 97 := by native_decide\nend Lemmata.ImplicationComposition\n"); withUmbrella(d); flag(d); },
  { refused: false });
expect("positive control: a flagged entry may define a macro",
  (d) => { addLean(d, "macro \"mytriv\" : tactic => `(tactic| trivial)\ntheorem t : True := by mytriv\ntheorem u : 2 + 2 = 4 := by native_decide"); withUmbrella(d); flag(d); }, { refused: false });
expect("a Lean file without the module header",
  (d) => { append(d, lean.replace("Main.lean", "Extra.lean"), "import Mathlib.Logic.Basic\nnamespace Lemmata.ImplicationComposition\nend Lemmata.ImplicationComposition\n"); withUmbrella(d); },
  { match: /first line must be `module`/ });
expect("a Lean file directly in lean/Lemmata/",
  (d) => { fs.writeFileSync(path.join(d, "lean/Lemmata/Helper.lean"), "module\npublic section\ntheorem helperT : True := trivial\n");
    fs.writeFileSync(path.join(d, "lean/Lemmata.lean"), fs.readFileSync(path.join(d, "lean/Lemmata.lean"), "utf8").replace("public import Lemmata.ImplicationComposition.Main", "public import Lemmata.Helper\npublic import Lemmata.ImplicationComposition.Main")); },
  { match: /lean\/Lemmata\/Helper\.lean: Lean files belong in/ });

// Citations (2026-10-28): papers are cited with @key from references.bib; links to papers
// and hand-written reference sections are refused in entries; unknown keys everywhere.
expect("an inline arXiv link in an entry", (d) => append(d, page, "\nSee [Rothvoss](https://arxiv.org/abs/1311.2369).\n"), { match: /cite papers with @key/ });
expect("a DOI link definition in an entry", (d) => append(d, page, "\nSee [the paper][x].\n\n[x]: https://doi.org/10.1287/moor.7.1.67\n"), { match: /cite papers with @key/ });
expect("a hand-written References section", (d) => append(d, page, "\n## References\n\n1. Someone (2020).\n"), { match: /no hand-written references section/ });
expect("an unknown citation key", (d) => append(d, page, "\nAs shown by @nobody2099nothing.\n"), { match: /citation @nobody2099nothing is not in docs\/references\.bib/ });
expect("positive control: known keys, narrative and parenthetical", (d) => append(d, page, "\nAs in @padberg1982odd and [@wyner1975common; @rothvoss2013matching].\n"), { refused: false });
expect("positive control: links to code and @ in code, math and an email are fine",
  (d) => append(d, page, "\nCode: [repo](https://github.com/x/y). Lean `@Foo.bar`, math $a@b$, mail x@example.org.\n\n```lean\n#check @Nat.add\n```\n"), { refused: false });

// Classification (2026-10-29): arXiv subjects and curated topics.
const setField = (d, re, line) => { const f = path.join(d, mf); fs.writeFileSync(f, fs.readFileSync(f, "utf8").replace(re, line)); };
expect("an unknown arXiv subject", (d) => setField(d, /^subject: .*$/m, "subject: math.XX"), { match: /is not an arXiv subject class/ });
expect("a cross-list repeating the subject", (d) => setField(d, /^subject: .*$/m, "subject: math.LO\ncross_lists: [math.LO]"), { match: /repeats the primary subject/ });
expect("an unknown topic", (d) => setField(d, /^topics: .*$/m, "topics: [no-such-topic]"), { match: /not in docs\/topics\.yml/ });
expect("the old category field", (d) => append(d, mf, "category: logic\n"), { match: /category\/tags were replaced/ });
expect("positive control: subject with cross-lists and topics", (d) => setField(d, /^subject: .*$/m, "subject: math.LO\ncross_lists: [cs.LO]"), { refused: false });

// Licenses: Apache-2.0 is an explicit opt-in; the default and existing CC choices stay
// unchanged. Exercise validation, both generated page labels, and the machine-readable
// index without compiling Lean or manufacturing a successful verification report.
function licenseCase(license, expected, name, url) {
  const dir = copy(), label = license ?? "default (omitted)";
  try {
    if (license) append(dir, mf, `license: ${license}\n`);
    const v = validate(dir);
    const ident = "2611.00013";
    fs.mkdirSync(path.join(dir, ".lemmata"), { recursive: true });
    fs.writeFileSync(path.join(dir, ".lemmata/identifiers.json"), JSON.stringify({ entries: { [entry]: ident } }));
    const report = path.join(dir, "report.json");
    fs.writeFileSync(report, "null\n");              // preview, not a verification result
    const env = { ...process.env, LEMMATA_ROOT: dir, LEMMATA_BUILD: "1" };
    const run = (...a) => spawnSync(process.execPath, [TOOL, ...a], { env, encoding: "utf8" });
    const p = run("prepare", "--preview");
    fs.mkdirSync(path.join(dir, "si"));
    const si = run("site-index", report, path.join(dir, "si"));
    const text = (f) => fs.existsSync(path.join(dir, f)) ? fs.readFileSync(path.join(dir, f), "utf8") : "";
    const panel = text(`docs/_generated/verification/${entry}.md`);
    const landing = text(`docs/abs/${ident.replace(".", "-")}/index.md`);
    const index = JSON.parse(text("si/lemmata.json") || "null");
    const item = index?.entries.find((e) => e.exports.some((x) => x.name.startsWith("Lemmata.ImplicationComposition.")));
    const line = `License: [${name}](${url})`;
    const checks = [
      ["validation accepts it", v.ok],
      ["prepare and site-index succeed", p.status === 0 && si.status === 0],
      ["entry has the correct license label and URL", panel.includes(line)],
      ["abstract page has the correct license label and URL", landing.includes(line)],
      ["lemmata.json has the correct SPDX id and URL", item?.license === expected && item.license_url === url],
      ["llms.txt lists Apache 2.0 as an alternative", text("si/llms.txt").includes("CC BY-SA 4.0, CC0 1.0 or Apache 2.0")],
    ];
    for (const [what, ok] of checks) { console.log(`${ok ? "ok  " : "FAIL"} license ${label}: ${what}`); if (!ok) failed++; }
    if (!v.ok || p.status !== 0 || si.status !== 0)
      console.log("     " + (v.out + "\n" + p.stderr + si.stderr).trim().split("\n").slice(0, 3).join("\n     "));
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}
for (const [license, name, url] of [
  ["CC-BY-4.0", "CC BY 4.0", "https://creativecommons.org/licenses/by/4.0/"],
  ["CC-BY-SA-4.0", "CC BY-SA 4.0", "https://creativecommons.org/licenses/by-sa/4.0/"],
  ["CC0-1.0", "CC0 1.0", "https://creativecommons.org/publicdomain/zero/1.0/"],
  ["Apache-2.0", "Apache 2.0", "https://www.apache.org/licenses/LICENSE-2.0"],
]) licenseCase(license, license, name, url);
licenseCase(undefined, "CC-BY-4.0", "CC BY 4.0", "https://creativecommons.org/licenses/by/4.0/");
for (const license of ["MIT", "constructor"])
  expect(`unsupported license '${license}' is refused`, (d) => append(d, mf, `license: ${license}\n`), { match: /license must be one of/ });

// Frozen entries keep what their last check recorded, computations included (review,
// 2026-10-26: a frozen computation-backed result was shown as plainly kernel-checked, its
// claims dropped and llms.txt without the caveat). A frozen record of the shape
// controller/worker.mjs writes, and a report in which the entry is absent (it was not built):
// the panel, the overview and lemmata.json / llms.txt must still say "computation".
function frozenCase() {
  const dir = copy();
  try {
    const ns = "Lemmata.ImplicationComposition", mod = `${ns}.Main`;
    const claim = { name: `${mod}.x._native.native_decide.ax_1_1`, declaration: `${ns}.implication_composition`, tactic: "native_decide",
      contribution: entry, module: mod, source_file: "lean/Lemmata/ImplicationComposition/Main.lean", line: 12, claim: "decide (2 + 2 = 4)" };
    const m = YAML_load(path.join(dir, mf));
    const results = m.exports.map((e, i) => ({ name: e.name, kind: e.kind, status: "checked",
      computation: i === 0 ? "own" : "kernel", computations: i === 0 ? [claim] : [] }));
    fs.mkdirSync(path.join(dir, ".lemmata"), { recursive: true });
    fs.writeFileSync(path.join(dir, ".lemmata/frozen.json"), JSON.stringify({ entries: { [entry]: {
      commit: "a".repeat(40), lean_version: "4.35.0", checked_at: "2026-10-26T12:00:00Z", results } } }));
    const report = { result: "passed", lean_version: "4.35.0", exports: [], computations: [] };
    fs.writeFileSync(path.join(dir, "report.json"), JSON.stringify(report));
    const env = { ...process.env, LEMMATA_ROOT: dir, LEMMATA_BUILD: "1" };
    const run = (...a) => spawnSync(process.execPath, [TOOL, ...a], { env, encoding: "utf8" });
    const p = run("prepare", path.join(dir, "report.json"), "--commit", "b".repeat(12));
    fs.mkdirSync(path.join(dir, "si"));
    const si = run("site-index", path.join(dir, "report.json"), path.join(dir, "si"), "--commit", "b".repeat(12));
    const panel = fs.readFileSync(path.join(dir, `docs/_generated/verification/${entry}.md`), "utf8");
    const cat = fs.readFileSync(path.join(dir, "docs/_generated/catalog.md"), "utf8");
    const json = JSON.parse(fs.readFileSync(path.join(dir, "si/lemmata.json"), "utf8")).entries.find((e) => e.exports.some((x) => x.name.startsWith(ns)));
    const llms = fs.readFileSync(path.join(dir, "si/llms.txt"), "utf8");
    const checks = [
      ["tools ran", p.status === 0 && si.status === 0],
      ["panel: the computation-backed result is not called kernel-checked", /⚙ checked by computation\*\* \[\]\(#/.test(panel)],
      ["panel: the claim is listed", /Computations assumed/.test(panel) && /line 12/.test(panel)],
      ["overview says mod. computation", new RegExp(`checked with v4\\.35\\.0, mod\\. computation`).test(cat)],
      ["lemmata.json keeps the claim", json?.exports[0]?.verification === "checked-by-computation" && json.exports[0].computations.length === 1],
      ["llms.txt keeps the caveat", /last checked with Lean v4\.35\.0 on 2026-10-26, modulo computation/.test(llms)],
    ];
    for (const [name, ok] of checks) { console.log(`${ok ? "ok  " : "FAIL"} frozen entry: ${name}`); if (!ok) failed++; }
    if (p.status !== 0 || si.status !== 0) console.log("     " + (p.stderr + si.stderr).trim().split("\n").slice(0, 3).join("\n     "));
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}
const YAML_load = (f) => { const src = fs.readFileSync(f, "utf8"); return { exports: [...src.matchAll(/^\s*- name: (\S+)\n\s*kind: (\w+)/gm)].map((x) => ({ name: x[1], kind: x[2] })) }; };
frozenCase();

console.log(failed ? `\n${failed} adversarial case(s) FAILED` : "\nall adversarial cases passed");
process.exit(failed ? 1 : 0);
