#!/usr/bin/env node
// Repository tooling for Lemmata. One file, no dependencies besides `yaml`, so the
// cluster's build Job can run the same code a contributor runs locally.
//
//   node tools/lemmata.mjs validate            structure, manifests, pairing, snippets, umbrella
//   node tools/lemmata.mjs umbrella [--write]  check (or regenerate) lean/Lemmata.lean
//   node tools/lemmata.mjs request <out.json>  verifier request built from the manifests
//   node tools/lemmata.mjs prepare <report.json> [--commit SHA] [--source-url URL]
//                                              generated pages + docs/myst.runtime.yml
//   node tools/lemmata.mjs new <id> <LeanName> <subject>    scaffold a new contribution (subject: an arXiv class)
//
// Exit status is non-zero on any problem; every problem is printed, not just the first.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { execFileSync } from "node:child_process";
import YAML from "yaml";

// LEMMATA_ROOT lets the cluster run its own (trusted) copy of this file against a
// checkout somewhere else; locally the repository is the file's parent directory.
const ROOT = path.resolve(process.env.LEMMATA_ROOT ?? path.join(path.dirname(fileURLToPath(import.meta.url)), ".."));
const DOCS = path.join(ROOT, "docs");
const LEAN = path.join(ROOT, "lean");
const LIB = "Lemmata";
const ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"];
// v2 (2026-10-26): computations (native_decide) accepted for entries that declare
// native_computation: true, and shown apart from kernel-checked results.
const POLICY_ID = "lemmata-verification-v2";

// Directories in docs/ and lean/Lemmata/ that are infrastructure, not contributions.
// Names of Object.prototype properties, lower-cased: valid kebab-case ids that would collide
// with built-ins in any id-keyed JavaScript object.
const RESERVED_JS = Object.fromEntries([...Object.getOwnPropertyNames(Object.prototype),
  ...Object.getOwnPropertyNames(Function.prototype), "prototype"].map((k) => [k.toLowerCase(), true]));
const RESERVED_DOCS = new Set(["_static", "_generated", "_build", "_releases", "_status",
  "index", "healthz", "readyz", "node_modules", "c", "s", "t", "a", "changelog", "abs", "html", "llms", "checked", "about"]);
// The page that explains what "checked" means (docs/checked.md), linked from every
// verification panel; entries are at docs/<id>/, so the link is one level up.
const CHECKED_PAGE_LINK = "../checked.md";
// Classification (2026-10-29): every entry has one primary arXiv subject (`subject`), any
// number of further ones (`cross_lists`), and optional free `topics` from docs/topics.yml.
// Subject pages are generated at docs/s/<subject>/ and topic pages at docs/t/<topic>/,
// under reserved prefixes so they never collide with entry ids. MyST turns dots in page
// paths into hyphens, so math.OC lives at /s/math-oc/; titles keep the arXiv spelling.
// /c/<id>/ were the pages of the categories this replaced; they remain as redirects.
const SUBJECT_DIR = "s", TOPIC_DIR = "t", OLD_CATEGORY_DIR = "c";
const subjectSlug = (id) => id.toLowerCase().replace(/\./g, "-");
// Author pages at /a/<slug>/: every entry a person is credited on, like arXiv's author
// search. Keyed by the displayed name (git author name, or the manifest's contributors);
// names only, never emails. Not an identity: two people with one name share a page.
const AUTHOR_DIR = "a";
// The collapsible "Cite as" box with the BibTeX under the header. Replaced by a copy button
// next to the identifier (2026-10-21); kept so it can be switched back on.
const SHOW_CITE_BOX = false;
// Comments under each entry with Giscus (GitHub Discussions). Off until a PUBLIC repository
// with Discussions and the Giscus app exists: fill in its ids (from giscus.app) to enable.
// Ids from GitHub (gh api graphql, or giscus.app). "Comments" is an Announcement-format
// category, so only maintainers and giscus start threads; readers comment in them.
const GISCUS = { repo: "ZIB-IOL/lemmata", repoId: "R_kgDOVQjOqA", category: "Comments", categoryId: "DIC_kwDOVQjOqM4DJSBM" };
const TOPIC_KEYS = new Set(["id", "title", "description", "replaces"]);
const RESERVED_LEAN = new Set(["Shared"]);
const MANIFEST_KEYS = new Set(["schema_version", "id", "lean_namespace", "subject", "cross_lists", "topics", "arxiv", "contributors",
  "ai_use", "acknowledgements", "abstract", "license", "withdrawn", "related", "native_computation", "pages", "exports"]);
// Computations: `native_computation: true` lets an entry prove facts by having the compiler
// run them (native_decide, decide +native, bv_decide). The build runs them; nobody re-runs
// them and Lean's kernel never checks them, so results that rely on one are labelled apart
// from kernel-checked ones, and every claim is listed on the page. Which axioms count as
// computations is decided by the verifier (checker/Main.lean) from the compiled files; the
// source scan here only gives an early, readable error when an entry without the flag uses
// one of these tactics. FORBIDDEN_LEAN are ways to assert or swap in unchecked facts or code,
// refused in every Lean file.
const COMPUTATION_TACTICS = ["native_decide", "bv_decide", "bv_decide?", "bv_check"];
const FORBIDDEN_LEAN = { axiom: "an axiom", implemented_by: "`@[implemented_by]`", extern: "`@[extern]`" };
// Optional derived material attached to an entry: slides, videos, a monograph, code, ...
// Each is {kind, title, url}; shown as a list at the end of the entry.
const RELATED_KINDS = new Set(["slides", "video", "paper", "book", "notes", "code", "talk", "other"]);
// Licence of an entry (prose and Lean). Optional; without it the entry is CC BY 4.0. Only
// these SPDX ids are accepted, so every entry stays reusable and its link is known.
const LICENSES = {
  "CC-BY-4.0": { name: "CC BY 4.0", url: "https://creativecommons.org/licenses/by/4.0/" },
  "CC-BY-SA-4.0": { name: "CC BY-SA 4.0", url: "https://creativecommons.org/licenses/by-sa/4.0/" },
  "CC0-1.0": { name: "CC0 1.0", url: "https://creativecommons.org/publicdomain/zero/1.0/" },
  "Apache-2.0": { name: "Apache 2.0", url: "https://www.apache.org/licenses/LICENSE-2.0" },
};
const DEFAULT_LICENSE = "CC-BY-4.0";
// Free-text notes rendered at the bottom of an entry. Inline MyST only: text, emphasis,
// links and math ($...$, $$...$$, rendered by KaTeX). Anything that could create page
// structure or pull in other content is refused, so a note cannot impersonate the
// verification panel or include files.
const NOTE_KEYS = { ai_use: "AI use", acknowledgements: "Acknowledgements" };
const NOTE_MAX_CHARS = 2000;
function checkNote(text, at) {
  if (typeof text !== "string" || !text.trim()) { fail(`${at}: must be non-empty text`); return null; }
  if (text.length > NOTE_MAX_CHARS) { fail(`${at}: longer than ${NOTE_MAX_CHARS} characters`); return null; }
  const bad = [[/^\s*(```|~~~|:::)/m, "code fences or directives"], [/\{[a-z][\w:-]*\}`/i, "roles such as {eval}`...`"],
    [/^\s*#/m, "headings"], [/^\s*\(.*\)=\s*$/m, "labels"], [/<\s*\/?\s*[a-z]/i, "HTML"], [/^\s*[-*+]\s|^\s*\d+\.\s/m, "lists"]];
  for (const [re, what] of bad) if (re.test(text)) { fail(`${at}: ${what} are not allowed (inline text, links and $math$ only)`); return null; }
  // Balanced $ / $$ so a stray dollar does not swallow the rest of the page into math.
  const dollars = (text.replace(/\\\$/g, "").match(/\$/g) ?? []).length;
  if (dollars % 2) { fail(`${at}: unbalanced $ (escape a literal dollar as \\$)`); return null; }
  return text.trim();
}
// arXiv identifiers: new style 2301.01234 (4 or 5 digits after the dot, since 2015), old
// style math/0601001 or math.AG/0601001; each optionally with a version vN.
const ARXIV_RE = /^(?:\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Z]{2})?\/\d{7})(?:v\d+)?$/;
const EXPORT_KEYS = new Set(["name", "kind", "page", "label"]);
const KINDS = new Set(["theorem", "definition"]);
const ID_RE = /^[a-z][a-z0-9]*(-[a-z0-9]+)*$/;
const LEAN_COMPONENT_RE = /^[A-Z][A-Za-z0-9]*$/;
const LABEL_RE = /^[a-z][a-z0-9-]*$/;

const problems = [];
const fail = (msg) => problems.push(msg);

function finish(okMessage) {
  if (problems.length) {
    for (const p of problems) console.error(`FAIL ${p}`);
    console.error(`${problems.length} problem(s)`);
    process.exit(1);
  }
  if (okMessage) console.log(okMessage);
}

// Refuse anything that is not a plain file/directory inside the repo: no symlinks, no
// traversal. Used for every path a manifest or page can name.
function safeRel(base, rel, what) {
  if (typeof rel !== "string" || !rel || path.isAbsolute(rel) || rel.includes("\\")) {
    fail(`${what}: unsafe path ${JSON.stringify(rel)}`); return null;
  }
  const abs = path.resolve(base, rel);
  if (!abs.startsWith(ROOT + path.sep)) { fail(`${what}: ${rel} escapes the repository`); return null; }
  let p = abs;
  while (p !== ROOT) {
    try { if (fs.lstatSync(p).isSymbolicLink()) { fail(`${what}: ${rel} goes through a symlink`); return null; } }
    catch { break; }
    p = path.dirname(p);
  }
  return abs;
}

function listDirs(dir) {
  return fs.readdirSync(dir, { withFileTypes: true })
    .filter((d) => d.isDirectory() && !d.name.startsWith(".")).map((d) => d.name).sort();
}

function walk(dir, ext, out = []) {
  for (const d of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, d.name);
    if (d.isSymbolicLink()) fail(`symlink not allowed: ${path.relative(ROOT, p)}`);
    else if (d.isDirectory()) walk(p, ext, out);
    else if (d.name.endsWith(ext)) out.push(p);
  }
  return out;
}

function arxivIds(source) {
  const node = YAML.parseDocument(source).get("arxiv", true);
  if (node === undefined || node === null) return [];
  const items = YAML.isSeq(node) ? node.items : [node];
  return items.map((x) => (YAML.isScalar(x) ? (x.source ?? String(x.value)) : x)).map((v) => typeof v === "string" ? v.trim() : v);
}

// --------------------------------------------------------------------------- classification

// docs/subjects.json is arXiv's list of subject classes, kept as fetched (nothing to curate);
// docs/topics.yml is the short, curated list of topics. An unknown subject or topic is an
// error, so a typo cannot quietly create a new page. A topic may name the old category ids
// it `replaces`: their /c/<id>/ pages then redirect to it.
function loadTaxonomy() {
  const sf = path.join(DOCS, "subjects.json");
  let subjects = {};
  if (!fs.existsSync(sf)) fail("docs/subjects.json is missing");
  else try { subjects = JSON.parse(fs.readFileSync(sf, "utf8")).subjects ?? {}; } catch (e) { fail(`docs/subjects.json: ${e.message}`); }
  const tf = path.join(DOCS, "topics.yml");
  const topics = [];
  if (fs.existsSync(tf)) {
    let list;
    try { list = YAML.parse(fs.readFileSync(tf, "utf8"), { uniqueKeys: true }) ?? []; } catch (e) { fail(`docs/topics.yml: ${e.message}`); list = []; }
    if (!Array.isArray(list)) { fail("docs/topics.yml must be a list"); list = []; }
    const seen = new Set();
    for (const [i, t] of list.entries()) {
      const at = `docs/topics.yml[${i}]`;
      if (!t || typeof t !== "object") { fail(`${at}: not a mapping`); continue; }
      for (const k of Object.keys(t)) if (!TOPIC_KEYS.has(k)) fail(`${at}: unknown field ${k}`);
      if (typeof t.id !== "string" || !ID_RE.test(t.id)) { fail(`${at}: id must be lowercase kebab-case`); continue; }
      if (seen.has(t.id)) fail(`${at}: duplicate id ${t.id}`);
      if (typeof t.title !== "string" || !t.title.trim()) fail(`${at}: title is required`);
      if (t.description !== undefined && typeof t.description !== "string") fail(`${at}: description must be text`);
      if (t.replaces !== undefined && (!Array.isArray(t.replaces) || t.replaces.some((x) => typeof x !== "string" || !ID_RE.test(x)))) fail(`${at}: replaces must be a list of old category ids`);
      seen.add(t.id);
      topics.push({ id: t.id, title: String(t.title ?? t.id), description: t.description ?? "", replaces: t.replaces ?? [] });
    }
  }
  return { subjects, topics };
}
const subjectTitle = (tax, id) => `${id} — ${tax.subjects[id] ?? id}`;

// ---------------------------------------------------------------------------- manifests

function loadManifests(tax = loadTaxonomy()) {
  const topicIds = new Set(tax.topics.map((t) => t.id));
  const manifests = [];
  const seen = { ids: new Map(), ns: new Map(), labels: new Map(), lower: new Map() };
  for (const dir of listDirs(DOCS)) {
    if (RESERVED_DOCS.has(dir)) continue;
    const where = `docs/${dir}`;
    if (!ID_RE.test(dir)) { fail(`${where}: directory name is not a lowercase kebab-case id`); continue; }
    if (dir in Object.prototype || dir.toLowerCase() in RESERVED_JS) { fail(`${where}: "${dir}" is a reserved id (it names a built-in property); choose another`); continue; }
    const mfPath = path.join(DOCS, dir, "contribution.yml");
    if (!fs.existsSync(mfPath)) { fail(`${where}: missing contribution.yml`); continue; }
    let m;
    try { m = YAML.parse(fs.readFileSync(mfPath, "utf8"), { uniqueKeys: true }); }
    catch (e) { fail(`${where}/contribution.yml: ${e.message}`); continue; }
    if (!m || typeof m !== "object") { fail(`${where}/contribution.yml: not a mapping`); continue; }
    for (const k of Object.keys(m)) if (!MANIFEST_KEYS.has(k)) fail(`${where}/contribution.yml: unknown field ${k}`);
    if (m.schema_version !== 1) fail(`${where}/contribution.yml: schema_version must be 1`);
    if (m.id !== dir) fail(`${where}/contribution.yml: id ${JSON.stringify(m.id)} does not match directory`);
    if (m.category !== undefined || m.tags !== undefined)
      fail(`${where}/contribution.yml: category/tags were replaced by subject (an arXiv class, e.g. math.OC), cross_lists and topics; see AGENTS.md`);
    if (!Object.hasOwn(tax.subjects, m.subject ?? ""))
      fail(`${where}/contribution.yml: subject ${JSON.stringify(m.subject)} is not an arXiv subject class (docs/subjects.json), e.g. math.OC, cs.CC`);
    if (m.cross_lists !== undefined && !Array.isArray(m.cross_lists)) fail(`${where}/contribution.yml: cross_lists must be a list`);
    for (const c of Array.isArray(m.cross_lists) ? m.cross_lists : []) {
      if (!Object.hasOwn(tax.subjects, c)) fail(`${where}/contribution.yml: cross_list ${JSON.stringify(c)} is not an arXiv subject class`);
      if (c === m.subject) fail(`${where}/contribution.yml: cross_list ${c} repeats the primary subject`);
    }
    if (m.topics !== undefined && !Array.isArray(m.topics)) fail(`${where}/contribution.yml: topics must be a list`);
    for (const t of Array.isArray(m.topics) ? m.topics : [])
      if (!topicIds.has(t)) fail(`${where}/contribution.yml: topic ${JSON.stringify(t)} is not in docs/topics.yml (add it there, with a title and a one-line description)`);

    const ns = String(m.lean_namespace ?? "");
    const comps = ns.split(".");
    if (comps.length !== 2 || comps[0] !== LIB || !LEAN_COMPONENT_RE.test(comps[1]) || RESERVED_LEAN.has(comps[1]))
      fail(`${where}/contribution.yml: lean_namespace must be ${LIB}.<UpperCamel>, got ${JSON.stringify(ns)}`);
    const leanDir = comps[1] ? path.join(LEAN, LIB, comps[1]) : null;
    if (leanDir && !fs.existsSync(path.join(leanDir, "Main.lean")))
      fail(`${where}: lean/${LIB}/${comps[1]}/Main.lean does not exist`);

    for (const [key, map, val] of [["id", seen.ids, m.id], ["lean_namespace", seen.ns, ns]]) {
      if (map.has(val)) fail(`${where}: ${key} ${val} already used by ${map.get(val)}`);
      map.set(val, where);
    }
    const lower = (comps[1] ?? "").toLowerCase();
    if (seen.lower.has(lower)) fail(`${where}: Lean directory ${comps[1]} collides case-insensitively with ${seen.lower.get(lower)}`);
    seen.lower.set(lower, where);

    const pages = Array.isArray(m.pages) ? m.pages : [];
    if (pages[0] !== "index.md") fail(`${where}/contribution.yml: pages must start with index.md`);
    const pageSet = new Set();
    for (const p of pages) {
      if (typeof p !== "string" || !p.endsWith(".md")) { fail(`${where}: page ${JSON.stringify(p)} is not a .md path`); continue; }
      const abs = safeRel(path.join(DOCS, dir), p, where);
      if (abs && !fs.existsSync(abs)) fail(`${where}: page ${p} does not exist`);
      if (pageSet.has(p)) fail(`${where}: page ${p} listed twice`);
      pageSet.add(p);
    }
    // The two generated panels are not optional: an entry must show who contributed it
    // (from git) and what was checked (from the verifier), and only the tools write them.
    if (pageSet.has("index.md")) {
      const idx = fs.readFileSync(path.join(DOCS, dir, "index.md"), "utf8");
      for (const [kind, what] of [["provenance", "contributors line"], ["verification", "verification panel"]]) {
        const inc = `{include} ../_generated/${kind}/${dir}.md`;
        if (idx.split(inc).length - 1 !== 1) fail(`${where}/index.md: must include the ${what} exactly once: \`\`\`${inc}\``);
      }
    }
    for (const f of walk(path.join(DOCS, dir), ".md")) {
      const rel = path.relative(path.join(DOCS, dir), f);
      if (!pageSet.has(rel)) fail(`${where}: page ${rel} is not listed in contribution.yml`);
      else checkProofs(fs.readFileSync(f, "utf8"), `${where}/${rel}`);
    }

    const exports = Array.isArray(m.exports) ? m.exports : [];
    if (!exports.some((e) => e?.kind === "theorem")) fail(`${where}: needs at least one exported theorem`);
    for (const [i, e] of exports.entries()) {
      const at = `${where} exports[${i}]`;
      if (!e || typeof e !== "object") { fail(`${at}: not a mapping`); continue; }
      for (const k of Object.keys(e)) if (!EXPORT_KEYS.has(k)) fail(`${at}: unknown field ${k}`);
      if (!KINDS.has(e.kind)) fail(`${at}: kind must be theorem or definition`);
      if (typeof e.name !== "string" || !e.name.startsWith(ns + ".")) fail(`${at}: ${e.name} is not inside ${ns}`);
      if (!pageSet.has(e.page)) fail(`${at}: page ${e.page} is not one of this contribution's pages`);
      if (typeof e.label !== "string" || !LABEL_RE.test(e.label)) { fail(`${at}: bad label ${JSON.stringify(e.label)}`); continue; }
      if (!e.label.includes(m.id)) fail(`${at}: label ${e.label} should contain the contribution id ${m.id}`);
      if (seen.labels.has(e.label)) fail(`${at}: label ${e.label} also bound in ${seen.labels.get(e.label)}`);
      seen.labels.set(e.label, at);
      if (pageSet.has(e.page)) {
        const text = fs.readFileSync(path.join(DOCS, dir, e.page), "utf8");
        const n = [...text.matchAll(new RegExp(`^\\s*:label:\\s*${e.label}\\s*$|^\\(${e.label}\\)=\\s*$`, "gm"))].length;
        if (n !== 1) fail(`${at}: label ${e.label} appears ${n} times in ${e.page}, expected exactly once`);
      }
    }
    // Optional arXiv id(s) for additional material; shown linked under the title. Read
    // from the YAML source text, not the parsed value: unquoted, 2301.10230 parses as the
    // number 2301.1023 -- a link to a different paper.
    const arxiv = arxivIds(fs.readFileSync(mfPath, "utf8"));
    for (const a of arxiv) {
      if (typeof a !== "string" || !ARXIV_RE.test(a))
        fail(`${where}/contribution.yml: arxiv ${JSON.stringify(a)} is not an arXiv identifier (e.g. 2301.01234, 2301.01234v2, math/0601001)`);
    }
    if (new Set(arxiv).size !== arxiv.length) fail(`${where}/contribution.yml: arxiv lists an identifier twice`);
    // Optional explicit contributors: replaces the git-derived names (git knows who
    // committed, not who wrote it). Each item is "First Last" or {first, last} -- the
    // mapping form is for surnames with several parts ("van Beethoven", "García Márquez").
    const contributors = [];
    if (m.contributors !== undefined) {
      if (!Array.isArray(m.contributors) || !m.contributors.length) fail(`${where}/contribution.yml: contributors must be a non-empty list`);
      for (const [i, c] of (Array.isArray(m.contributors) ? m.contributors : []).entries()) {
        const at = `${where}/contribution.yml: contributors[${i}]`;
        if (typeof c === "string") {
          const t = c.trim().replace(/\s+/g, " ");
          if (!t || /[{}\\@<>]/.test(t)) { fail(`${at}: ${JSON.stringify(c)} is not a plain name`); continue; }
          contributors.push({ name: t });
        } else if (c && typeof c === "object" && !Array.isArray(c)) {
          // {first, last} or {name}, each with an optional ORCID iD.
          for (const k of Object.keys(c)) if (!["first", "last", "name", "orcid"].includes(k)) fail(`${at}: unknown field ${k} (use first/last or name, and orcid)`);
          let orcid = null;
          if (c.orcid !== undefined) {
            orcid = String(c.orcid).trim().replace(/^https?:\/\/orcid\.org\//, "");
            if (!orcidValid(orcid)) { fail(`${at}: orcid ${JSON.stringify(c.orcid)} is not a valid ORCID iD (0000-0000-0000-000X, checksum)`); orcid = null; }
          }
          if (c.name !== undefined) {
            if (c.first !== undefined || c.last !== undefined) { fail(`${at}: give either name or first/last`); continue; }
            const t = String(c.name).trim().replace(/\s+/g, " ");
            if (!t || /[{}\\@<>]/.test(t)) { fail(`${at}: ${JSON.stringify(c.name)} is not a plain name`); continue; }
            contributors.push({ name: t, orcid });
            continue;
          }
          const first = String(c.first ?? "").trim(), last = String(c.last ?? "").trim();
          if (!last) { fail(`${at}: last is required`); continue; }
          if (/[{}\\@<>]/.test(first + last)) { fail(`${at}: names must be plain text`); continue; }
          contributors.push({ name: first ? `${first} ${last}` : last, first, last, orcid });
        } else fail(`${at}: must be a name, {name, orcid} or {first, last, orcid}`);
      }
      const seen = new Set();
      for (const c of contributors) { if (seen.has(c.name)) fail(`${where}/contribution.yml: contributor ${c.name} listed twice`); seen.add(c.name); }
      const ids = contributors.filter((c) => c.orcid).map((c) => c.orcid);
      if (new Set(ids).size !== ids.length) fail(`${where}/contribution.yml: an ORCID iD is listed twice`);
    }
    const notes = {};
    for (const k of Object.keys(NOTE_KEYS)) if (m[k] !== undefined) notes[k] = checkNote(m[k], `${where}/contribution.yml: ${k}`);
    // Optional abstract for the entry's /abs/ page; inline only, like the notes.
    if (m.abstract === undefined) fail(`${where}/contribution.yml: abstract is required (one paragraph, inline text and $math$)`);
    else notes.abstract = checkNote(m.abstract, `${where}/contribution.yml: abstract`);
    // Withdrawn: the reason, shown as a notice on the entry and its /abs/ page. A withdrawn
    // entry is never deleted (identifiers are cited, other entries may import its Lean):
    // it is still built and checked, only left out of the sidebar and the listings.
    if (m.withdrawn !== undefined) notes.withdrawn = checkNote(m.withdrawn, `${where}/contribution.yml: withdrawn`);
    if (m.native_computation !== undefined && m.native_computation !== true)
      fail(`${where}/contribution.yml: native_computation must be true or left out`);
    if (m.license !== undefined && !Object.hasOwn(LICENSES, m.license))
      fail(`${where}/contribution.yml: license must be one of ${Object.keys(LICENSES).join(", ")} (default ${DEFAULT_LICENSE})`);
    const license = Object.hasOwn(LICENSES, m.license) ? m.license : DEFAULT_LICENSE;
    const related = [];
    if (m.related !== undefined) {
      if (!Array.isArray(m.related)) fail(`${where}/contribution.yml: related must be a list of {kind, title, url}`);
      for (const [i, r] of (Array.isArray(m.related) ? m.related : []).entries()) {
        const at = `${where}/contribution.yml: related[${i}]`;
        if (!r || typeof r !== "object") { fail(`${at}: must be {kind, title, url}`); continue; }
        for (const k of Object.keys(r)) if (!["kind", "title", "url"].includes(k)) fail(`${at}: unknown field ${k}`);
        if (!RELATED_KINDS.has(r.kind)) fail(`${at}: kind must be one of ${[...RELATED_KINDS].join(", ")}`);
        let u = null; try { u = new URL(r.url); } catch {}
        if (!u || !["https:", "http:"].includes(u.protocol) || /["'<>\s]/.test(r.url)) fail(`${at}: url must be a plain http(s) URL`);
        const title = typeof r.title === "string" ? checkNote(r.title, `${at}: title`) : (fail(`${at}: title is required`), null);
        if (title && u) related.push({ kind: r.kind, title, url: r.url });
      }
    }
    manifests.push({ ...m, dir, leanDir: comps[1], exports, pages, crossLists: Array.isArray(m.cross_lists) ? m.cross_lists : [],
      topics: Array.isArray(m.topics) ? m.topics : [], arxiv, contributors, notes, license, related,
      native: m.native_computation === true });
  }
  // Every Lean contribution directory needs a manifest.
  if (fs.existsSync(path.join(LEAN, LIB))) {
    const claimed = new Set(manifests.map((m) => m.leanDir));
    for (const d of listDirs(path.join(LEAN, LIB)))
      if (!RESERVED_LEAN.has(d) && !claimed.has(d)) fail(`lean/${LIB}/${d}: no docs/<id>/contribution.yml claims it`);
  }
  return manifests;
}

// ------------------------------------------------------------------- snippets, umbrella

// Every literalinclude must point inside the repo at an existing file, and its
// start-after/end-before markers must each occur exactly once, in that order.
// MyST numbers proofs like theorems, so an entry with a theorem, a proposition and one
// proof shows "Proof 1" and leaves the reader guessing what it proves. Every proof is
// therefore unnumbered and names its statement with a link:
//   ```{prf:proof} of [](#thm-<id>)
//   :nonumber:
// which renders as "Proof (of Theorem 1)". No project-wide switch does this: MyST's
// numbering config ignores proofs.
function checkProofs(text, where) {
  const lines = text.split("\n");
  for (const [i, line] of lines.entries()) {
    const m = line.match(/^\s*(`{3,}|:{3,})\{prf:proof\}(.*)$/);
    if (!m) continue;
    const at = `${where}:${i + 1}`;
    if (!/\]\(#[^)\s]+\)/.test(m[2])) fail(`${at}: a proof must say what it proves, e.g. \`${m[1]}{prf:proof} of [](#thm-…)\``);
    let nonumber = false;
    for (let j = i + 1; j < lines.length && /^\s*:[\w-]+:/.test(lines[j]); j++)
      if (/^\s*:nonumber:/.test(lines[j])) nonumber = true;
    if (!nonumber) fail(`${at}: a proof must be unnumbered: add \`:nonumber:\` on the line after the directive`);
  }
}

// DOI links. MyST treats every doi.org link (and doi:…) as a citation and looks it up
// online while rendering, unless docs/references.bib already has an entry with that DOI.
// The cluster renders offline -- the render step shares its pod, and so its network
// policy, with the untrusted Lean build -- so an unresolved DOI fails only there
// ("Could not find DOI"), long after a local check passed. Hence: every DOI linked from
// docs/ must be in references.bib, and `lemmata.mjs doi` fetches the missing entries on
// the contributor's (online) machine.
const BIB = path.join(DOCS, "references.bib");
const DOI_LINK_RE = /(?:https?:\/\/(?:dx\.|www\.)?doi\.org\/|\bdoi:)(10\.\d{4,9}\/[^\s)>\]"'`]+)/gi;
const doiNorm = (d) => decodeURIComponent(d).replace(/[.,;:]+$/, "").toLowerCase();
// The hand-written pages: the start page, checked/changelog, and every entry's pages.
function linkedDois(manifests) {
  const out = new Map();     // normalised DOI -> first place it is linked
  const pages = ["index.md", "checked.md", "changelog.md", "about.md"].map((p) => path.join(DOCS, p))
    .concat(manifests.flatMap((m) => m.pages.map((p) => path.join(DOCS, m.dir, p))));
  for (const f of pages) {
    if (!fs.existsSync(f)) continue;
    const rel = path.relative(ROOT, f);
    fs.readFileSync(f, "utf8").split("\n").forEach((line, i) => {
      for (const m of line.matchAll(DOI_LINK_RE)) { const d = doiNorm(m[1]); if (!out.has(d)) out.set(d, `${rel}:${i + 1}`); }
    });
  }
  return out;
}
const bibDois = () => new Set([...(fs.existsSync(BIB) ? fs.readFileSync(BIB, "utf8") : "")
  .matchAll(/(?:^|[\s,{])doi\s*=\s*[{"]\s*([^}"]+?)\s*[}"]/gim)].map((m) => doiNorm(m[1])));
function checkDois(manifests) {
  const have = bibDois();
  for (const [d, at] of linkedDois(manifests))
    if (!have.has(d)) fail(`${at}: DOI ${d} is not in docs/references.bib (the cluster renders offline); run: node tools/lemmata.mjs doi`);
  checkCitations(manifests);
}
// Citations, one style everywhere (2026-10-28): an entry cites papers with @key / [@key]
// from docs/references.bib, and MyST lists them under "References" at the end of the page.
// So in an entry's pages: no link to a paper (doi.org, arxiv.org, as a link or a link
// definition) and no hand-written References section; every @key used must be in the bib.
// Other links (code, data, a project page) are fine.
const PAPER_LINK_RE = /\]\(\s*(https?:\/\/(?:dx\.|www\.)?(?:doi\.org|arxiv\.org)\/[^)\s]+)|^\s*\[[^\]]+\]:\s*(https?:\/\/(?:dx\.|www\.)?(?:doi\.org|arxiv\.org)\/\S+)/gim;
function checkCitations(manifests) {
  const bib = fs.existsSync(BIB) ? fs.readFileSync(BIB, "utf8") : "";
  // An at-sign outside an entry start (in a % comment, say) makes MyST's parser read an
  // entry there and then fail on the whole file, so that no citation on the site resolves
  // (found 2026-10-28: "expected lbrace, got label at line 1").
  bib.split("\n").forEach((line, i) => {
    if (line.includes("@") && !/^\s*@\w+\s*\{/.test(line) && !/^\s*[a-z]+\s*=/i.test(line))
      fail(`docs/references.bib:${i + 1}: an at-sign outside an entry start breaks the whole file for MyST; remove it`);
  });
  const keys = new Set([...bib.matchAll(/^@\w+\s*\{\s*([^,\s]+)\s*,/gm)].map((m) => m[1]));
  const sitePages = ["index.md", "checked.md", "changelog.md", "about.md"].map((p) => ({ f: path.join(DOCS, p), entry: false }));
  const entryPages = manifests.flatMap((m) => m.pages.map((p) => ({ f: path.join(DOCS, m.dir, p), entry: true })));
  for (const { f, entry } of [...sitePages, ...entryPages]) {
    if (!fs.existsSync(f)) continue;
    const rel = path.relative(ROOT, f);
    // Outside code and math: `@` in Lean snippets or $...$ is not a citation.
    let inFence = false;
    fs.readFileSync(f, "utf8").split("\n").forEach((line, i) => {
      if (/^\s*(```|~~~|:::)/.test(line)) { inFence = !inFence && /^\s*(```|~~~)/.test(line) ? true : /^\s*(```|~~~)/.test(line) ? false : inFence; return; }
      if (inFence) return;
      const text = line.replace(/`[^`]*`/g, "").replace(/\$\$?[^$]*\$\$?/g, "");
      for (const m of text.matchAll(/(?<![\w@.\/-])\[?-?@([A-Za-z][\w:-]*[\w])/g))
        if (!keys.has(m[1])) fail(`${rel}:${i + 1}: citation @${m[1]} is not in docs/references.bib (add the entry; \`node tools/lemmata.mjs doi\` fetches it for a DOI)`);
      if (!entry) return;
      for (const m of text.matchAll(PAPER_LINK_RE))
        fail(`${rel}:${i + 1}: cite papers with @key from docs/references.bib, not a link (${m[1] ?? m[2]}); see AGENTS.md, "Cite"`);
      if (/^#{1,6}\s+(references|bibliography|literature)\s*$/i.test(line))
        fail(`${rel}:${i + 1}: no hand-written references section; cite with @key and MyST lists the references at the end of the page`);
    });
  }
}
// `doi`: append a BibTeX entry from doi.org for every linked DOI that references.bib lacks.
// `doi <DOI>…` adds those DOIs (an arXiv paper's is 10.48550/arXiv.<id>); without arguments,
// every DOI linked from the site pages that references.bib lacks. Each entry gets the house
// key: first author's surname, year, first significant title word (braun2014matching).
async function fetchDois(manifests, given = []) {
  const have = bibDois();
  const missing = (given.length ? given.map(doiNorm) : [...linkedDois(manifests).keys()]).filter((d) => !have.has(d));
  if (!missing.length) { console.log(given.length ? "references.bib already has these DOIs" : "references.bib already has every linked DOI"); return; }
  let bib = fs.existsSync(BIB) ? fs.readFileSync(BIB, "utf8") : "";
  for (const d of missing) {
    const r = await fetch(`https://doi.org/${d}`, { headers: { accept: "application/x-bibtex; charset=utf-8" } });
    const text = (await r.text()).trim();
    if (!r.ok || !text.startsWith("@")) { fail(`DOI ${d}: doi.org answered ${r.status}; check the DOI, or add its entry to docs/references.bib by hand`); continue; }
    // The house key, from the entry itself; made unique if it collides.
    // A field's value with balanced braces: doi.org returns one-line records, so "to the end
    // of the line" would run into the next field.
    const field = (f) => {
      const m = new RegExp(`(?:^|[\\s,{])${f}\\s*=\\s*([{"])`, "i").exec(text); if (!m) return "";
      let i = m.index + m[0].length, depth = 1, out = "";
      if (m[1] === '"') { const j = text.indexOf('"', i); return j < 0 ? "" : text.slice(i, j); }
      for (; i < text.length && depth; i++) { const c = text[i]; if (c === "{") depth++; else if (c === "}" && --depth === 0) break; out += c; }
      return out;
    };
    const plain = (x) => x.normalize("NFD").replace(/[\u0300-\u036f]/g, "").replace(/\\[a-z]+\s*|[{}\\'"`^~]/gi, "").toLowerCase();
    const surname = plain((field("author").split(/\s+and\s+/i)[0] ?? "").split(",")[0].trim().split(/\s+/).pop() ?? "ref").replace(/[^a-z]/g, "");
    const STOP = new Set(["a", "an", "the", "on", "of", "and", "for", "in", "to", "with", "is", "are"]);
    const word = plain(field("title")).split(/[^a-z0-9]+/).find((w) => w && !STOP.has(w)) ?? "";
    let key = `${surname || "ref"}${field("year").replace(/\D/g, "")}${word}`, k = key, n = 1;
    while (new RegExp(`\\{${k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`).test(bib)) k = `${key}_${++n}`;
    bib = bib.replace(/\s*$/, "\n\n") + text.replace(/^(@\w+\{)[^,]+,/, `$1${k},`).replace(/\s+\n/g, "\n") + "\n";
    console.log(`added ${d} as ${k}`);
  }
  fs.writeFileSync(BIB, bib);
}

// Every MyST directive in a page, in both fence styles (```{name} and :::{name}, any fence
// length, nested), with its argument and :option: lines. Enough of MyST's grammar to see
// every directive; the Markdown inside is not interpreted. Line numbers are 1-based.
function myStDirectives(text) {
  const out = [], lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^\s*(`{3,}|~{3,}|:{3,})\{([^}\s]+)\}\s*(.*?)\s*$/);
    if (!m) continue;
    const opts = {};
    for (let j = i + 1; j < lines.length; j++) {
      const o = lines[j].match(/^\s*:([\w-]+):\s*(.*?)\s*$/);
      if (!o) break;
      opts[o[1]] = o[2];
    }
    out.push({ name: m[2].toLowerCase(), arg: m[3], opts, line: i + 1 });
  }
  return out;
}

// Directives that read a file at build time, and where the path is. MyST copies or
// inlines what they read into the published site, so a path outside the entry's own
// files would publish whatever the build can read (measured 2026-10-22: a colon-fenced
// literalinclude of ../../x and an absolute path both ended up on the page). The build
// Job limits what it can read; this check refuses such paths before that.
const FILE_DIRECTIVES = {
  include: ["arg"], literalinclude: ["arg"], figure: ["arg"], image: ["arg"],
  "csv-table": ["file"], anywidget: ["arg", "css"], download: ["arg"], bibliography: ["arg"],
  iframe: ["arg"],
};
// Directives that may not be used at all in content: raw output and execution.
const FORBIDDEN_DIRECTIVES = new Set(["raw", "raw:latex", "raw:typst", "code-cell", "eval", "jupyter-execute"]);
function checkFileDirectives(page, roots) {
  const text = fs.readFileSync(page, "utf8"), at = path.relative(ROOT, page);
  for (const d of myStDirectives(text)) {
    const where = `${at}:${d.line}: {${d.name}}`;
    if (FORBIDDEN_DIRECTIVES.has(d.name)) { fail(`${where} is not allowed in content`); continue; }
    const keys = FILE_DIRECTIVES[d.name] ?? [];
    const refs = keys.map((k) => k === "arg" ? d.arg : d.opts[k]).filter((v) => v);
    // {include} with :literal: is a literalinclude in disguise; same rule either way.
    for (const ref of refs) {
      // Web addresses are fine for figures, iframes and anywidget's front-end module.
      if (/^https?:\/\//i.test(ref) && ["figure", "image", "iframe", "anywidget"].includes(d.name)) continue;
      if (/^[a-z][\w+.-]*:/i.test(ref)) { fail(`${where}: ${ref} is not a relative file path`); continue; }
      const abs = safeRel(path.dirname(page), ref, where);
      if (!abs) continue;
      if (!roots.some((r) => abs === r || abs.startsWith(r + path.sep)))
        fail(`${where}: ${ref} is outside this page's files (${roots.map((r) => path.relative(ROOT, r) + "/").join(", ")})`);
    }
  }
}

function checkSnippets(manifests) {
  // What each page may read: an entry page its own docs/<id>/ and lean/Lemmata/<Lean>/,
  // a site page all of docs/; both the shared docs/_static/ and docs/_generated/.
  const shared = [path.join(DOCS, "_static"), path.join(DOCS, "_generated")];
  for (const p of ["index.md", "checked.md", "changelog.md", "about.md"].map((x) => path.join(DOCS, x)))
    if (fs.existsSync(p)) checkFileDirectives(p, [DOCS]);
  for (const m of manifests) for (const p of m.pages) {
    const page = path.join(DOCS, m.dir, p);
    if (fs.existsSync(page)) checkFileDirectives(page, [path.join(DOCS, m.dir), path.join(LEAN, LIB, m.leanDir), ...shared]);
  }
  const pages = [path.join(DOCS, "index.md"),
    ...manifests.flatMap((m) => m.pages.map((p) => path.join(DOCS, m.dir, p)))];
  const re = /```\{literalinclude\}\s+(\S+)\s*\n((?::[^\n]*\n)*)/g;
  for (const page of pages) {
    if (!fs.existsSync(page)) continue;
    const text = fs.readFileSync(page, "utf8");
    const at = path.relative(ROOT, page);
    for (const m of text.matchAll(re)) {
      const target = safeRel(path.dirname(page), m[1], at);
      if (!target) continue;
      if (!fs.existsSync(target)) { fail(`${at}: literalinclude ${m[1]} does not exist`); continue; }
      const src = fs.readFileSync(target, "utf8");
      const opt = (k) => (m[2].match(new RegExp(`^:${k}:\\s*(.*)$`, "m")) || [])[1]?.trim();
      const pos = {};
      for (const k of ["start-after", "end-before"]) {
        const marker = opt(k);
        if (!marker) continue;
        const count = src.split(marker).length - 1;
        if (count !== 1) fail(`${at}: marker "${marker}" occurs ${count} times in ${m[1]}`);
        pos[k] = src.indexOf(marker);
      }
      if (pos["start-after"] !== undefined && pos["end-before"] !== undefined && pos["start-after"] > pos["end-before"])
        fail(`${at}: markers in ${m[1]} are in the wrong order`);
    }
  }
}

function umbrellaText() {
  const mods = walk(path.join(LEAN, LIB), ".lean")
    .map((f) => path.relative(LEAN, f).replace(/\.lean$/, "").split(path.sep).join("."))
    .sort();
  return ["module", "",
    "-- Generated by `node tools/lemmata.mjs umbrella --write` -- do not edit.",
    `-- Imports every module under ${LIB}/, for downstream users. Contributions import the`,
    "-- specific modules they need instead, which keeps the import graph acyclic.",
    ...mods.map((m) => `public import ${m}`), ""].join("\n");
}

// A sparse checkout (git sparse-checkout) has only some entries on disk, so the umbrella,
// which imports every module of every entry, cannot match the files here -- and rewriting it
// from them would drop the entries that are not checked out. The local check needs all
// entries until it has a sparse mode (TODO.md in lemmata-code); this says so instead.
// Detected from git itself; no git (the cluster's source copy) means a complete tree.
function sparseCheckout() {
  try {
    const out = execFileSync("git", ["-C", ROOT, "config", "--get", "core.sparseCheckout"],
      { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim();
    return out === "true";
  } catch { return false; }
}
const SPARSE_HELP = "this is a sparse checkout, and the local check needs every entry " +
  "(`git sparse-checkout disable` restores them; see AGENTS.md, \"If the repository gets large\")";

function checkUmbrella(write) {
  const file = path.join(LEAN, `${LIB}.lean`);
  if (sparseCheckout()) {
    // Never rewrite it here: the result would import only the entries checked out.
    if (write) { fail(`lean/${LIB}.lean is not rewritten: ${SPARSE_HELP}`); return; }
    fail(`lean/${LIB}.lean cannot be checked: ${SPARSE_HELP}`); return;
  }
  const want = umbrellaText();
  if (write) { fs.writeFileSync(file, want); return; }
  const have = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
  if (have !== want) fail(`lean/${LIB}.lean is out of date: run node tools/lemmata.mjs umbrella --write`);
}

// ------------------------------------------------------------------------- generation

// What a Lean file contains, from Lean tokens (comments and strings excluded): the `module`
// header, forbidden declarations and attributes, and the lines that use a computation tactic
// -- for an early error in an entry without native_computation. That last part is a hint,
// not a check: the verifier decides from the compiled files what is a computation.
function leanScan(file) {
  const toks = leanTokens(fs.readFileSync(path.join(ROOT, file), "utf8"));
  const calls = [], forbidden = [];
  const header = toks[0]?.k === "word" && toks[0].t === "module";
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t.k !== "word") continue;
    // `native_decide`, `bv_decide`, …, and `decide` with `native` among its options
    // (`decide +native`, `(config := { native := true })`; the next few tokens).
    if (COMPUTATION_TACTICS.includes(t.t) ||
        (t.t === "decide" && toks.slice(i + 1, i + 12).some((x) => x.k === "word" && x.t === "native"))) calls.push(t.line);
    // `axiom <name>` declares one (the tokenizer keeps names whole, so `Foo.axiom_x` is one
    // word); the two attributes appear inside `@[...]`, alone or after a comma.
    if (t.t === "axiom" && toks[i + 1]?.k === "word") forbidden.push({ what: FORBIDDEN_LEAN.axiom, line: t.line });
    if ((t.t === "implemented_by" || t.t === "extern") && ["[", ","].includes(toks[i - 1]?.t))
      forbidden.push({ what: FORBIDDEN_LEAN[t.t], line: t.line });
  }
  return { calls, forbidden, header };
}
function leanFiles(dir) {
  const abs = path.join(LEAN, LIB, dir);
  return fs.existsSync(abs) ? walk(abs, ".lean").map((f) => path.relative(ROOT, f).split(path.sep).join("/")).sort() : [];
}
// Every Lean file in the library: a `module`, in an entry's directory or Shared/, with no
// forbidden declaration or attribute, and no computation tactic outside an entry that
// declared native_computation (Shared has no manifest). The verifier enforces the last point
// on the compiled files as well; this gives the error early, with a file and line.
function checkLeanSources(manifests) {
  const byDir = new Map(manifests.map((m) => [m.leanDir, m]));
  const dirs = fs.existsSync(path.join(LEAN, LIB)) ? listDirs(path.join(LEAN, LIB)) : [];
  // A file directly in lean/Lemmata/ belongs to no entry, but Lake builds it (the lakefile
  // globs Lemmata.*) and entries can import it.
  if (fs.existsSync(path.join(LEAN, LIB)))
    for (const d of fs.readdirSync(path.join(LEAN, LIB), { withFileTypes: true }))
      if (!d.isDirectory() && d.name.endsWith(".lean"))
        fail(`lean/${LIB}/${d.name}: Lean files belong in lean/${LIB}/<LeanName>/ (an entry) or lean/${LIB}/Shared/, not directly in lean/${LIB}/`);
  for (const d of dirs) for (const f of leanFiles(d)) {
    const { calls, forbidden, header } = leanScan(f);
    if (!header) fail(`${f}: the first line must be \`module\` (Lean's module system; see AGENTS.md, Write the Lean)`);
    for (const x of forbidden) fail(`${f}:${x.line}: ${x.what} is not allowed (it asserts or replaces something Lean's kernel cannot check)`);
    const m = byDir.get(d);
    if (calls.length && !m?.native) fail(`${f}:${calls[0]}: computation tactic (native_decide, decide +native, bv_decide) ` +
      (m ? `in an entry without \`native_computation: true\` in docs/${m.dir}/contribution.yml` : "outside an entry (lean/Lemmata/Shared must stay kernel-checked)"));
  }
}

function verifierRequest(manifests) {
  const frozen = loadFrozen();          // not built, so not checked: they keep their last result
  return {
    root: LIB,
    allowed_axioms: ALLOWED_AXIOMS,
    exports: manifests.filter((m) => !frozen[m.id]).flatMap((m) => m.exports.map((e) =>
      ({ contribution: m.id, name: e.name, kind: e.kind, namespace: m.lean_namespace }))),
    // Entries that may rely on computations: the verifier accepts a computation axiom only
    // in their modules.
    native: manifests.filter((m) => m.native).map((m) => ({ contribution: m.id, namespace: m.lean_namespace })),
  };
}

const esc = (s) => String(s).replace(/[<>&`]/g, (c) => ({ "<": "&lt;", ">": "&gt;", "&": "&amp;", "`": "\\`" }[c]));

function titleOf(m) {
  const text = fs.readFileSync(path.join(DOCS, m.dir, "index.md"), "utf8");
  const fm = text.match(/^---\n([\s\S]*?)\n---/);
  return (fm && YAML.parse(fm[1])?.title) || m.id;
}

// BibTeX for one entry. Every field comes from data the tools trust: title from the page,
// authors and year from git (provenance), ids from the manifest, URLs from the site.
// `url` is the permanent identifier URL (/abs/YYYY.NNNNN, or /<dir>/ before one is
// assigned); the commit in `note` names the exact version. No `urldate`: it would be the
// build date, not the reader's.
const bibEscape = (v) => String(v).replace(/[\\{}]/g, "").replace(/([&%$#_])/g, "\\$1");
// Names stay exactly as git has them ("Ludwig van Beethoven"): BibTeX parses
// "First von Last" itself, particles included, which a naive reordering gets wrong.
const bibName = (n) => n.trim().replace(/\s+/g, " ");
// Who to credit: the manifest's explicit list if given, else everyone who committed.
// The withdrawal notice, first thing on the entry and on its /abs/ page.
const withdrawnNotice = (m) => m.notes?.withdrawn
  ? [":::{div}", ":class: lemmata-withdrawn", "", `**Withdrawn.** ${m.notes.withdrawn}`, "",
     "The entry stays available under its identifier as a record; it is no longer listed as a current entry.", ":::", ""]
  : [];
const licenseLine = (m) => `License: [${LICENSES[m.license].name}](${LICENSES[m.license].url})`;
const people = (m, p) => m.contributors.length ? m.contributors : (p?.contributors ?? []);
// ORCID iD: four groups of four, the last character a digit or X, which is the ISO 7064
// MOD 11-2 check digit of the other fifteen (so a mistyped iD is caught).
function orcidValid(id) {
  if (!/^\d{4}-\d{4}-\d{4}-\d{3}[\dX]$/.test(id)) return false;
  const d = id.replace(/-/g, ""); let t = 0;
  for (let i = 0; i < 15; i++) t = (t + Number(d[i])) * 2;
  const r = (12 - (t % 11)) % 11;
  return d[15] === (r === 10 ? "X" : String(r));
}
// An author's name in a header: linked to their author page when they have an ORCID iD,
// plain otherwise (a name alone does not identify a person). `up` is the path to docs/.
// The author page's directory. Not the bare iD: MyST strips leading digit groups from page
// paths as an ordering prefix, so "0009-0000-5193-184X" was published at /a/x/ (measured).
// A letter prefix, lower case, survives: /a/orcid-0009-0000-5193-184x/.
const authorDir = (orcid) => `orcid-${orcid.toLowerCase()}`;
const authorName = (c, up) => c.orcid ? `[**${esc(c.name)}**](${up}${AUTHOR_DIR}/${authorDir(c.orcid)}/index.md)` : `**${esc(c.name)}**`;
// A {first, last} name is written "{Last}, First": braces keep a multi-part surname whole.
const bibAuthor = (c) => c.last !== undefined
  ? (c.first ? `{${bibEscape(c.last)}}, ${bibEscape(c.first)}` : `{${bibEscape(c.last)}}`)
  : bibEscape(bibName(c.name));
function bibtex(m, title, p, { siteUrl, commit, checked, computation = false, ident }) {
  // With an identifier, both the key and the URL are the permanent ones; the directory
  // name is an internal detail that may change.
  const stable = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
  const fields = [
    ["title", `{${bibEscape(title)}}`],
    ["author", people(m, p).length ? people(m, p).map(bibAuthor).join(" and ") : "{Lemmata Repository contributors}"],
    ["howpublished", ident ? `Lemmata Repository, lemmata:${ident}, \\url{${stable}}` : `Lemmata Repository, \\url{${stable}}`],
    ["year", p ? p.first.date.slice(0, 4) : String(new Date().getUTCFullYear())],
    ["url", stable],
  ];
  // No snapshot URL: old releases are pruned, so a citation must not depend on one. The
  // permanent /abs/ URL always resolves; the commit names the exact version cited.
  const note = [commit ? `Version ${commit.slice(0, 12)}` : null,
    checked ? `formal statements checked in Lean 4${computation ? ", modulo computation" : ""}` : null]
    .filter(Boolean).join("; ");
  if (note) fields.push(["note", note]);
  if (m.arxiv.length) fields.push(["eprint", m.arxiv[0]], ["archivePrefix", "arXiv"]);
  const key = ident ? `lemmata:${ident}` : `lemmata:${m.dir}`;
  const w = Math.max(...fields.map(([k]) => k.length));
  return `@misc{${key},\n` + fields.map(([k, v]) => `  ${k.padEnd(w)} = {${v.replace(/^\{(.*)\}$/s, "$1")}}`).join(",\n") + "\n}";
}

// .lemmata/provenance.json if the cluster supplied it; otherwise compute the same shape
// from local git (a working checkout), or null if there is no git at all.
// Stable identifiers (lemmata:YYYY.NNNNN) are assigned by the cluster and shipped as
// .lemmata/identifiers.json; a local preview has none ("assigned on publication").
// Id-keyed tables (identifiers, frozen entries, provenance) as objects without a prototype,
// so a lookup like frozen[m.id] can never hit Object.prototype: an entry named "constructor"
// once read as frozen and its exports were left out of the verifier request (review,
// 2026-10-22). Ids naming such properties are also refused in validate.
const byId = (o) => Object.assign(Object.create(null), o ?? {});

function loadIdentifiers(commit) {
  const shipped = path.join(ROOT, ".lemmata", "identifiers.json");
  if (!fs.existsSync(shipped)) return byId();
  const d = JSON.parse(fs.readFileSync(shipped, "utf8"));
  if (commit && d.source_commit && d.source_commit !== commit) fail(`.lemmata/identifiers.json is for ${d.source_commit}, not ${commit}`);
  for (const [entry, ident] of Object.entries(d.entries ?? {}))
    if (!/^\d{4}\.\d{5}$/.test(ident)) fail(`.lemmata/identifiers.json: bad identifier ${ident} for ${entry}`);
  return byId(d.entries);
}

// Entries an admin froze, with their last successful check (commit, versions, date,
// results), shipped by the cluster as .lemmata/frozen.json. Empty outside the cluster.
function loadFrozen() {
  const f = path.join(ROOT, ".lemmata", "frozen.json");
  return byId(fs.existsSync(f) ? JSON.parse(fs.readFileSync(f, "utf8")).entries : null);
}

function loadProvenance(manifests, commit) {
  const shipped = path.join(ROOT, ".lemmata", "provenance.json");
  if (fs.existsSync(shipped)) {
    const p = JSON.parse(fs.readFileSync(shipped, "utf8"));
    p.entries = byId(p.entries);
    if (commit && p.source_commit !== commit) fail(`.lemmata/provenance.json is for ${p.source_commit}, not ${commit}`);
    return p;
  }
  const git = (...a) => execFileSync("git", ["-C", ROOT, ...a], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] });
  try { git("rev-parse", "HEAD"); } catch { return null; }
  const out = { schema_version: 1, source_commit: git("rev-parse", "HEAD").trim(), entries: byId() };
  for (const m of manifests) {
    const log = git("log", "--no-merges", "--format=%H%x1f%an%x1f%ae%x1f%aI", "HEAD", "--", `docs/${m.dir}`, `lean/${LIB}/${m.leanDir}`);
    const commits = log.split("\n").filter(Boolean).map((l) => { const [hash, name, email, date] = l.split("\x1f"); return { hash, name, email: email.toLowerCase(), date }; });
    if (!commits.length) continue;
    const people = new Map();
    for (const c of [...commits].reverse()) {
      const p = people.get(c.email) ?? { name: c.name, commits: 0, first: c.date };
      p.commits++; p.name = c.name; people.set(c.email, p);
    }
    out.entries[m.id] = {
      contributors: [...people.values()].sort((a, b) => b.commits - a.commits || a.first.localeCompare(b.first)).map(({ name, commits }) => ({ name, commits })),
      first: { commit: commits.at(-1).hash, date: commits.at(-1).date },
      last: { commit: commits[0].hash, date: commits[0].date },
    };
  }
  return out;
}

// Panels and catalog come only from the verifier's report, never from page content.
// Links into the content repository, for whichever forge hosts it. The repository's web
// address is the only required input (the build Job gets it as SOURCE_WEB_URL, from the
// cluster's one CONTENT_WEB setting), so moving the repo is a configuration change.
// GitLab puts "/-/" before blob/commit; GitHub, Gitea and Forgejo do not. The style is
// guessed from the host name ("gitlab" in it), and SOURCE_FORGE=gitlab|github overrides
// the guess -- needed for self-hosted GitLab under another name, such as git.zib.de.
// The source text of a Lean declaration, for showing it next to the result on the page.
// Read from the trusted source tree (the render step's pristine copy), using the file the
// verifier reported; the verifier itself loads no environment extensions, so it has no
// declaration ranges to offer. Found by Lean syntax, not by text (review, 2026-10-22): the
// file is tokenized so comments (line, nested block), strings and char literals are never
// mistaken for code, `namespace`/`section`/`end` are tracked so the declaration is matched
// by its fully qualified name, a theorem is cut at its first top-level ":=" (the
// statement, not the proof), and a definition runs to the next top-level command (a blank
// line inside it does not end it). Returns { from, to, declLine, text } with 1-based lines,
// or null if the declaration is not in the file.
const DECL_KW = new Set(["theorem", "lemma", "def", "abbrev", "structure", "instance", "inductive", "class", "opaque", "axiom", "example"]);
const DECL_MOD = new Set(["private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "public"]);
// Tokens that start a new top-level command, ending a definition's body.
const COMMAND_KW = new Set([...DECL_KW, "namespace", "section", "end", "open", "variable", "universe", "set_option",
  "attribute", "export", "mutual", "import", "module", "macro", "macro_rules", "syntax", "notation", "infix", "infixl",
  "infixr", "prefix", "postfix", "elab", "deriving", "initialize", "noncomputable", "private", "protected", "public",
  "theorem", "#check", "#eval", "#print", "#reduce", "#guard"]);
function leanTokens(src) {
  // [{t: text, k: "word"|"sym"|"str"|"doc", start, line}], comments other than doc comments
  // dropped. Doc comments (/-- ... -/) are kept as one token so they can be shown.
  const toks = []; let i = 0, line = 1;
  const adv = (n) => { for (let k = 0; k < n; k++) if (src[i + k] === "\n") line++; i += n; };
  while (i < src.length) {
    const c = src[i], c2 = src.slice(i, i + 2);
    if (c === "\n" || c === " " || c === "\t" || c === "\r") { adv(1); continue; }
    if (c2 === "--") { while (i < src.length && src[i] !== "\n") i++; continue; }
    if (c2 === "/-") {                                  // block comment, nested
      const doc = src[i + 2] === "-" && src[i + 3] !== "/", s0 = i, l0 = line; let depth = 0;
      while (i < src.length) {
        if (src.startsWith("/-", i)) { depth++; adv(2); }
        else if (src.startsWith("-/", i)) { depth--; adv(2); if (depth === 0) break; }
        else adv(1);
      }
      if (doc) toks.push({ t: src.slice(s0, i), k: "doc", start: s0, line: l0 });
      continue;
    }
    if (c === '"') {                                    // string literal with escapes
      const s0 = i, l0 = line; adv(1);
      while (i < src.length && src[i] !== '"') adv(src[i] === "\\" ? 2 : 1);
      adv(1); toks.push({ t: src.slice(s0, i), k: "str", start: s0, line: l0 }); continue;
    }
    if (c === "'" && /^'(\\.|[^\\'])'/u.test(src.slice(i, i + 6))) { // char literal 'a', '\n'
      const m = src.slice(i).match(/^'(\\.|[^\\'])'/u); toks.push({ t: m[0], k: "str", start: i, line }); adv(m[0].length); continue;
    }
    if (c === "«") { const j = src.indexOf("»", i); const e = j < 0 ? src.length : j + 1; toks.push({ t: src.slice(i, e), k: "word", start: i, line }); adv(e - i); continue; }
    const w = src.slice(i).match(/^(#?[\p{L}_][\p{L}\p{N}_'!?.₀-₉ₐ-ₜ]*)/u);
    if (w) { toks.push({ t: w[1].replace(/\.$/, ""), k: "word", start: i, line }); adv(w[1].replace(/\.$/, "").length || 1); continue; }
    if (c2 === ":=") { toks.push({ t: ":=", k: "sym", start: i, line }); adv(2); continue; }
    toks.push({ t: c, k: "sym", start: i, line }); adv(1);
  }
  return toks;
}
function leanStatement(file, fullName) {
  let src; try { src = fs.readFileSync(path.join(ROOT, file), "utf8"); } catch { return null; }
  const toks = leanTokens(src), scopes = [];          // [{kind: "namespace"|"section", name}]
  const prefix = () => scopes.filter((s) => s.kind === "namespace").map((s) => s.name).join(".");
  let depth = 0;                                       // bracket depth, for top-level ":="
  for (let i = 0; i < toks.length; i++) {
    const tk = toks[i];
    if (tk.k === "sym") { if ("([{⟨".includes(tk.t)) depth++; else if (")]}⟩".includes(tk.t)) depth = Math.max(0, depth - 1); continue; }
    if (tk.k !== "word" || depth > 0) continue;
    if (tk.t === "namespace" && toks[i + 1]?.k === "word") { scopes.push({ kind: "namespace", name: toks[i + 1].t }); i++; continue; }
    if (tk.t === "section") { scopes.push({ kind: "section", name: toks[i + 1]?.k === "word" ? toks[i + 1].t : "" }); continue; }
    if (tk.t === "end") {                              // closes the innermost matching scope
      const nm = toks[i + 1]?.k === "word" && toks[i + 1].line === tk.line ? toks[i + 1].t : "";
      const k = scopes.map((s) => s.name).lastIndexOf(nm); if (k >= 0) scopes.splice(k); else scopes.pop();
      continue;
    }
    if (!DECL_KW.has(tk.t)) continue;
    // Modifiers and attributes directly before the keyword belong to the declaration.
    let first = i;
    while (first > 0 && (DECL_MOD.has(toks[first - 1].t) || toks[first - 1].t === "]")) {
      if (toks[first - 1].t === "]") { let b = first - 1; while (b > 0 && toks[b].t !== "@") b--; if (toks[b]?.t !== "@") break; first = b; }
      else first--;
    }
    const nameTok = toks[i + 1];
    if (!nameTok || nameTok.k !== "word") continue;
    const qualified = nameTok.t.startsWith("_root_.") ? nameTok.t.slice(7) : [prefix(), nameTok.t].filter(Boolean).join(".");
    if (qualified !== fullName) continue;
    const isTheorem = tk.t === "theorem" || tk.t === "lemma";
    // End: a theorem at its first top-level ":="; anything else at the next top-level command.
    let endTok = null, d = 0;
    for (let j = i + 2; j < toks.length; j++) {
      const t = toks[j];
      if (t.k === "sym") {
        if ("([{⟨".includes(t.t)) d++; else if (")]}⟩".includes(t.t)) d = Math.max(0, d - 1);
        else if (isTheorem && d === 0 && t.t === ":=") { endTok = { cut: t.start }; break; }
        continue;
      }
      if (d === 0 && (t.k === "doc" || (t.k === "word" && COMMAND_KW.has(t.t) && j > i + 1 && toks[j - 1].line < t.line))) { endTok = { cut: t.start }; break; }
    }
    const declStart = toks[first].start;
    const cut = endTok ? endTok.cut : src.length;
    const body = src.slice(declStart, cut).replace(/\s+$/, "");
    // A doc comment directly before the declaration is shown with it.
    const prev = toks[first - 1];
    const docStart = prev?.k === "doc" ? prev.start : declStart;
    const text = (prev?.k === "doc" ? src.slice(prev.start, declStart) : "") + body;
    const lineOf = (pos) => src.slice(0, pos).split("\n").length;
    return { from: lineOf(docStart), to: lineOf(declStart + body.length), declLine: lineOf(declStart), text: text.replace(/\s+$/, "") };
  }
  return null;
}

function forgeLinks(webUrl, forge = process.env.SOURCE_FORGE) {
  if (!webUrl) return null;
  const base = webUrl.replace(/\/+$/, "").replace(/\.git$/, "");
  const gitlab = forge ? forge === "gitlab" : /gitlab/i.test(new URL(base).host);
  const sep = gitlab ? "/-" : "";
  return { blob: (sha, file) => `${base}${sep}/blob/${sha}/${file}`, commit: (sha) => `${base}${sep}/commit/${sha}` };
}

// Computations a result relies on, from the verifier's report, and the resulting status:
//   "kernel"    no computation anywhere in its dependencies           (kernel-checked)
//   "inherited" only computations of other entries                   (kernel-checked, modulo computation)
//   "own"       a computation of its own entry                        (checked by computation)
// An entry's own computations are those defined in its namespace. Frozen entries keep the
// classification recorded with their last check.
const COMPUTATION_PAGE_LINK = "../checked.md#computation";
function computationView(manifests, report) {
  const byNs = manifests.map((m) => [m.lean_namespace + ".", m]).sort((a, b) => b[0].length - a[0].length);
  const entryOfModule = (mod) => byNs.find(([ns]) => (mod + ".").startsWith(ns))?.[1] ?? null;
  const claims = new Map((report?.computations ?? []).map((c) => [c.name, c]));
  // For one export of entry m: { status, own: [claim], other: [{entry, claims}] }.
  const of = (m, r) => {
    const uses = (r?.computations ?? []).map((u) => ({ ...claims.get(u.name), name: u.name, entry: entryOfModule(u.module) }));
    const own = uses.filter((u) => u.entry?.id === m.id), other = uses.filter((u) => u.entry?.id !== m.id);
    const byEntry = new Map();
    for (const u of other) { const k = u.entry?.id ?? "?"; if (!byEntry.has(k)) byEntry.set(k, { entry: u.entry, claims: [] }); byEntry.get(k).claims.push(u); }
    return { status: own.length ? "own" : other.length ? "inherited" : "kernel", own, other: [...byEntry.values()] };
  };
  // A frozen entry's result, from what the controller recorded at its last check (the claims
  // themselves since 2026-10-26; older records only have the status, so no claims are listed).
  const ofFrozen = (m, x) => {
    const uses = (x?.computations ?? []).map((u) => ({ ...u, entry: entryOfModule(u.module ?? "") }));
    const own = uses.filter((u) => u.entry?.id === m.id), other = uses.filter((u) => u.entry?.id !== m.id);
    const byEntry = new Map();
    for (const u of other) { const k = u.entry?.id ?? "?"; if (!byEntry.has(k)) byEntry.set(k, { entry: u.entry, claims: [] }); byEntry.get(k).claims.push(u); }
    const status = x?.computation ?? (own.length ? "own" : other.length ? "inherited" : "kernel");
    return { status, own, other: [...byEntry.values()] };
  };
  return { of, ofFrozen, claims: [...claims.values()], entryOfModule };
}
// Wording, kept in one place: the three statuses as badges and as short list values.
const COMPUTATION_WORDS = {
  kernel: { badge: "✓ kernel-checked", short: "checked" },
  inherited: { badge: "◐ kernel-checked, modulo computation", short: "checked mod. computation" },
  own: { badge: "⚙ checked by computation", short: "checked mod. computation" },
};
// The weakest status among an entry's results ("own" < "inherited" < "kernel").
const weakest = (list) => list.includes("own") ? "own" : list.includes("inherited") ? "inherited" : "kernel";

function prepare(manifests, tax, report, { commit, sourceUrl }) {
  const forge = forgeLinks(sourceUrl);
  const gen = path.join(DOCS, "_generated");
  const subjRoot = path.join(DOCS, SUBJECT_DIR), topicRoot = path.join(DOCS, TOPIC_DIR), oldCatRoot = path.join(DOCS, OLD_CATEGORY_DIR);
  const absRoot = path.join(DOCS, "abs");
  const authorRoot = path.join(DOCS, AUTHOR_DIR);
  for (const d of [gen, subjRoot, topicRoot, oldCatRoot, absRoot, authorRoot]) fs.rmSync(d, { recursive: true, force: true });
  fs.mkdirSync(path.join(gen, "verification"), { recursive: true });
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const link = (file) => forge && commit ? forge.blob(commit, file) : null;
  // Frozen entries (admin decision, see lemmata-code/frozen.json) were not built: they keep
  // their last successful check, shown with its Lean version and date.
  const idents = loadIdentifiers(commit);
  // Where links to an entry point: its identifier URL /html/<ident> once it has one (the
  // address readers see and share, independent of the directory name), else its
  // directory page, written relative to the linking page so MyST checks it.
  const entryHref = (m, rel) => idents[m.id] ? `/html/${idents[m.id]}` : `${rel}${m.dir}/index.md`;
  const frozen = loadFrozen();
  const comp = computationView(manifests, report);
  // Per export: kernel / inherited / own (frozen entries: as recorded at their last check).
  const compOf = (m, e) => {
    if (frozen[m.id]) return comp.ofFrozen(m, (frozen[m.id].results ?? []).find((y) => y.name === e.name));
    return comp.of(m, byName.get(e.name));
  };
  const entryComp = (m) => weakest(m.exports.map((e) => compOf(m, e).status));
  // "; relies on 1 computation of this entry, listed below, and on 2 computations from
  // lemmata:2611.00001" -- after a result in the verification panel.
  const reliesOn = (m, c, ok) => {
    if (!ok || c.status === "kernel") return "";
    const n = (k) => `${k} computation${k === 1 ? "" : "s"}`;
    const others = c.other.map((o) => `${n(o.claims.length)} from ` +
      (o.entry ? `[${idents[o.entry.id] ? `lemmata:${idents[o.entry.id]}` : esc(titleOf(o.entry))}](${entryHref(o.entry, "../")})` : "another entry")).join(", ");
    const parts = [c.own.length ? `${n(c.own.length)} of this entry, listed below` : null, c.other.length ? others : null].filter(Boolean);
    return parts.length ? "; relies on " + parts.join(", and on ") : "; relies on computation";
  };
  // The distinct claims of this entry that its frozen results recorded.
  const frozenClaims = (m) => {
    const seen = new Map();
    for (const x of frozen[m.id]?.results ?? []) for (const u of x.computations ?? [])
      if (comp.entryOfModule(u.module ?? "")?.id === m.id && !seen.has(u.name)) seen.set(u.name, u);
    return [...seen.values()];
  };
  // "Computations assumed": every claim with the line that runs it, grouped by source file,
  // one collapsed block per file. The line comes from the source shown, so for a frozen entry
  // it is the file at the frozen commit (unchanged since, which freezing requires). The claims
  // as the kernel stores them are left out: they can be very long (one real entry had 128
  // claims totalling 860 kB, which made its page 3.6 MB) and are in lemmata.json, linked.
  const claimList = (m, claims, linkFor, usedNames = null) => {
    if (!claims.length) return [];
    const one = claims.length === 1;
    // Computations in helpers that no displayed result uses are listed too, but said so.
    const unused = usedNames ? claims.filter((x) => !usedNames.has(x.name)).length : 0;
    const byFile = new Map();
    for (const x of claims) { const f = x.source_file ?? "?"; if (!byFile.has(f)) byFile.set(f, []); byFile.get(f).push(x); }
    const out = ["", `**Computations assumed.** ${one ? "This claim was" : `These ${claims.length} claims were`} ` +
      `evaluated by compiled code during the build and ${one ? "is" : "are"} **not** checked by Lean's kernel or re-run by the archive. ` +
      `Running \`tools/check.sh\` re-runs ${one ? "it" : "them"}. [What this means](${COMPUTATION_PAGE_LINK}). ` +
      (unused ? `${claims.length - unused} of them are used by the results above; the other ${unused} sit in helper declarations no displayed result depends on. ` : "") +
      `Each claim as the kernel stores it is in [\`lemmata.json\`](${(process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "")}/lemmata.json).`, ""];
    // Inside the panel (a 4-colon dropdown), so each file's block uses 3 colons.
    for (const [file, xs] of [...byFile].sort((a, b) => a[0].localeCompare(b[0]))) {
      const at = file !== "?" ? linkFor(file) : null;
      out.push(`:::{dropdown} ${file.replace(/^lean\//, "")} — ${xs.length} claim${xs.length === 1 ? "" : "s"}`, "");
      const src = (() => { try { return fs.readFileSync(path.join(ROOT, file), "utf8").split("\n"); } catch { return []; } })();
      for (const x of xs.sort((a, b) => (a.line ?? 0) - (b.line ?? 0))) {
        const line = src[(x.line ?? 0) - 1]?.trim() ?? "";
        out.push(`- \`${String(x.declaration ?? x.name).split(".").slice(-1)[0]}\`, ${x.tactic ?? "computation"}, ` +
          (at ? `[line ${x.line}](${at}#L${x.line})` : `line ${x.line}`) + (line ? `: \`${line.replace(/`/g, "'")}\`` : ""));
      }
      out.push("", ":::", "");
    }
    return out;
  };
  const statusOf = (m) => frozen[m.id] ? "frozen" : !report ? "preview"
    : !m.exports.every((e) => passed && byName.get(e.name)?.status === "checked") ? "failed"
    : entryComp(m) === "kernel" ? "checked" : "computation";

  // One box per bound result: "Lean `Name` · ✅ kernel-checked · source", then the
  // statement (a theorem up to ":=", a definition in full; for a theorem whose type is a
  // named Prop, that Prop's definition too), collapsed. Lines link to the source at the
  // commit that was checked.
  const leanBoxes = (m, fz) => {
    const old = fz ? new Map((fz.results ?? []).map((x) => [x.name, x])) : null;
    // Fence lengths nest outward: container 6 colons, box 5, dropdown 4 (an inner fence
    // must be shorter than the one around it, or it closes the outer one).
    const out = ["::::::{div}", ":class: lemmata-lean-boxes", ""];
    for (const e of m.exports) {
      const r = byName.get(e.name);
      const file = r?.source_file;
      const at = fz ? fz.commit : commit;
      const ok = fz ? old.get(e.name)?.status === "checked" : passed && r?.status === "checked";
      const cs = compOf(m, e).status;
      const badge = !report && !fz ? "○ not verified (preview)" : !ok ? "✗ not checked"
        : e.kind === "definition" ? (cs === "kernel" ? "◇ elaborated" : `◇ elaborated, ${cs === "own" ? "uses computation" : "modulo computation"}`)
        : cs === "kernel" ? "✅ kernel-checked" : `[${COMPUTATION_WORDS[cs].badge}](${COMPUTATION_PAGE_LINK})`;
      // By the fully qualified name the verifier checked, in the file it reported.
      const st = file ? leanStatement(file, e.name) : null;
      // With a report, every checked export must be locatable in its source: otherwise its
      // box would show no statement, and readers could not compare it with the prose.
      if (file && !st && report) fail(`${m.dir}: cannot find the declaration of ${e.name} in ${file} ` +
        "(declare it with `theorem`/`def` inside its `namespace`, not generated by a macro)");
      const range = (f, s) => forge && at && f ? `${forge.blob(at, f)}#L${s.from}${s.to > s.from ? `-L${s.to}` : ""}` : null;
      const src = st && range(file, st);
      out.push(`:::::{div}`, `:class: lemmata-lean-for lemmata-for-${e.label}`, "",
        `**Lean** \`${e.name.split(".").slice(-1)[0]}\` · ${badge}` + (src ? ` · [source](${src})` : ""), "");
      if (st) {
        // A theorem stated as a named Prop (`theorem t : CertifiedSlackFactorization`): show
        // that Prop's definition as well, from the entry's own Lean files.
        let prop = null;
        const named = r?.type && /^[\w.']+(\.\{[^}]*\})?$/.test(r.type) && r.type.includes(".") ? r.type.replace(/\.\{.*$/, "") : null;
        // The type names a constant: look for exactly that constant (fully qualified, from
        // the kernel type) among the entry's own Lean files.
        if (named && e.kind === "theorem") {
          const leanRoot = path.join("lean", LIB, m.leanDir);
          const files = walk(path.join(ROOT, leanRoot), ".lean").map((x) => path.relative(ROOT, x));
          for (const f of [file, ...files.filter((x) => x !== file)]) {
            const ps = leanStatement(f, named); if (ps) { prop = { file: f, ...ps }; break; }
          }
        }
        out.push(`::::{dropdown} ${e.kind === "definition" ? "Definition" : "Statement"} in Lean`, "", "```lean", st.text, "```");
        if (prop) out.push("", `where \`${named.split(".").pop()}\` is` + (range(prop.file, prop) ? ` ([source](${range(prop.file, prop)}))` : "") + ":", "",
          "```lean", prop.text, "```");
        out.push("::::", "");
      }
      out.push(":::::", "");
    }
    out.push("::::::");
    return out;
  };

  // Verification panel per entry, from the verifier's report only.
  for (const m of manifests) {
    // Collapsed, with the outcome in the bar: one click opens the per-result list.
    const fz = frozen[m.id], n = m.exports.length;
    const okCount = fz ? m.exports.filter((e) => (fz.results ?? []).some((x) => x.name === e.name && x.status === "checked")).length
      : m.exports.filter((e) => passed && byName.get(e.name)?.status === "checked").length;
    // Results relying on computations are counted apart from kernel-checked ones.
    const compN = m.exports.filter((e) => compOf(m, e).status !== "kernel").length;
    const summary = !report && !fz ? `○ not verified (local preview)`
      : okCount !== n ? `✗ ${n - okCount} of ${n} formal results not checked`
      : compN === 0 ? `✅ ${n === 1 ? "the formal result is" : `all ${n} formal results are`} ${fz ? "checked" : "kernel-checked"}`
      : compN === n ? `◐ ${n === 1 ? "the formal result relies" : `all ${n} formal results rely`} on computation`
      : `◐ ${n - compN} of ${n} formal results kernel-checked; ${compN} rel${compN === 1 ? "ies" : "y"} on computation`;
    const lines = [`::::{dropdown} Formal verification — ${summary}`, ":class: lemmata-verification", ""];
    if (fz) {
      const old = new Map((fz.results ?? []).map((x) => [x.name, x]));
      for (const e of m.exports) {
        const ok = old.get(e.name)?.status === "checked";
        const c = compOf(m, e);
        const badge = !ok ? "**✗ not checked**" : e.kind === "definition" ? "**◇ elaborated definition**"
          : c.status === "kernel" ? "**✓ kernel-checked**" : c.status === "own" ? "**⚙ checked by computation**"
          : "**◐ kernel-checked, modulo computation**";
        const src = forge ? forge.blob(fz.commit, `lean/${LIB}/${m.leanDir}`) : null;
        lines.push(`- ${badge} [](#${e.label}) — \`${e.name}\`` + (src ? ` ([source](${src}))` : "") + reliesOn(m, c, ok));
      }
      lines.push(...claimList(m, frozenClaims(m), (f) => forge ? forge.blob(fz.commit, f) : null));
      lines.push("", `**Last checked with Lean v${esc(fz.lean_version ?? "?")} on ${String(fz.checked_at ?? "").slice(0, 10)}** ` +
        `(commit \`${String(fz.commit).slice(0, 12)}\`)` +
        (report?.lean_version && report.lean_version !== fz.lean_version ? `; not re-checked with the current Lean v${esc(report.lean_version)}.` : ".") +
        " The Lean source shown is unchanged since that check. " +
        `[What "checked" means](${CHECKED_PAGE_LINK}).`, "::::", "");
    }
    else for (const e of m.exports) {
      const r = byName.get(e.name);
      const ok = passed && r?.status === "checked";
      const lean = report?.lean_version ? ` (Lean v${esc(report.lean_version)})` : "";
      const c = compOf(m, e);
      const badge = !report ? "**○ not verified (preview)**"
        : !ok ? "**✗ failed**"
        : e.kind === "definition" ? `**◇ elaborated definition${lean}**`
        : c.status === "kernel" ? `**✓ kernel-checked${lean}**`
        : c.status === "own" ? `**⚙ checked by computation${lean}**`
        : `**◐ kernel-checked${lean}, modulo computation**`;
      const detail = reliesOn(m, c, ok);
      const src = r && link(r.source_file);
      // The standard axioms a result uses are not listed here: every published result is
      // held to the same policy (see the "checked" page), and lemmata.json carries them per
      // result. Computations are listed, below.
      lines.push(`- ${badge} [](#${e.label}) — \`${e.name}\`` + (src ? ` ([source](${src}))` : "") + detail);
    }
    // Every computation this entry's results rely on that the entry itself contributes:
    // where it is in the source (linked to the line) and what it claims, verbatim as the
    // kernel stores it (the verifier reads compiled files without notation).
    if (!fz && report && passed) {
      const used = new Set(m.exports.flatMap((e) => (byName.get(e.name)?.computations ?? []).map((u) => u.name)));
      lines.push(...claimList(m, comp.claims.filter((x) => comp.entryOfModule(x.module)?.id === m.id), link, used));
    }
    if (!fz) lines.push("",
      report ? `Checked${commit ? ` at commit \`${commit.slice(0, 12)}\`` : ""}. The formal statement is ` +
        "machine-checked" + (compN ? ", modulo the computations named above" : "") + "; that it matches the prose is checked by review. " +
        `[What "checked" means](${CHECKED_PAGE_LINK}).`
      : "This is a local preview: nothing on this page has been verified.",
      "::::", "");
    // Lean next to each result: per bound result, its declaration, status, statement and a
    // link to the exact lines. Rendered here, in one hidden block; the page script moves
    // each box under the result with that label (class lemmata-for-<label>). Without the
    // script they stay hidden and the panel above remains the complete list.
    lines.push(...leanBoxes(m, fz), "");
    // Related material, AI use, acknowledgements and the license close the entry.
    const notes = Object.entries(NOTE_KEYS).filter(([k]) => m.notes?.[k]);
    lines.push(":::{div}", ":class: lemmata-notes", "");
    if (m.related.length) {
      lines.push("**Related material.**", "");
      for (const r of m.related) lines.push(`- ${r.kind[0].toUpperCase() + r.kind.slice(1)}: [${r.title}](${r.url})`);
      lines.push("");
    }
    for (const [k, title] of notes) lines.push(`**${title}.** ${m.notes[k]}`, "");
    lines.push(licenseLine(m), "", ":::", "");
    // Comments, one discussion per entry, keyed by its directory (stable when the title
    // changes). Only a placeholder here: the page script loads giscus into it after React
    // has hydrated (a <script> in the page body would be dropped or mismatch).
    if (GISCUS) lines.push(":::{div}", `:class: lemmata-giscus lemmata-giscus-${m.id}`, "", "**Comments.**", ":::", "");
    fs.writeFileSync(path.join(gen, "verification", `${m.id}.md`), lines.join("\n"));
  }

  // Contributors line per entry. In the cluster the controller computes it from git and
  // ships .lemmata/provenance.json with the source (the build sees no history); locally the
  // same is computed from this checkout's git log. Names only -- never email addresses.
  // Public address of the site (SITE_URL, set by the build Job; locally the production site).
  const siteUrl = (process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "");
  const prov = loadProvenance(manifests, commit);
  fs.mkdirSync(path.join(gen, "provenance"), { recursive: true });
  // The identifier line's "copy" control: a tiny anywidget module written by the tools,
  // not taken from the content repo, so contributors cannot change what it does.
  fs.writeFileSync(path.join(gen, "provenance", "ident.mjs"), IDENT_WIDGET);
  const day = (iso) => String(iso ?? "").slice(0, 10);
  for (const m of manifests) {
    const p = prov?.entries?.[m.id];
    // One header block per entry, visually set apart from the mathematics below (styled by
    // docs/_static/lemmata.css, class lemmata-header): identifier with copy controls, the
    // authors (linked to their author pages), versions, and the abstract.
    const ident = idents[m.id];
    const bib = bibtex(m, titleOf(m), p, { siteUrl, commit, checked: ["checked", "computation"].includes(statusOf(m)), computation: statusOf(m) === "computation", ident });
    const lines = [...withdrawnNotice(m), ":::::{div}", ":class: lemmata-header", ""];
    // The stable identifier and its permanent URL, the address to cite and link to: its own
    // row above the text lines (an empty block before it once added a stray gap).
    if (ident) {
      // Identifier as permanent link, "copy URL" and "copy BibTeX", rendered by a widget.
      // Without JavaScript the identifier is still the page's /abs/ address.
      // Path relative to the entry page that includes this file (docs/<id>/index.md):
      // MyST resolves widget modules from the including page, not from _generated/.
      lines.push("```{anywidget} ../_generated/provenance/ident.mjs",
        JSON.stringify({ ident: `lemmata:${ident}`, url: `${siteUrl}/abs/${ident}`, bibtex: bib }), "```", "");
    }
    lines.push(":::{div}", ":class: lemmata-provenance", "");
    if (!ident) lines.push("*Identifier assigned on publication.*  ");
    const who = people(m, p).map((c) => authorName(c, "../")).join(", ");
    if (!p && !m.contributors.length) lines.push("*Not yet committed.*");
    else lines.push(who + (p ? "  " : ""));
    // Versions, arXiv style: "v1 <first> · last <date linked to the commit>".
    if (p) {
      const last = forge ? `[${day(p.last.date)}](${forge.commit(p.last.commit)})` : day(p.last.date);
      lines.push(p.first.commit === p.last.commit ? `v1 ${day(p.first.date)}` : `v1 ${day(p.first.date)} · last ${last}`);
    }
    if (m.arxiv.length) {
      if (lines.at(-1) !== "" && !lines.at(-1).endsWith("  ")) lines[lines.length - 1] += "  ";
      lines.push(`Additional material: ${m.arxiv.map((a) => `[arXiv:${a}](https://arxiv.org/abs/${a})`).join(", ")}`);
    }
    lines.push(":::", "");
    // "Cite as": the BibTeX in a collapsed box. Hidden since the copy button replaced it.
    if (SHOW_CITE_BOX) lines.push("::::{dropdown} Cite as", "", "```bibtex", bib, "```", "::::", "");
    if (m.notes?.abstract) lines.push(":::{div}", ":class: lemmata-abstract", "", `**Abstract.** ${m.notes.abstract}`, ":::", "");
    lines.push(":::::", "");
    fs.writeFileSync(path.join(gen, "provenance", `${m.id}.md`), lines.join("\n"));
  }

  // Entries per subject (primary members: catalog and sidebar; cross-listed members: also
  // listed on the subject's page) and per topic, each sorted by title. Only subjects and
  // topics with entries get a page. Withdrawn entries are not listed (they keep their pages
  // and identifiers). Subjects with the most entries first (by primary entries, then
  // cross-listed ones), ties in arXiv's order -- for a small archive, alphabetical order put
  // a one-entry class above the one most entries share.
  const byTitle = (a, b) => titleOf(a).localeCompare(titleOf(b));
  const current = manifests.filter((m) => !m.notes?.withdrawn);
  const subjectOrder = Object.keys(tax.subjects);
  const nPrimary = (id) => current.filter((m) => m.subject === id).length, nCross = (id) => current.filter((m) => m.crossLists.includes(id)).length;
  const usedSubjects = subjectOrder.filter((id) => nPrimary(id) || nCross(id))
    .sort((a, b) => nPrimary(b) - nPrimary(a) || nCross(b) - nCross(a) || subjectOrder.indexOf(a) - subjectOrder.indexOf(b));
  const primary = new Map(usedSubjects.map((id) => [id, current.filter((m) => m.subject === id).sort(byTitle)]));
  const crossListed = new Map(usedSubjects.map((id) => [id, current.filter((m) => m.crossLists.includes(id)).sort(byTitle)]));
  const usedTopics = tax.topics.filter((t) => current.some((m) => m.topics.includes(t.id)));
  const subjectHref = (id, rel) => `${rel}${SUBJECT_DIR}/${subjectSlug(id)}/index.md`;
  const topicHref = (id, rel) => `${rel}${TOPIC_DIR}/${id}/index.md`;
  // "math.OC · cs.LG · topics: duality" under an entry's title, linked.
  const classLine = (m, rel) => [m.subject, ...m.crossLists].map((id) => `[${id}](${subjectHref(id, rel)})`).join(" · ") +
    (m.topics.length ? " · " + m.topics.map((t) => `[${esc(tax.topics.find((x) => x.id === t)?.title ?? t)}](${topicHref(t, rel)})`).join(", ") : "");
  // `rel` is the path prefix from the page that will contain the table to docs/: links in
  // generated text must be relative to the page MyST renders them on (an included file
  // resolves against the INCLUDING page; `../<id>/index.md` from _generated/ once
  // rendered as a raw href and 404'd).
  // Each entry's identifier after its title, outside the link so the space before it is not
  // underlined (a code span, styled by `table a.link + code` in lemmata.css); a local
  // preview has none and shows the title only.
  const table = (list, rel) => ["| Entry | Results | Status |", "|---|---|---|",
    ...list.map((m) => `| [${esc(titleOf(m))}](${entryHref(m, rel)})${idents[m.id] ? ` \`${idents[m.id]}\`` : ""} | ${m.exports.length} | ` +
      (statusOf(m) === "frozen" ? `checked with v${esc(frozen[m.id].lean_version ?? "?")}` + (entryComp(m) === "kernel" ? "" : ", mod. computation")
        : statusOf(m) === "computation" ? `[${COMPUTATION_WORDS.own.short}](${rel}checked.md#computation)` : statusOf(m)) + " |")];

  // "Contributing" paragraph of the landing page, with the repository address from the
  // build (SOURCE_WEB_URL) rather than written into docs/index.md, so moving the
  // repository needs no content change.
  const repo = sourceUrl?.replace(/\/+$/, "").replace(/\.git$/, "");
  const repoFile = (f) => forge?.blob("main", f) ?? null;
  const repoLabel = repo ? repo.replace(/^https?:\/\//, "") : null;
  const contributing = (repo
    ? `The archive is a Git repository, [${repoLabel}](${repo}). New entries and changes ` +
      `arrive by pull request; the [contribution guide](${repoFile("CONTRIBUTING.md")}) (and ` +
      `[AGENTS.md](${repoFile("AGENTS.md")}), the same procedure written for coding agents) explains every step. `
    : "New entries and changes arrive by pull request against the archive's Git repository. ") +
    `The site rebuilds itself from \`main\` within minutes; the [build status](${siteUrl}/_status) shows which ` +
    "version is live and, for a commit that was not published, why.\n";
  // With a bold label for the start page; without, for a page that has its own heading (About).
  fs.writeFileSync(path.join(gen, "contributing.md"), "**Contributing.** " + contributing);
  fs.writeFileSync(path.join(gen, "contributing-body.md"), contributing);

  // Landing page catalog (included from docs/index.md, so rel = ""): by primary subject, as
  // arXiv lists, then the topics.
  const cat = ["## Entries", ""];
  for (const id of usedSubjects) {
    if (!primary.get(id).length) continue;
    cat.push(`### [${esc(subjectTitle(tax, id))}](${subjectHref(id, "")})`, "");
    cat.push(...table(primary.get(id), ""), "");
  }
  if (usedTopics.length) cat.push("### Topics", "", usedTopics.map((t) =>
    `[${esc(t.title)}](${topicHref(t.id, "")}) (${current.filter((m) => m.topics.includes(t.id)).length})`).join(" · "), "");
  fs.writeFileSync(path.join(gen, "catalog.md"), cat.join("\n"));

  // One landing page per entry with an identifier, at /abs/<ident>/ (like arXiv's abstract
  // page): title, identifier with copy, contributors, dates, abstract, status, Cite as and
  // a link to the full entry at /html/<ident>. Built here so it is part of each release.
  const absPages = [];
  for (const m of manifests) {
    const ident = idents[m.id];
    if (!ident) continue;
    // Directory "2610-00001": MyST turns dots in a page path into hyphens, so the page is
    // built at abs/2610-00001/ whatever we name it. The public URL keeps the identifier's
    // dot (/abs/2610.00001); the supervisor maps one to the other.
    const p = prov?.entries?.[m.id], dir = path.join(absRoot, ident.replace(".", "-"));
    fs.mkdirSync(dir, { recursive: true });
    const status = statusOf(m), lean = report?.lean_version ? ` with Lean v${esc(report.lean_version)}` : "";
    // Header in the same style as the entry's, built here rather than included: the copy
    // widget's module path is relative to the page, and this page sits one level deeper
    // (docs/abs/<ident>/index.md) than an entry (docs/<id>/index.md).
    const who = people(m, p).map((c) => authorName(c, "../../")).join(", ");
    const last = p && (forge ? `[${day(p.last.date)}](${forge.commit(p.last.commit)})` : day(p.last.date));
    const dates = p ? (p.first.commit === p.last.commit ? `v1 ${day(p.first.date)}` : `v1 ${day(p.first.date)} · last ${last}`) : "";
    const bib = bibtex(m, titleOf(m), p, { siteUrl, commit, checked: ["checked", "computation"].includes(statusOf(m)), computation: statusOf(m) === "computation", ident });
    const L = ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(titleOf(m))}`, "---", "", ...withdrawnNotice(m),
      ":::::{div}", ":class: lemmata-header", "",
      "```{anywidget} ../../_generated/provenance/ident.mjs",
      JSON.stringify({ ident: `lemmata:${ident}`, url: `${siteUrl}/abs/${ident}`, bibtex: bib }), "```", "",
      ":::{div}", ":class: lemmata-provenance", "",
      ...(who ? [`${who}  `] : []), ...(dates ? [`${dates}  `] : []), licenseLine(m), ":::", "",
      // The page's main action, in the header where it is seen first (it sat below the
      // status and was missed, 2026-10-21). Relative, so it reads as an internal link.
      ":::{div}", ":class: lemmata-view-full", "",
      classLine(m, "../../") +
        (m.arxiv.length ? ` · ${m.arxiv.map((a) => `[arXiv:${a}](https://arxiv.org/abs/${a})`).join(", ")}` : "") +
        ` · **[View the full entry →](${entryHref(m, "../../")})**`, ":::", "",
      ...(SHOW_CITE_BOX ? ["::::{dropdown} Cite as", "", "```bibtex", bib, "```", "::::", ""] : []),
      ":::::", "",
      // Not "## Abstract": MyST lifts a section of that name above everything else on the
      // page. A bold label keeps the abstract below the header block, as on arXiv.
      "**Abstract.** " + m.notes.abstract, "",
      "## Status", "",
      status === "frozen" ? `**Last checked with Lean v${esc(frozen[m.id].lean_version ?? "?")} on ${String(frozen[m.id].checked_at ?? "").slice(0, 10)}**` +
        (entryComp(m) === "kernel" ? "" : ", modulo computation") +
        `${report?.lean_version && report.lean_version !== frozen[m.id].lean_version ? `; not re-checked with the current Lean v${esc(report.lean_version)}` : ""}. [What "checked" means](../../checked.md).`
      : status === "checked" ? `All formal results are **kernel-checked**${lean}. [What "checked" means](../../checked.md).`
      : status === "computation" ? `Formal results checked${lean}, **modulo computation**: some rely on facts evaluated by ` +
        "compiled code during the build rather than checked by Lean's kernel; the full entry lists them. " +
        "[What this means](../../checked.md#computation)."
        : status === "preview" ? "Not verified (local preview)." : "**Verification failed.**", ""];
    fs.writeFileSync(path.join(dir, "index.md"), L.join("\n"));
    absPages.push(`abs/${ident.replace(".", "-")}/index.md`);
  }

  // One page per subject at /s/<subject>/ (primary entries, then cross-listed ones) and per
  // topic at /t/<topic>/. Written into the build tree only.
  const page = (title, body) => ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(title)}`, "---", "", ...body].join("\n");
  for (const id of usedSubjects) {
    const dir = path.join(subjRoot, subjectSlug(id));
    fs.mkdirSync(dir, { recursive: true });
    const body = [`Entries whose primary subject is the arXiv class ${id} (${esc(tax.subjects[id])}), then entries cross-listed to it.`, ""];
    if (primary.get(id).length) body.push(...table(primary.get(id), "../../"), "");
    if (crossListed.get(id).length) body.push("## Also listed", "", ...table(crossListed.get(id), "../../"), "");
    fs.writeFileSync(path.join(dir, "index.md"), page(subjectTitle(tax, id), body));
  }
  for (const t of usedTopics) {
    const dir = path.join(topicRoot, t.id);
    fs.mkdirSync(dir, { recursive: true });
    const body = t.description ? [esc(t.description), ""] : [];
    body.push(...table(current.filter((m) => m.topics.includes(t.id)).sort(byTitle), "../../"), "");
    fs.writeFileSync(path.join(dir, "index.md"), page(`Topic: ${t.title}`, body));
  }
  // The old category pages (/c/<id>/) were linked from outside; each now points to the topic
  // that replaces it (topics.yml `replaces`), or to the start page. A MyST page cannot send
  // an HTTP redirect, so it says where the content moved, and the page script forwards.
  const oldPages = [];
  for (const old of ["logic", "order", "optimization", "extended-formulations", "multilinear-algebra", "coding-theory"]) {
    const t = tax.topics.find((x) => x.replaces.includes(old));
    const target = t ? `../../${TOPIC_DIR}/${t.id}/index.md` : "../../index.md";
    const dir = path.join(oldCatRoot, old);
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(dir, "index.md"), page("Moved", [":::{div}", `:class: lemmata-moved`, "",
      `Entries are now classified by arXiv subject and topic. This page moved to [${t ? esc(t.title) : "the list of entries"}](${target}).`, ":::", ""]));
    oldPages.push(`${OLD_CATEGORY_DIR}/${old}/index.md`);
  }

  // One page per author at /a/orcid-<ORCID iD>/ (see authorDir), listing every entry they are credited on (current
  // ones first, withdrawn ones after), and an index at /a/. Only contributors with an ORCID
  // iD get a page: the iD tells people with the same name apart, a name alone does not.
  // Keyed by the iD, so a page survives a change of spelling; it shows the most frequent
  // spelling. Written into the build tree only, like the category pages; not in the sidebar.
  const byAuthor = new Map();          // orcid -> {names: Map(name -> count), entries}
  for (const m of manifests) for (const c of people(m, prov?.entries?.[m.id])) {
    if (!c.orcid) continue;
    if (!byAuthor.has(c.orcid)) byAuthor.set(c.orcid, { names: new Map(), entries: [] });
    const a = byAuthor.get(c.orcid);
    a.names.set(c.name, (a.names.get(c.name) ?? 0) + 1);
    a.entries.push(m);
  }
  const shown = (a) => [...a.names].sort((x, y) => y[1] - x[1] || x[0].localeCompare(y[0]))[0][0];
  const authors = [...byAuthor].map(([orcid, a]) => ({ orcid, name: shown(a), entries: a.entries }))
    .sort((x, y) => x.name.localeCompare(y.name));
  const authorPages = [];
  for (const a of authors) {
    const dir = path.join(authorRoot, authorDir(a.orcid));
    fs.mkdirSync(dir, { recursive: true });
    const cur = a.entries.filter((m) => !m.notes?.withdrawn).sort(byTitle), gone = a.entries.filter((m) => m.notes?.withdrawn).sort(byTitle);
    const lines = ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(a.name)}`, "---", "",
      `ORCID iD: [${a.orcid}](https://orcid.org/${a.orcid})`, "",
      `Entries in the Lemmata Repository credited to ${esc(a.name)}.`, ""];
    if (cur.length) lines.push(...table(cur, "../../"), "");
    if (gone.length) lines.push("## Withdrawn", "", ...table(gone, "../../"), "");
    fs.writeFileSync(path.join(dir, "index.md"), lines.join("\n"));
    authorPages.push(`${AUTHOR_DIR}/${authorDir(a.orcid)}/index.md`);
  }
  fs.mkdirSync(authorRoot, { recursive: true });
  fs.writeFileSync(path.join(authorRoot, "index.md"), ["---", "numbering:", "  headings: false", "title: Authors", "---", "",
    "Contributors who have given an ORCID iD in their entry's `contribution.yml`. Others are named on their entries but have no page here.", "",
    ...(authors.length ? authors.map((a) => `- [${esc(a.name)}](${authorDir(a.orcid)}/index.md) (${a.entries.length})`) : ["*No contributor has given an ORCID iD yet.*"]), ""].join("\n"));
  authorPages.unshift(`${AUTHOR_DIR}/index.md`);

  // Effective MyST config: the authored one plus the generated TOC. Parsed and re-emitted
  // as YAML, never patched as text. Kept next to myst.yml so relative paths mean the same.
  // The sidebar groups entries under their category page; entry URLs come from their own
  // directories (/<id>/), so moving an entry to another category never breaks a link.
  const cfg = YAML.parse(fs.readFileSync(path.join(DOCS, "myst.yml"), "utf8"));
  if (cfg.extends) fail("docs/myst.yml: `extends` is not allowed");
  if (cfg.project?.plugins) fail("docs/myst.yml: build plugins are not allowed");
  // The sidebar shows only the site's own pages: a list of every entry and category would
  // grow without bound (2026-10-21). Entries are reached from the start page's catalog and
  // the category pages. They stay in the toc as ordinary pages under their category --
  // MyST does not number theorems or sections on `hidden` pages (measured) -- and the
  // sidebar hides them with CSS (.lemmata-toc-* in lemmata.css).
  const entryToc = (m) => m.pages.length === 1 ? { file: `${m.dir}/index.md` }
    : { file: `${m.dir}/index.md`, children: m.pages.slice(1).map((p) => ({ file: `${m.dir}/${p}` })) };
  cfg.project.toc = [{ file: "index.md" },
    ...usedSubjects.filter((id) => primary.get(id).length).map((id) => ({
      file: `${SUBJECT_DIR}/${subjectSlug(id)}/index.md`,
      children: primary.get(id).map(entryToc),
    })),
    // Subjects with only cross-listed entries, and the topics: pages, not sidebar groups.
    ...usedSubjects.filter((id) => !primary.get(id).length).map((id) => ({ file: `${SUBJECT_DIR}/${subjectSlug(id)}/index.md`, hidden: true })),
    ...usedTopics.map((t) => ({ file: `${TOPIC_DIR}/${t.id}/index.md`, hidden: true })),
    // Hand-written site pages, after the entries: what "checked" means, the changelog, and
    // the About page (who runs the site, who supports it), last in the sidebar.
    ...(fs.existsSync(path.join(DOCS, "checked.md")) ? [{ file: "checked.md" }] : []),
    ...(fs.existsSync(path.join(DOCS, "changelog.md")) ? [{ file: "changelog.md" }] : []),
    ...(fs.existsSync(path.join(DOCS, "about.md")) ? [{ file: "about.md" }] : []),
    // Withdrawn entries and the landing pages: built, not listed. (Hidden pages are not
    // numbered; a withdrawn entry keeps its content but loses theorem numbers, accepted.)
    ...manifests.filter((m) => m.notes?.withdrawn).flatMap((m) => m.pages.map((p) => ({ file: `${m.dir}/${p}`, hidden: true }))),
    ...absPages.map((f) => ({ file: f, hidden: true })),
    ...authorPages.map((f) => ({ file: f, hidden: true })),
    ...oldPages.map((f) => ({ file: f, hidden: true }))];
  if (process.env.LEMMATA_THEME) cfg.site.template = process.env.LEMMATA_THEME;
  fs.writeFileSync(path.join(DOCS, "myst.runtime.yml"),
    "# Generated by tools/lemmata.mjs prepare -- do not edit, not committed.\n" + YAML.stringify(cfg));
}

function scaffold(id, lean, subject) {
  // Refuse before writing anything: the umbrella update at the end would fail anyway.
  if (sparseCheckout()) { fail(`new: ${SPARSE_HELP}`); return; }
  if (!ID_RE.test(id) || RESERVED_DOCS.has(id)) { fail(`bad id ${id}`); return; }
  if (!LEAN_COMPONENT_RE.test(lean) || RESERVED_LEAN.has(lean)) { fail(`bad Lean name ${lean}`); return; }
  const tax = loadTaxonomy();
  if (!Object.hasOwn(tax.subjects, subject ?? "")) { fail(`subject ${JSON.stringify(subject)} is not an arXiv subject class (docs/subjects.json), e.g. math.OC, cs.CC, math.CO`); return; }
  const d = path.join(DOCS, id), l = path.join(LEAN, LIB, lean);
  if (fs.existsSync(d) || fs.existsSync(l)) { fail(`docs/${id} or lean/${LIB}/${lean} already exists`); return; }
  fs.mkdirSync(d, { recursive: true }); fs.mkdirSync(l, { recursive: true });
  const thm = `${LIB}.${lean}.main`;
  fs.writeFileSync(path.join(d, "contribution.yml"), YAML.stringify({ schema_version: 1, id,
    lean_namespace: `${LIB}.${lean}`, subject, pages: ["index.md"],
    exports: [{ name: thm, kind: "theorem", page: "index.md", label: `thm-${id}` }] }));
  // No `authors:` block: who contributed is shown from git, under the title.
  fs.writeFileSync(path.join(d, "index.md"), `---\ntitle: ${id}\n---\n\n` +
    "```{include} ../_generated/provenance/" + id + ".md\n```\n\n" +
    "```{prf:theorem} Statement\n:label: thm-" + id + "\n\nState the result here.\n```\n\n" +
    "```{prf:proof} of [](#thm-" + id + ")\n:nonumber:\n\nProve it here.\n```\n\n" +
    "```{literalinclude} ../../lean/" + LIB + "/" + lean + "/Main.lean\n:language: lean\n" +
    ":start-after: -- DOCS_BEGIN_MAIN\n:end-before: -- DOCS_END_MAIN\n```\n\n" +
    "```{include} ../_generated/verification/" + id + ".md\n```\n");
  fs.writeFileSync(path.join(l, "Main.lean"), `module\n\npublic import Mathlib.Logic.Function.Basic\n\npublic section\n\n` +
    `namespace ${LIB}.${lean}\n\n-- DOCS_BEGIN_MAIN\ntheorem main : True := trivial\n-- DOCS_END_MAIN\n\nend ${LIB}.${lean}\n`);
  checkUmbrella(true);
  console.log(`created docs/${id}/ and lean/${LIB}/${lean}/; umbrella updated`);
}

// The identifier line as a widget: the permanent link, and "copy" which puts the permanent
// URL on the clipboard (feedback "copied" for 1.5 s). Only model.get is used -- the static
// MyST theme has no kernel.
const IDENT_WIDGET = `const COPY = '<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="currentColor" aria-hidden="true" width="18" height="18"><path stroke-linecap="round" stroke-linejoin="round" d="M15.75 17.25v3.375c0 .621-.504 1.125-1.125 1.125h-9.75a1.125 1.125 0 0 1-1.125-1.125V7.875c0-.621.504-1.125 1.125-1.125H6.75a9.06 9.06 0 0 1 1.5.124m7.5 10.376h3.375c.621 0 1.125-.504 1.125-1.125V11.25c0-4.46-3.243-8.161-7.5-8.876a9.06 9.06 0 0 0-1.5-.124H9.375c-.621 0-1.125.504-1.125 1.125v3.5m7.5 10.375H9.375a1.125 1.125 0 0 1-1.125-1.125v-9.25m12 6.625v-1.875a3.375 3.375 0 0 0-3.375-3.375h-1.5a1.125 1.125 0 0 1-1.125-1.125v-1.5a3.375 3.375 0 0 0-3.375-3.375H9.75"/></svg>';
const DONE = '<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="currentColor" aria-hidden="true" width="18" height="18"><path stroke-linecap="round" stroke-linejoin="round" d="m4.5 12.75 6 6 9-13.5"/></svg>';
// A copy control: same icon as on code blocks, check mark after copying. Text label optional.
function copyButton(text, what, label) {
  const btn = document.createElement("button"); btn.type = "button"; btn.className = "lemmata-ident-copy";
  const show = (icon) => { btn.innerHTML = icon + (label ? "<span>" + label + "</span>" : ""); };
  show(COPY); btn.title = "Copy " + what; btn.setAttribute("aria-label", "Copy " + what);
  btn.addEventListener("click", async () => {
    try { await navigator.clipboard.writeText(text); }
    catch { const t = document.createElement("textarea"); t.value = text; document.body.append(t); t.select(); document.execCommand("copy"); t.remove(); }
    show(DONE); btn.setAttribute("aria-label", "Copied"); setTimeout(() => { show(COPY); btn.setAttribute("aria-label", "Copy " + what); }, 1500);
  });
  return btn;
}
function render({ model, el }) {
  const ident = model.get("ident"), url = model.get("url"), bib = model.get("bibtex");
  const box = document.createElement("span"); box.className = "lemmata-ident";
  const a = document.createElement("a"); a.href = url; a.className = "lemmata-ident-link";
  const b = document.createElement("strong"); b.textContent = ident; a.append(b);
  const btn = copyButton(url, "the permanent URL " + url, "URL");
  // "Cite": copies the entry's BibTeX, the same text as in the (hidden) Cite-as box.
  const cite = bib ? copyButton(bib, "the BibTeX entry", "BibTeX") : null;
  const css = document.createElement("style");
  css.textContent = ".lemmata-ident{display:inline-flex;align-items:center;gap:.3rem;font-size:.875rem}" +
    ".lemmata-ident-link{color:inherit}" +
    ".lemmata-ident-copy{display:inline-flex;align-items:center;padding:0;border:0;background:transparent;cursor:pointer;" +
    "color:var(--myst-color-link-underline,currentColor);opacity:.8}" +
    ".lemmata-ident-copy:hover{opacity:1;color:var(--myst-color-link-hover,currentColor)}" +
    ".lemmata-ident-copy span{margin-left:.2rem;font-size:.8rem}";
  box.append(a, btn); if (cite) box.append(cite); el.append(css, box);
}
export default { render };
`;

// ------------------------------------------------------------------------- site index

// Machine-readable views of the archive, written into the rendered site after `myst
// build`: llms.txt (the llms.txt convention: Markdown, one line per entry), lemmata.json
// (everything an agent needs to cite or link a result), and a sitemap.xml/robots.txt with
// the public addresses -- MyST's own pointed at its internal build server
// (http://localhost:3000). Entries are listed by their permanent /abs/ URL when they
// have an identifier, so links into the index never depend on directory names.
function siteIndex(manifests, tax, report, outDir, { commit, sourceUrl }) {
  const siteUrl = (process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "");
  fs.copyFileSync(new URL("./lemmata.png", import.meta.url), path.join(outDir, "lemmata.png"));
  const imageUrl = `${siteUrl}/lemmata.png`;
  const prov = loadProvenance(manifests, commit), idents = loadIdentifiers(commit);
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const topicTitle = new Map(tax.topics.map((t) => [t.id, t.title]));
  // Frozen entries are not in this build's report (they were not built); they keep the
  // results of their last check, exactly as the rendered pages show them.
  const frozen = loadFrozen();
  const comp = computationView(manifests, report);
  const entries = manifests.map((m) => {
    const ident = idents[m.id] ?? null, p = prov?.entries?.[m.id], fz = frozen[m.id];
    const url = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
    const old = new Map((fz?.results ?? []).map((x) => [x.name, x]));
    const exports = m.exports.map((e) => { const r = byName.get(e.name);
      const ok = fz ? old.get(e.name)?.status === "checked" : passed && r?.status === "checked";
      const c = fz ? comp.ofFrozen(m, old.get(e.name)) : comp.of(m, r);
      // verification: kernel-checked | kernel-checked-modulo-computation | checked-by-computation
      return { name: e.name, kind: e.kind, label: e.label, status: ok ? "checked" : "failed",
               verification: { kernel: "kernel-checked", inherited: "kernel-checked-modulo-computation", own: "checked-by-computation" }[c.status],
               computations: [...c.own, ...c.other.flatMap((o) => o.claims)].map((x) => ({ declaration: x.declaration ?? null,
                 entry: x.entry?.id ?? null, identifier: x.entry && idents[x.entry.id] ? `lemmata:${idents[x.entry.id]}` : null,
                 tactic: x.tactic ?? null, source_file: x.source_file ?? null, line: x.line ?? null, claim: x.claim ?? null })),
               axioms: r?.axioms ?? [], source_file: r?.source_file ?? null }; });
    const allOk = exports.every((x) => x.status === "checked");
    const anyComp = exports.some((x) => x.verification !== "kernel-checked");
    return {
      identifier: ident ? `lemmata:${ident}` : null, url, html_url: ident ? `${siteUrl}/html/${ident}` : `${siteUrl}/${m.dir}/`,
      title: titleOf(m),
      subject: m.subject, subject_name: tax.subjects[m.subject] ?? null, cross_lists: m.crossLists,
      topics: m.topics.map((t) => ({ id: t, title: topicTitle.get(t) ?? t })),
      contributors: people(m, p).map((c) => c.name),
      contributor_ids: people(m, p).map((c) => ({ name: c.name, orcid: c.orcid ?? null })),
      first_published: p?.first.date ?? null, last_changed: p?.last.date ?? null,
      // "withdrawn" says how the entry is listed; its formal results keep their own status.
      status: m.notes?.withdrawn ? "withdrawn" : fz ? (allOk ? "frozen" : "failed") : allOk ? (anyComp ? "checked-modulo-computation" : "checked") : "failed",
      native_computation: m.native,
      withdrawn: m.notes?.withdrawn ?? null,
      last_checked: fz ? { lean_version: fz.lean_version ?? null, checked_at: fz.checked_at ?? null, commit: fz.commit ?? null } : null,
      exports, arxiv: m.arxiv, license: m.license, license_url: LICENSES[m.license].url, ai_use: m.notes?.ai_use ?? null, acknowledgements: m.notes?.acknowledgements ?? null,
      bibtex: bibtex(m, titleOf(m), p, { siteUrl, commit, checked: !fz && allOk, computation: anyComp, ident }),
    };
  }).sort((a, b) => (a.identifier ?? "~").localeCompare(b.identifier ?? "~") || a.title.localeCompare(b.title));

  fs.writeFileSync(path.join(outDir, "lemmata.json"), JSON.stringify({
    schema_version: 1, site: siteUrl, source_commit: commit ?? null,
    checked_means: `formal statements compile, are accepted by Lean's kernel, and use no axioms beyond ${ALLOWED_AXIOMS.join(", ")}; the correspondence between prose and Lean statement is checked by human review`,
    computation_means: "a result marked kernel-checked-modulo-computation or checked-by-computation also relies on claims that a Bool expression evaluates to true, evaluated by compiled code during the build (native_decide and similar) and not checked by Lean's kernel or re-run by the archive; each such claim is listed under the result's computations, with its source line",
    entries,
  }, null, 2) + "\n");

  const line = (e) => `- [${e.title}](${e.url})${e.identifier ? ` (${e.identifier})` : ""}: ` +
    (e.status === "frozen" ? `last checked with Lean v${e.last_checked.lean_version ?? "?"} on ${String(e.last_checked.checked_at ?? "").slice(0, 10)}` +
        (e.exports.some((x) => x.verification !== "kernel-checked") ? ", modulo computation (some results rely on compiled computations, not kernel-checked)" : "")
      : e.status === "checked-modulo-computation" ? "checked modulo computation (some results rely on compiled computations, not kernel-checked)" : e.status) +
    `${e.contributors.length ? `; ${e.contributors.join(", ")}` : ""}${e.arxiv.length ? `; arXiv:${e.arxiv.join(", arXiv:")}` : ""}`;
  const md = ["# Lemmata Repository", "",
    "> An experimental mathematics repository: each entry is a result written as prose and formalized in Lean 4 on Mathlib. " +
    "\"kernel-checked\" means the formal statements compile and were accepted by Lean's kernel using only the standard " +
    `axioms (${siteUrl}/checked/). Whether the prose and the Lean statement say the same thing is checked by human review. ` +
    "\"checked modulo computation\" means some results also rely on facts evaluated by compiled code during the build " +
    `(native_decide), which the kernel does not check; ${siteUrl}/lemmata.json lists each such claim.`, "",
    `Each entry has an identifier lemmata:YYMM.NNNNN, a landing page ${siteUrl}/abs/YYMM.NNNNN (abstract, status, BibTeX) ` +
    `and the full entry at ${siteUrl}/html/YYMM.NNNNN. Cite the /abs/ URL. Machine-readable index with exported Lean ` +
    `declarations, axioms, licence and BibTeX: ${siteUrl}/lemmata.json. Entries are licensed CC BY 4.0 unless the ` +
    "entry says otherwise (CC BY-SA 4.0, CC0 1.0 or Apache 2.0).", ""];
  // By primary subject, most entries first, as on the start page.
  const order = Object.keys(tax.subjects), n = (id) => entries.filter((e) => e.subject === id && e.status !== "withdrawn").length;
  for (const id of order.filter(n).sort((a, b) => n(b) - n(a) || order.indexOf(a) - order.indexOf(b))) {
    const list = entries.filter((e) => e.subject === id && e.status !== "withdrawn");
    if (list.length) md.push(`## ${subjectTitle(tax, id)}`, "", ...list.map(line), "");
  }
  // Withdrawn entries stay reachable under their identifiers, so they are still indexed.
  const gone = entries.filter((e) => e.status === "withdrawn");
  if (gone.length) md.push("## Withdrawn", "", ...gone.map((e) => `- [${e.title}](${e.url})${e.identifier ? ` (${e.identifier})` : ""}: withdrawn`), "");
  // How to contribute, for agents reading this file. The repository address is the build's
  // SOURCE_WEB_URL (the cluster's one CONTENT_WEB setting), never written in here, so a
  // moved repository is reflected on the next build.
  const repo = sourceUrl?.replace(/\/+$/, "").replace(/\.git$/, "");
  if (repo) {
    const file = (f) => forgeLinks(repo)?.blob("main", f) ?? `${repo}/${f}`;
    md.push("## Contributing", "",
      `New entries and corrections are pull requests against \`main\` of ${repo}. An agent should follow ` +
      `AGENTS.md there: it is the complete procedure (scaffold, Lean and prose rules, local checks with ` +
      `tools/check.sh, the pull request, and how to confirm publication via ${siteUrl}/_status.json).`, "",
      `- [AGENTS.md](${file("AGENTS.md")}): step-by-step procedure for agents`,
      `- [CONTRIBUTING.md](${file("CONTRIBUTING.md")}): the same for people`,
      `- [Repository](${repo})`, "");
  }
  md.push("## Optional", "", `- [What "kernel-checked" means](${siteUrl}/checked/)`, `- [Changelog](${siteUrl}/changelog/)`, `- [About](${siteUrl}/about/)`,
    `- [Build status](${siteUrl}/_status)`, "");
  fs.writeFileSync(path.join(outDir, "llms.txt"), md.join("\n"));

  const xmlEsc = (u) => u.replace(/&/g, "&amp;").replace(/</g, "&lt;");
  const usedSubjects = Object.keys(tax.subjects).filter((id) => entries.some((e) => e.subject === id || e.cross_lists.includes(id)));
  const usedTopics = tax.topics.filter((t) => entries.some((e) => e.topics.some((x) => x.id === t.id)));
  const urls = [`${siteUrl}/`, ...usedSubjects.map((id) => `${siteUrl}/${SUBJECT_DIR}/${subjectSlug(id)}/`),
    ...usedTopics.map((t) => `${siteUrl}/${TOPIC_DIR}/${t.id}/`),
    ...entries.map((e) => e.url), ...entries.filter((e) => e.identifier).map((e) => e.url.replace("/abs/", "/html/")),
    `${siteUrl}/checked/`, `${siteUrl}/changelog/`, `${siteUrl}/about/`];
  fs.writeFileSync(path.join(outDir, "sitemap.xml"), ['<?xml version="1.0" encoding="UTF-8"?>',
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ...urls.map((u) => `  <url><loc>${xmlEsc(u)}</loc></url>`), "</urlset>", ""].join("\n"));
  // Pages built for the site root are served at their stable URLs; /_releases/<id>/ are
  // copies for debugging that go stale, so keep crawlers off them. A release built with
  // the prefix lives only there, so it is left crawlable.
  fs.writeFileSync(path.join(outDir, "robots.txt"), ["User-agent: *", "Allow: /",
    ...(process.env.BASE_URL ? [] : ["Disallow: /_releases/"]),
    `Sitemap: ${siteUrl}/sitemap.xml`, ""].join("\n"));
  dedupeTitles(outDir);
  injectEnhancements(outDir);           // before canonical(), which annotates its tag
  pageMetadata(path.join(outDir, "index.html"), { imageUrl });
  // One preferred address per entry for search engines and link previews: the entry is
  // reachable at /<dir>/ and /html/<ident>, its landing page at /abs/<ident>/.
  for (const m of manifests) {
    const file = path.join(outDir, m.dir, "index.html"), title = titleOf(m), abstract = m.notes.abstract;
    pageMetadata(file, { title, description: abstract, imageUrl });
    const ident = idents[m.id];
    if (!ident) continue;
    canonical(file, `${siteUrl}/html/${ident}`);
    const landing = path.join(outDir, "abs", ident.replace(".", "-"), "index.html");
    pageMetadata(landing, { title, description: abstract, imageUrl });
    canonical(landing, `${siteUrl}/abs/${ident}`);
  }
}

// Link previews read the served HTML without JavaScript. Entries use their own title
// and abstract; the home page keeps the site's title and description.
function pageMetadata(file, { title, description, imageUrl }) {
  if (!fs.existsSync(file)) return;
  const html = fs.readFileSync(file, "utf8");
  const escape = (s) => s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const fields = [
    ["property", "og:image", imageUrl],
    ["property", "og:image:type", "image/png"],
    ["property", "og:image:width", "512"],
    ["property", "og:image:height", "512"],
    ["property", "og:image:alt", "Lemmata"],
    ["name", "twitter:card", "summary"],
    ["name", "twitter:image", imageUrl],
    ["name", "twitter:image:alt", "Lemmata"],
  ];
  if (title !== undefined)
    fields.push(["property", "og:title", title], ["name", "twitter:title", title]);
  if (description !== undefined) {
    const text = description.replace(/\s+/g, " ").trim();
    fields.push(["name", "description", text], ["property", "og:description", text], ["name", "twitter:description", text]);
  }
  const out = html.replace(/<head\b[^>]*>[\s\S]*?<\/head>/i, (head) => {
    if (title !== undefined)
      head = head.replace(/<title>[\s\S]*?<\/title>/i, () => `<title>${escape(title)}</title>`);
    for (const [attr, key, value] of fields) {
      const re = new RegExp(`<meta\\b(?=[^>]*\\b${attr}\\s*=\\s*["']${key}["'])[^>]*>`, "i");
      const tag = `<meta ${attr}="${key}" content="${escape(value)}"/>`;
      head = re.test(head) ? head.replace(re, () => tag) : head.replace(/<\/head>/i, () => tag + "</head>");
    }
    return head;
  });
  if (out !== html) fs.writeFileSync(file, out);
}

// The theme titles every page "<page title> - <site title>". On the start page both are
// the site title, so tabs and link previews (Slack, og:title) read "X - X". Collapse that
// one case to "X"; pageMetadata handles the entry pages separately.
// <link rel="canonical"> and og:url in a page's <head> (React leaves the head alone).
function canonical(file, url) {
  if (!fs.existsSync(file)) return;
  let html = fs.readFileSync(file, "utf8");
  // Each part on its own, so a page that already has one of them still gets the others.
  if (!html.includes('rel="canonical"'))
    html = html.replace("</head>", `<link rel="canonical" href="${url}"/><meta property="og:url" content="${url}"/></head>`);
  // The page script restores the link after React re-renders <head>; it reads the URL from
  // its own <script> tag, which sits outside what React hydrates. An element added inside
  // the page body would be a hydration mismatch (React #418).
  if (!html.includes("data-lemmata-canonical="))
    html = html.replace("<script data-lemmata-enhance>", `<script data-lemmata-enhance data-lemmata-canonical="${url}">`);
  fs.writeFileSync(file, html);
}

function dedupeTitles(siteDir) {
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    const out = html.replace(/(<title>|<meta property="og:title" content=")([^<"]+) - \2(<\/title>|")/g, "$1$2$3");
    if (out !== html) fs.writeFileSync(f, out);
  }
}

// ------------------------------------------------------------------- page enhancements

// The theme renders pages with React, which replaces the static HTML on load, so edits to
// the built HTML are discarded (measured 2026-10-21). These are applied in the browser
// instead, by one small script added to every page after the build. Each step is
// idempotent and re-run when React re-renders.
//   - proofs: "Proof (of Theorem 1)" -> "Proof of Theorem 1"; clicking a proof's header
//     folds it (proofs start open)
//   - results: a [↓] after the heading of a result whose proof is not directly below it
//   - Lean code (MyST code blocks under an entry): collapsed behind a bar, copy button kept
//   - Lean next to each result: the per-result boxes rendered at the end of the page are
//     moved directly under the theorem or definition they belong to
const ENHANCE_SCRIPT = `(function(){
function proofs(){
  document.querySelectorAll(".myst-proof.border-myst-proof").forEach(function(box){
    var title=box.querySelector(".myst-proof-title"), head=box.querySelector(".myst-proof-header"), body=box.querySelector(".myst-proof-body");
    if(!title||!head||!body) return;
    if(!title.dataset.lemmata){
      title.dataset.lemmata="1";
      // "Proof (of X)" -> "Proof of X": the theme wraps any proof title in "(" and ")" text
      // nodes. Only text nodes are edited, so the links React rendered stay its own.
      var texts=[]; title.childNodes.forEach(function(n){ if(n.nodeType===3) texts.push(n); });
      var open=texts.find(function(n){ return /\\(\\s*$/.test(n.textContent); });
      var next=open&&open.nextSibling; while(next&&next.nodeType===8) next=next.nextSibling;   // skip React's comment markers
      if(open && next && /^\\s*of\\b/.test(next.textContent||"")){
        open.textContent=open.textContent.replace(/\\(\\s*$/,"");
        var close=texts.reverse().find(function(n){ return /^\\s*\\)\\s*$/.test(n.textContent); });
        if(close) close.textContent="";
      }
    }
    if(!head.dataset.lemmata){
      head.dataset.lemmata="1"; head.classList.add("lemmata-fold"); head.setAttribute("role","button"); head.tabIndex=0;
      head.title="Fold or unfold the proof";
      var toggle=function(e){ if(e.target.closest("a")) return; box.classList.toggle("lemmata-folded"); };
      head.addEventListener("click",toggle);
      head.addEventListener("keydown",function(e){ if(e.key==="Enter"||e.key===" "){ e.preventDefault(); toggle(e); } });
    }
  });
}
// The theme's router takes over clicks on links it did not render and loads the page's
// data for the address shown -- /html/<ident>, which has none (it is a redirect), so the
// page crashed ("reading 'frontmatter'"). Scroll ourselves and set the hash without it.
// replaceState, not pushState: Back to an entry we pushed hands the router the same
// address and crashed it the same way. The theme's own cross-references add no history
// entry either, so Back leaves the page in both cases.
function jump(e){
  var box=document.getElementById(this.getAttribute("href").slice(1)); if(!box) return;
  e.preventDefault(); e.stopPropagation();
  box.scrollIntoView({block:"start"});
  try{ history.replaceState(history.state,"",location.pathname+location.search+"#"+box.id); }catch(err){}
}
function arrow(cls,id,text,title){
  var a=document.createElement("a"); a.className="lemmata-jump "+cls; a.href="#"+id; a.textContent=text;
  a.title=title; a.addEventListener("click",jump); return a;
}
function proofLinks(){
  // For each proof that names results, add [↓] to those results' headings and [↑] back to
  // the result in the proof's own heading, unless the proof directly follows the result.
  document.querySelectorAll(".myst-proof.border-myst-proof").forEach(function(box, i){
    if(!box.id) box.id="lemmata-proof-"+(i+1);
    box.querySelectorAll(".myst-proof-title a[href^='#']").forEach(function(a){
      var res=document.getElementById(a.getAttribute("href").slice(1));
      if(!res||res===box) return;
      var head=res.querySelector(".myst-proof-title"); if(!head||head.querySelector(".lemmata-to-proof[href='#"+box.id+"']")) return;
      if(res.nextElementSibling===box) return;
      head.append(" ",arrow("lemmata-to-proof",box.id,"[↓]","Go to the proof"));
      var own=box.querySelector(".myst-proof-title");
      if(own&&!own.querySelector(".lemmata-to-result[href='#"+res.id+"']"))
        own.append(" ",arrow("lemmata-to-result",res.id,"[↑]","Back to the statement"));
    });
  });
}
function lean(){
  // The Lean is a literalinclude of a .lean file, shown with its filename in the block's
  // header (MyST highlights it as plain text, so there is no language class to match).
  document.querySelectorAll("article .myst-code").forEach(function(code){
    if(code.dataset.lemmata) return;
    var head=code.firstElementChild; if(!head||!/\\.lean\\s*$/.test(head.textContent||"")) return;
    code.dataset.lemmata="1";
    var d=document.createElement("details"); d.className="lemmata-lean";
    var s=document.createElement("summary"); var lines=(code.textContent.match(/\\n/g)||[]).length+1;
    s.textContent="Lean source: "+head.textContent.trim()+" ("+lines+" lines)"; d.append(s);
    code.parentNode.insertBefore(d,code); d.append(code);
  });
}
function leanNextToResults(){
  // Move each per-result Lean box (rendered at the end of the page) under its result.
  document.querySelectorAll(".lemmata-lean-boxes .lemmata-lean-for").forEach(function(box){
    var m=(box.className.match(/lemmata-for-(\\S+)/)||[])[1]; if(!m) return;
    var res=document.getElementById(m); if(!res||!res.parentNode) return;
    box.classList.add("lemmata-placed");
    res.parentNode.insertBefore(box,res.nextSibling);
    // The Lean line itself opens the statement: its "Statement in Lean" toggle is hidden
    // (CSS), and a click on the line (not on its links) toggles that dropdown.
    var line=box.querySelector(":scope > p"), det=box.querySelector("details");
    if(line&&det&&!line.dataset.lemmata){
      line.dataset.lemmata="1"; line.classList.add("lemmata-lean-line"); line.setAttribute("role","button"); line.tabIndex=0;
      line.title="Show or hide the Lean statement";
      var flip=function(e){ if(e.target.closest("a")) return; det.open=!det.open; line.classList.toggle("lemmata-open",det.open); };
      line.addEventListener("click",flip);
      line.addEventListener("keydown",function(e){ if(e.key==="Enter"||e.key===" "){ e.preventDefault(); flip(e); } });
    }
  });
}
// Right-hand contents: the theme highlights a heading only while it is in a narrow band at
// the top of the window, so inside a long section nothing was highlighted (104 of 122
// scroll positions, measured). Instead: the section being read is the last heading above
// a third of the window; its contents item gets lemmata-current, and CSS shows only that.
function outline(){
  var items=[].slice.call(document.querySelectorAll(".myst-outline-item"));
  if(!items.length) return;
  var heads=[].slice.call(document.querySelectorAll("article h2[id], article h3[id], article h4[id]"));
  var cur=null, line=window.innerHeight/3;
  for(var i=0;i<heads.length;i++){ if(heads[i].getBoundingClientRect().top<line) cur=heads[i].id; else break; }
  // At the very bottom, the last heading is the one being read even if it never got high.
  if(window.innerHeight+window.scrollY>=document.documentElement.scrollHeight-2 && heads.length) cur=heads[heads.length-1].id;
  items.forEach(function(li){
    var a=li.querySelector("a[href^='#']"), on=!!(a&&cur&&a.getAttribute("href")==="#"+cur);
    if(on!==li.classList.contains("lemmata-current")) li.classList.toggle("lemmata-current",on);
    // Section numbers: the theme numbers the headings but not the contents list. Copy the
    // heading's number (the text before its title) in front of the item.
    if(a&&!a.querySelector(".lemmata-secnum")){
      var h=document.getElementById(a.getAttribute("href").slice(1)), n=h&&h.querySelector("span");
      var num=n&&/^\\s*[\\d.]+\\s*$/.test(n.textContent)?n.textContent.trim():null;
      if(num){ var sp=document.createElement("span"); sp.className="lemmata-secnum"; sp.textContent=num+" "; a.insertBefore(sp,a.firstChild); }
    }
  });
  document.documentElement.classList.add("lemmata-outline");
}
// Copying text with formulas gives their TeX ($z_x\\in P$), not the rendered glyphs, as
// KaTeX's copy-tex add-on does: every formula carries its source in an annotation.
document.addEventListener("copy",function(e){
  var sel=window.getSelection(); if(!sel||sel.isCollapsed||!e.clipboardData) return;
  var frag=sel.getRangeAt(0).cloneContents();
  if(!frag.querySelector(".katex-mathml, .katex")) return;
  // Outermost formulas only (a .katex-display wraps a .katex). The ancestor test stops at
  // the fragment: when the selection starts inside a display, its wrapper is not copied.
  var all=[].slice.call(frag.querySelectorAll(".katex-display, .katex"));
  all.filter(function(k){ for(var a=k.parentElement; a; a=a.parentElement) if(all.indexOf(a)>=0) return false; return true; })
  .forEach(function(k){
    var ann=k.querySelector("annotation[encoding='application/x-tex']"); if(!ann) return;
    var tex=ann.textContent.trim(), m=k.querySelector("math");
    // Display math: the .katex-display wrapper, or -- when the selection starts inside it --
    // the MathML's display="block", which KaTeX always writes.
    var display=k.classList.contains("katex-display")||(m&&m.getAttribute("display")==="block");
    var dl=display?"$"+"$":"$"; k.replaceWith(document.createTextNode(dl+tex+dl));
  });
  e.clipboardData.setData("text/plain",frag.textContent);
  e.preventDefault();
},true);
var ticking=false;
window.addEventListener("scroll",function(){ if(!ticking){ ticking=true; requestAnimationFrame(function(){ ticking=false; step("contents",outline); }); } },{passive:true});
window.addEventListener("resize",function(){ step("contents",outline); });
// The canonical URL is written into the served HTML (what crawlers and link previews read);
// React re-renders the <head> on load and drops it, so put it back for the live page too.
var CANON=(document.querySelector("script[data-lemmata-canonical]")||{dataset:{}}).dataset.lemmataCanonical||null;   // see canonical() in lemmata.mjs
function canon(){ if(CANON&&!document.querySelector("link[rel=canonical]")){ var l=document.createElement("link"); l.rel="canonical"; l.href=CANON; document.head.append(l); } }
// On an entry page, show its identifier address (/html/<ident>) in the address bar, so that
// is what readers copy and share; the page itself is served at its directory, which the
// theme's router needs. Same document, so nothing reloads; anchors are kept.
function idAddress(){
  if(!CANON||!/\\/html\\/\\d{4}\\.\\d{5}$/.test(CANON)) return;
  var u=new URL(CANON), here=location.pathname.replace(/\\/+$/,"");
  if(here===u.pathname) return;
  // Only from the entry's own directory page, never from a page the router moved to.
  if(!document.querySelector(".lemmata-lean-for, .lemmata-header")) return;
  try{ history.replaceState(history.state,"",u.pathname+location.search+location.hash); }catch(e){}
}
// Comments (giscus): load into the entry's placeholder once; theme follows the site's.
var GISCUS=${GISCUS ? JSON.stringify(GISCUS) : "null"};
function comments(){
  if(!GISCUS) return;
  var box=document.querySelector(".lemmata-giscus"); if(!box||box.dataset.loaded) return;
  var term=(box.className.match(/lemmata-giscus-(\\S+)/)||[])[1]; if(!term) return;
  box.dataset.loaded="1";
  var dark=document.documentElement.classList.contains("dark");
  var s=document.createElement("script"); s.src="https://giscus.app/client.js"; s.async=true; s.crossOrigin="anonymous";
  var a={repo:GISCUS.repo,"repo-id":GISCUS.repoId,category:GISCUS.category,"category-id":GISCUS.categoryId,
    mapping:"specific",term:term,"reactions-enabled":"1","emit-metadata":"0","input-position":"top",
    theme:dark?"dark":"light",lang:"en",loading:"lazy"};
  for(var k in a) s.setAttribute("data-"+k,a[k]);
  box.append(s);
}
// Each step on its own: one that fails must not skip the others (they all ran under one
// try before, so the first error silently dropped the rest; review, 2026-10-22). A failure
// is reported once per step in the console.
var reported={};
// A moved page (an old /c/<category>/ address) forwards to where its content is now.
function moved(){
  var box=document.querySelector(".lemmata-moved a[href]"); if(!box||moved.done) return;
  moved.done=1; location.replace(box.href);
}
function step(name,fn){ try{ fn(); }catch(e){ if(!reported[name]){ reported[name]=1; console.warn("[lemmata] "+name+" failed:",e); } } }
function run(){
  step("canonical",canon); step("lean boxes",leanNextToResults); step("proofs",proofs); step("proof links",proofLinks);
  step("moved",moved); step("lean source",lean); step("contents",outline); step("comments",comments);
}
// Only after React has hydrated: changing the DOM before that is a hydration mismatch
// (React error #418), after which React re-renders and drops the changes. Then re-apply
// whenever React re-renders.
function start(){
  setTimeout(function(){
    run(); idAddress();
    var t=null; new MutationObserver(function(){ clearTimeout(t); t=setTimeout(run,50); }).observe(document.body,{childList:true,subtree:true});
  },300);
}
if(document.readyState==="complete") start(); else window.addEventListener("load",start);
})();`;
function injectEnhancements(siteDir) {
  const tag = `<script data-lemmata-enhance>${ENHANCE_SCRIPT}</script>`;
  let n = 0;
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    if (html.includes("data-lemmata-enhance") || !html.includes("</body>")) continue;
    fs.writeFileSync(f, html.replace("</body>", tag + "</body>")); n++;
  }
  return n;
}

// ------------------------------------------------------------------------- analytics

// Privacy-friendly analytics (Plausible), added to every page's <head> after the build.
// The theme's own analytics_plausible option is hard-wired to plausible.io, so it cannot
// point at a self-hosted instance. The script URL comes from the cluster (ANALYTICS_SCRIPT,
// a trusted setting); without it nothing is added, so local builds and previews are not
// tracked. The URL must be https and is checked before it is written into HTML.
function injectAnalytics(siteDir, scriptUrl) {
  if (!scriptUrl) return 0;
  let u; try { u = new URL(scriptUrl); } catch { fail(`ANALYTICS_SCRIPT is not a URL: ${scriptUrl}`); return 0; }
  if (u.protocol !== "https:" || /["'<>\s]/.test(scriptUrl)) { fail(`ANALYTICS_SCRIPT must be a plain https URL`); return 0; }
  // transformRequest strips a release prefix (/_releases/<id>) from the page URL and the
  // referrer, so statistics are per stable page (/implication-composition), not split anew
  // with every release. A no-op for releases built for the site root (pins.json
  // release_prefix: false), whose pages are already at their stable URLs.
  const strip = "function(u){return u&&u.replace(/\\/_releases\\/[^/]+(?=\\/|$)/,'')}";
  const snippet = `<script async src="${scriptUrl}"></script>` +
    `<script>window.plausible=window.plausible||function(){(plausible.q=plausible.q||[]).push(arguments)},` +
    `plausible.init=plausible.init||function(i){plausible.o=i||{}};` +
    `plausible.init({transformRequest:function(e){var s=${strip};e.u=s(e.u);if(e.r)e.r=s(e.r);return e}})</script>`;
  let n = 0;
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    if (html.includes(scriptUrl) || !html.includes("</head>")) continue;
    fs.writeFileSync(f, html.replace("</head>", snippet + "</head>"));
    n++;
  }
  return n;
}

// ------------------------------------------------------------------------------- main

const [cmd, ...args] = process.argv.slice(2);
const flag = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
switch (cmd) {
  case "validate": {
    const ms = loadManifests(); checkSnippets(ms); checkDois(ms); checkUmbrella(false); checkLeanSources(ms);
    if (fs.existsSync(path.join(ROOT, ".publication"))) fail(".publication/ must not be committed");
    // .lemmata/ is where the cluster puts data it adds to the source (provenance.json).
    // Locally it must not exist; in a build (LEMMATA_BUILD=1) it is expected, and the
    // controller has already refused any commit that contained it.
    if (!process.env.LEMMATA_BUILD && fs.existsSync(path.join(ROOT, ".lemmata")))
      fail(".lemmata/ is reserved for data the cluster adds; it must not be committed");
    finish(`ok: ${ms.length} contribution(s), ${ms.reduce((n, m) => n + m.exports.length, 0)} export(s)`);
    break;
  }
  case "umbrella": checkUmbrella(args.includes("--write")); finish(args.includes("--write") ? "umbrella written" : "umbrella up to date"); break;
  case "request": {
    const ms = loadManifests(); finish();
    fs.writeFileSync(args[0], JSON.stringify(verifierRequest(ms), null, 2) + "\n"); break;
  }
  case "prepare": {
    const tax = loadTaxonomy(); const ms = loadManifests(tax); finish();
    const report = args[0] && args[0] !== "--preview" ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    prepare(ms, tax, report, { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish("prepared docs/_generated and docs/myst.runtime.yml"); break;
  }
  case "new": scaffold(args[0], args[1], args[2]); finish(); break;
  case "doi": { const ms = loadManifests(); finish(); await fetchDois(ms, args); finish(); break; }
  case "site-index": {            // after myst build: llms.txt, lemmata.json, sitemap, robots
    const tax = loadTaxonomy(); const ms = loadManifests(tax); finish();
    const report = args[0] ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    siteIndex(ms, tax, report, args[1], { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish(`wrote llms.txt, lemmata.json, sitemap.xml, robots.txt to ${args[1]}`); break;
  }
  case "enhance": {               // after the build: proof titles, folding, Lean collapsing
    finish(`page enhancements added to ${injectEnhancements(args[0])} page(s)`); break;
  }
  case "analytics": {             // after the build: add the analytics snippet to every page
    const n = injectAnalytics(args[0], process.env.ANALYTICS_SCRIPT ?? "");
    finish(process.env.ANALYTICS_SCRIPT ? `analytics added to ${n} page(s)` : "no ANALYTICS_SCRIPT: no analytics"); break;
  }
  case "provenance": {            // what the controller ships for HEAD, from local git
    const ms = loadManifests(); finish();
    process.stdout.write(JSON.stringify(loadProvenance(ms, null), null, 2) + "\n"); break;
  }
  default:
    console.error("usage: lemmata.mjs validate | umbrella [--write] | request <out> | prepare <report.json>|--preview [--commit SHA] [--source-url URL] | new <id> <LeanName> <subject>");
    process.exit(2);
}
