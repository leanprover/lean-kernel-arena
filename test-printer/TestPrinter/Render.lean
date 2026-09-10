import TestPrinter.Types
import SubVerso.Highlighting.Highlighted
import MD4Lean

namespace TestPrinter

open SubVerso.Highlighting

private def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;"
  |>.replace "<" "&lt;"
  |>.replace ">" "&gt;"
  |>.replace "\"" "&quot;"
  |>.replace "'" "&#39;"

private def nameToId (n : Lean.Name) : String :=
  "decl-" ++ toString n |>.replace "." "-" |>.replace " " "_"

/-- Strip `tutorial/` prefix from test names. -/
private def stripPrefix (s : String) : String :=
  if s.startsWith "tutorial/" then (s.drop 9).toString else s

/-- Render markdown to HTML using md4lean (cmark bindings). -/
private def renderMarkdown (s : String) : String :=
  MD4Lean.renderHtml s |>.getD (escapeHtml s)

/-! ## Highlighted → HTML rendering -/

/-- CSS class for a token kind (matches Verso naming). -/
private def tokenKindClass : Token.Kind → String
  | .var .. => "var"
  | .str .. => "literal string"
  | .sort .. => "sort"
  | .const .. => "const"
  | .option .. => "option"
  | .docComment => "doc-comment"
  | .keyword .. => "keyword"
  | .anonCtor .. => "unknown"
  | .unknown => "unknown"
  | .withType .. => "typed"
  | .levelConst .. => "level-const"
  | .levelVar .. => "level-var"
  | .levelOp .. => "level-op"
  | .moduleName .. => "module-name"

/-- Data-binding attribute value for binding highlighting on hover. -/
private def tokenKindData : Token.Kind → String
  | .const n _ _ _ | .anonCtor n _ _ => "const-" ++ toString n
  | .var ⟨v⟩ _ => "var-" ++ toString v
  | .option n _ _ => "option-" ++ toString n
  | .keyword _ (some occ) _ => "kw-occ-" ++ toString occ
  | .sort (some d) => s!"sort-{hash d}"
  | .levelVar x => s!"level-var-{x}"
  | .levelConst i => s!"level-const-{i}"
  | .levelOp op => s!"level-op-{op}"
  | .moduleName m => s!"module-name-{m}"
  | _ => ""

/-- Render a Highlighted value to an HTML string.
    If `declOrigin` is provided, `.const` tokens whose name appears in the map
    are wrapped in an `<a>` link pointing to the declaration's anchor. -/
partial def highlightedToHtml (hl : Highlighted)
    (declOrigin : Std.HashMap Lean.Name String := {}) : String :=
  match hl with
  | .token t =>
    let cls := tokenKindClass t.kind ++ " token"
    let binding := tokenKindData t.kind
    let bindAttr := if binding.isEmpty then "" else s!" data-binding=\"{escapeHtml binding}\""
    let sigAttr := match t.kind with
      | .const _ sig _ _ => if sig.isEmpty then "" else s!" data-sig=\"{escapeHtml sig}\""
      | .var _ ty => if ty.isEmpty then "" else s!" data-sig=\"{escapeHtml ty}\""
      | .sort (some doc) => s!" data-sig=\"{escapeHtml doc}\""
      | _ => ""
    let spanHtml := s!"<span class=\"{cls}\"{bindAttr}{sigAttr}>{escapeHtml t.content}</span>"
    -- Wrap const tokens in a link if the constant has a definition on the page
    match t.kind with
    | .const name _ _ isDef =>
      if !isDef && declOrigin.contains name then
        let target := nameToId name
        s!"<a href=\"#{escapeHtml target}\" class=\"const-ref\">{spanHtml}</a>"
      else spanHtml
    | _ => spanHtml
  | .text s => escapeHtml s
  | .seq hs => String.join (hs.toList.map (highlightedToHtml · declOrigin))
  | .span _ h => highlightedToHtml h declOrigin
  | .unparsed s => escapeHtml s
  | .tactics _ _ _ h => highlightedToHtml h declOrigin
  | .point _ _ => ""

/-- Render a PrettyDecl as highlighted HTML. -/
private def renderPrettyDecl (decl : PrettyDecl)
    (declOrigin : Std.HashMap Lean.Name String := {}) : String := Id.run do
  let anchorId := nameToId decl.name
  let hl (h : Highlighted) := highlightedToHtml h declOrigin
  -- Level params
  let lvlHtml := if decl.levelParams.isEmpty then ""
    else
      let params := decl.levelParams.map fun p =>
        let h : Highlighted := .token ⟨.levelVar p, toString p⟩
        hl h
      ".{" ++ ", ".intercalate params ++ "}"
  -- Build highlighted declaration line
  let kindH := hl (.token ⟨.keyword none none none, decl.kind⟩)
  let nameH := hl (.token ⟨.const decl.name "" none true, toString decl.name⟩)
  let paramsH := match decl.paramsPP with
    | some p => " " ++ hl p
    | none => ""
  let colonTypeH := hl decl.colonTypePP
  let mut s := s!"{kindH} <span id=\"{anchorId}\">{nameH}</span>{lvlHtml}{paramsH}{colonTypeH}"
  match decl.valuePP with
  | some val =>
    -- Add 2-space indent after every newline so value body stays indented
    let valHtml := (hl val).replace "\n" "\n  "
    s := s ++ s!" :=\n  {valHtml}"
  | none => pure ()
  return s

private def renderSharedDecls (sharedDecls : Array Lean.Name)
    (declOrigin : Std.HashMap Lean.Name String) : String :=
  if sharedDecls.isEmpty then ""
  else
    let links := sharedDecls.toList.map fun n =>
      let nameStr := toString n
      let target := declOrigin[n]?.getD (nameToId n)
      s!"<a href=\"#{target}\" class=\"const-ref\"><code>{escapeHtml nameStr}</code></a>"
    s!"<p class=\"shared\">Includes: {", ".intercalate links}</p>\n"

private def renderTest (test : ResolvedTest) (decls : Array PrettyDecl)
    (declOrigin : Std.HashMap Lean.Name String) : String := Id.run do
  let testClass := if test.parsed.file.isGood then "good" else "bad"
  -- 👍 / ✋
  let marker := if test.parsed.file.isGood then "&#x1F44D;" else "&#x270B;"
  let displayName := stripPrefix test.parsed.stats.name
  let testId := "test-" ++ test.parsed.file.baseName
  let mut s := s!"<section class=\"test {testClass}\" id=\"{testId}\">\n"
  s := s ++ s!"<h2><span class=\"marker\">{marker}</span> {escapeHtml displayName}</h2>\n"
  s := s ++ s!"<div class=\"description\">{renderMarkdown test.parsed.info.description}</div>\n"
  s := s ++ renderSharedDecls test.sharedDecls declOrigin
  if decls.isEmpty then
    s := s ++ "<p class=\"no-decls\"><em>No new declarations</em></p>\n"
  else
    s := s ++ s!"<div class=\"declarations\"><pre class=\"hl lean block\" data-lean-context=\"{testId}\">"
    let mut first := true
    for decl in decls do
      if first then first := false else s := s ++ "\n"
      s := s ++ renderPrettyDecl decl declOrigin
    s := s ++ "</pre></div>\n"
  s := s ++ "</section>\n"
  return s

/-! ## CSS -/

private def highlightCss : String :=
  "
/* Verso-compatible syntax highlighting */
.hl.lean {
  white-space: pre;
  font-weight: normal;
  font-style: normal;
  font-size: inherit;
}
.hl.lean .keyword {
  color: var(--verso-code-keyword-color, #7b1fa2);
  font-weight: var(--verso-code-keyword-weight, bold);
}
.hl.lean .const {
  color: var(--verso-code-const-color, #1565c0);
}
.hl.lean .var {
  color: var(--verso-code-var-color, #37474f);
  font-style: italic;
}
.hl.lean .sort {
  color: var(--verso-code-keyword-color, #7b1fa2);
  font-weight: bold;
}
.hl.lean .literal, .hl.lean .unknown {
  color: var(--verso-code-color, #333);
}
.hl.lean .literal.string {
  color: #2e7d32;
}
.hl.lean .level-var {
  color: #6a1b9a;
  font-style: italic;
}
.hl.lean .level-const {
  color: #6a1b9a;
}
.hl.lean .level-op {
  color: #6a1b9a;
  font-weight: bold;
}
.hl.lean .token {
  transition: all 0.25s;
}
@media (hover: hover) {
  .hl.lean .token.binding-hl {
    background-color: #eee;
    border-radius: 2px;
    transition: none;
  }
}
.hl.lean.block {
  display: block;
}
"

private def css : String :=
  "
* { box-sizing: border-box; margin: 0; padding: 0; }
html, body { height: 100%; }
body {
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
  background: #fafafa;
  color: #333;
  display: flex;
}
nav.sidebar {
  width: 260px;
  min-width: 260px;
  height: 100vh;
  position: sticky;
  top: 0;
  overflow-y: auto;
  background: #fff;
  border-right: 1px solid #e0e0e0;
  padding: 16px 0;
  font-size: 13px;
}
nav.sidebar h1 {
  font-size: 16px;
  padding: 0 16px 12px;
  border-bottom: 1px solid #eee;
  margin-bottom: 8px;
  color: #222;
}
nav.sidebar .summary {
  padding: 0 16px 10px;
  font-size: 12px;
  color: #888;
  border-bottom: 1px solid #eee;
  margin-bottom: 4px;
}
nav.sidebar ul { list-style: none; }
nav.sidebar li a {
  display: block;
  padding: 5px 16px;
  color: #444;
  text-decoration: none;
  border-left: 3px solid transparent;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}
nav.sidebar li a:hover {
  background: #f0f4ff;
}
nav.sidebar li a.active {
  background: #e8f0fe;
  border-left-color: #1976d2;
  color: #1565c0;
  font-weight: 600;
}
nav.sidebar li .marker { margin-right: 4px; font-size: 14px; }
main {
  flex: 1;
  padding: 24px 32px;
  overflow-y: auto;
  max-width: 900px;
  outline: none;
}
.test {
  margin-bottom: 20px;
  border: 1px solid #e0e0e0;
  border-radius: 8px;
  padding: 16px 20px;
  background: white;
  box-shadow: 0 1px 3px rgba(0,0,0,0.06);
  scroll-margin-top: 12px;
}
.test.good { border-left: 4px solid #4caf50; }
.test.bad { border-left: 4px solid #f44336; }
.test h2 { font-size: 1.02em; margin-bottom: 4px; }
.test h2 .marker { margin-right: 6px; }
.description { color: #666; margin-bottom: 14px; font-size: 0.92em; }
.description p { margin-bottom: 6px; }
.description p:last-child { margin-bottom: 0; }
.description code {
  font-family: 'JetBrains Mono', 'Fira Code', 'Source Code Pro', 'Consolas', monospace;
  font-size: 12px; background: #f0f0f0; padding: 1px 4px; border-radius: 3px;
}
.description a { color: #1976d2; word-break: break-all; }
.shared { color: #777; font-size: 0.88em; margin-bottom: 10px; }
.shared code {
  font-family: 'JetBrains Mono', 'Fira Code', 'Source Code Pro', 'Consolas', monospace;
  font-size: 12px;
  background: #f0f0f0;
  padding: 1px 4px;
  border-radius: 3px;
}
.shared a, .shared .const-ref { color: #1976d2; text-decoration: none; }
.shared a:hover, .shared .const-ref:hover { text-decoration: underline; }
.declarations a.const-ref { color: inherit; text-decoration: none; }
.declarations a.const-ref:hover { text-decoration: underline; }
.declarations {
  background: #f8f9fa;
  border: 1px solid #e8e8e8;
  border-radius: 4px;
  padding: 10px 14px;
  overflow-x: auto;
}
.declarations pre { margin: 0; }
.declarations pre, .declarations code {
  font-family: 'JetBrains Mono', 'Fira Code', 'Source Code Pro', 'Consolas', monospace;
  font-size: 13px;
  line-height: 1.5;
}
.no-decls { color: #999; }
.page-header { margin-bottom: 24px; }
.page-header h1 { font-size: 1.4em; margin-bottom: 8px; color: #222; }
.page-header p { color: #555; font-size: 0.92em; line-height: 1.5; }
.page-header a { color: #1976d2; }
.page-header code {
  font-family: 'JetBrains Mono', 'Fira Code', 'Source Code Pro', 'Consolas', monospace;
  font-size: 12px; background: #f0f0f0; padding: 1px 4px; border-radius: 3px;
}
.tooltip {
  position: fixed;
  background: #333;
  color: #fff;
  padding: 6px 10px;
  border-radius: 4px;
  font-size: 12px;
  white-space: pre;
  width: max-content;
  max-width: 90vw;
  z-index: 1000;
  pointer-events: none;
  box-shadow: 0 2px 8px rgba(0,0,0,0.3);
  font-family: 'JetBrains Mono', 'Fira Code', 'Source Code Pro', 'Consolas', monospace;
}
.nav-toggle {
  display: none;
  position: fixed;
  top: 10px;
  left: 10px;
  z-index: 200;
  background: #fff;
  border: 1px solid #ccc;
  border-radius: 6px;
  padding: 6px 10px;
  font-size: 20px;
  cursor: pointer;
  box-shadow: 0 1px 4px rgba(0,0,0,0.12);
  line-height: 1;
}
.nav-backdrop {
  display: none;
  position: fixed;
  inset: 0;
  background: rgba(0,0,0,0.3);
  z-index: 99;
}
@media (max-width: 700px) {
  .nav-toggle { display: block; }
  nav.sidebar {
    position: fixed;
    left: 0; top: 0;
    height: 100vh;
    z-index: 100;
    transform: translateX(-100%);
    transition: transform 0.2s ease;
    box-shadow: 2px 0 8px rgba(0,0,0,0.15);
  }
  nav.sidebar.open { transform: translateX(0); }
  .nav-backdrop.open { display: block; }
  main { padding: 48px 12px 24px; max-width: 100%; }
}
"

/-! ## JavaScript -/

private def js : String :=
  "
document.addEventListener('DOMContentLoaded', function() {
  // Focus main pane so PgDn/PgUp/Space work immediately
  var m = document.querySelector('main');
  if (m) m.focus();

  // Mobile nav toggle
  var nav = document.querySelector('nav.sidebar');
  var toggle = document.querySelector('.nav-toggle');
  var backdrop = document.querySelector('.nav-backdrop');
  function closeNav() { nav.classList.remove('open'); backdrop.classList.remove('open'); }
  toggle.addEventListener('click', function() {
    var open = nav.classList.toggle('open');
    backdrop.classList.toggle('open', open);
  });
  backdrop.addEventListener('click', closeNav);
  nav.addEventListener('click', function(e) {
    if (e.target.tagName === 'A') closeNav();
  });

  // Binding highlighting: on hover, highlight all tokens with same data-binding
  for (var c of document.querySelectorAll('.hl.lean .token')) {
    if (c.dataset.binding && c.dataset.binding !== '') {
      c.addEventListener('mouseover', function(event) {
        var context = this.closest('.hl.lean').dataset.leanContext;
        for (var example of document.querySelectorAll('.hl.lean')) {
          if (example.dataset.leanContext === context) {
            for (var tok of example.querySelectorAll('.token')) {
              if (this.dataset.binding === tok.dataset.binding) {
                tok.classList.add('binding-hl');
              }
            }
          }
        }
      });
    }
    c.addEventListener('mouseout', function(event) {
      for (var tok of document.querySelectorAll('.hl.lean .token')) {
        tok.classList.remove('binding-hl');
      }
    });
  }

  // Hover tooltips for tokens with data-sig
  document.querySelectorAll('[data-sig]').forEach(function(el) {
    var tooltip = null;
    el.addEventListener('mouseenter', function() {
      var sig = el.getAttribute('data-sig');
      if (!sig) return;
      tooltip = document.createElement('div');
      tooltip.className = 'tooltip';
      tooltip.textContent = sig;
      document.body.appendChild(tooltip);
      var rect = el.getBoundingClientRect();
      var ttHeight = tooltip.offsetHeight;
      var top = rect.top - ttHeight - 4;
      if (top < 4) top = rect.bottom + 4;
      tooltip.style.left = Math.max(4, rect.left) + 'px';
      tooltip.style.top = top + 'px';
    });
    el.addEventListener('mouseleave', function() {
      if (tooltip && tooltip.parentNode) tooltip.parentNode.removeChild(tooltip);
      tooltip = null;
    });
  });

  // Nav highlighting on scroll
  var sections = document.querySelectorAll('section.test');
  var navLinks = document.querySelectorAll('nav.sidebar a');
  var linkMap = {};
  navLinks.forEach(function(a) { linkMap[a.getAttribute('href').slice(1)] = a; });

  var mainEl = document.querySelector('main');
  function updateActive() {
    var scrollTop = mainEl ? mainEl.scrollTop : (window.scrollY || document.documentElement.scrollTop);
    var current = null;
    sections.forEach(function(sec) {
      var top = mainEl ? (sec.offsetTop - mainEl.offsetTop) : sec.offsetTop;
      if (top - 60 <= scrollTop) current = sec.id;
    });
    navLinks.forEach(function(a) { a.classList.remove('active'); });
    if (current && linkMap[current]) {
      linkMap[current].classList.add('active');
      linkMap[current].scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    }
  }
  if (mainEl) mainEl.addEventListener('scroll', updateActive);
  else window.addEventListener('scroll', updateActive);
  updateActive();
});
"

def generatePage (tests : Array (ResolvedTest × Array PrettyDecl)) : String := Id.run do
  let goodCount := tests.filter (·.1.parsed.file.isGood) |>.size
  let badCount := tests.size - goodCount
  let mut html := "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n"
  html := html ++ "<meta charset=\"utf-8\">\n"
  html := html ++ "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
  html := html ++ "<title>Tutorial Tests</title>\n"
  html := html ++ s!"<style>{css}{highlightCss}</style>\n"
  let sourceUrl := match tests[0]? with
    | some (t, _) => t.parsed.stats.sourceUrl
    | none => ""
  html := html ++ "</head>\n<body>\n"
  html := html ++ "<button class=\"nav-toggle\" aria-label=\"Toggle navigation\">&#9776;</button>\n"
  html := html ++ "<div class=\"nav-backdrop\"></div>\n"
  -- Sidebar nav
  html := html ++ "<nav class=\"sidebar\">\n"
  html := html ++ "<h1>Lean Kernel Arena</h1>\n"
  html := html ++ s!"<div class=\"summary\">{tests.size} tests: {goodCount} &#x1F44D; {badCount} &#x270B;</div>\n"
  html := html ++ "<ul>\n"
  for (test, _) in tests do
    let marker := if test.parsed.file.isGood then "&#x1F44D;" else "&#x270B;"
    let testId := "test-" ++ test.parsed.file.baseName
    let displayName := stripPrefix test.parsed.stats.name
    html := html ++ s!"<li><a href=\"#{testId}\"><span class=\"marker\">{marker}</span>{escapeHtml displayName}</a></li>\n"
  html := html ++ "</ul>\n</nav>\n"
  -- Build mapping from declaration name to the test section that first defined it
  let mut declOrigin : Std.HashMap Lean.Name String := {}
  for (test, _) in tests do
    let testId := "test-" ++ test.parsed.file.baseName
    for name in test.newDecls do
      if !declOrigin.contains name then
        declOrigin := declOrigin.insert name testId
  -- Main content
  html := html ++ "<main tabindex=\"-1\">\n"
  html := html ++ "<header class=\"page-header\">\n"
  html := html ++ "<h1>Tutorial Test Cases</h1>\n"
  html := html ++ "<p>These are the test cases from the <a href=\""
  html := html ++ escapeHtml sourceUrl
  html := html ++ "\">Lean Kernel Arena tutorial</a>. "
  html := html ++ "Each test is a small Lean 4 environment exported via <code>lean4export</code>. "
  html := html ++ s!"Good tests (&#x1F44D;) should be accepted by a correct kernel implementation; "
  html := html ++ s!"bad tests (&#x270B;) should be rejected. "
  html := html ++ "Later tests build on declarations from earlier ones; shared declarations are listed under <em>Includes</em>.</p>\n"
  html := html ++ "</header>\n"
  for (test, decls) in tests do
    html := html ++ renderTest test decls declOrigin
  html := html ++ "</main>\n"
  html := html ++ s!"<script>{js}</script>\n"
  html := html ++ "</body>\n</html>\n"
  return html

end TestPrinter
