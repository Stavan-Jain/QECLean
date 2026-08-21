/* Focused-subgraph view for the blueprint dependency graph.
 *
 * The dependency graph page renders every node in the blueprint at once, which
 * is the right default for "what does this library contain" and the wrong one
 * for "what does this one result rest on". This script adds a picker that
 * restricts the graph to a single node's transitive dependencies -- the
 * subgraph leading up to it -- and re-runs the graphviz layout on just that
 * subgraph, so the answer is a small readable picture rather than a highlighted
 * region of a large one.
 *
 * Edge direction, which is easy to get backwards: plastexdepgraph emits
 * `A -> B` to mean "B uses A", i.e. arrows run from a prerequisite to the thing
 * that needs it. So the dependencies of X are its *ancestors*, reached by
 * walking edges in reverse, and the results that build on X are its
 * descendants. Both directions are offered; dependencies are the default.
 *
 * How it hooks in
 * ---------------
 * plasTeX copies every `extra-js` entry from `blueprint/src/` into `web/js/`
 * and the upstream dep-graph template emits a <script> tag for each, after its
 * own inline setup script. So this file runs once the graph has been asked to
 * render, and can reuse the same d3-graphviz instance:
 * `d3.select('#graph').graphviz()` returns the existing renderer rather than
 * building a second one (see `selection_graphviz` in d3-graphviz).
 *
 * The one thing it needs that upstream does not hand over is the graphviz
 * source, which the template interpolates straight into a `.renderDot(`...`)`
 * call instead of a variable. It is recovered by reading that call out of the
 * inline script. `scripts/check-blueprint-render.sh` asserts that call is still
 * shaped that way, so an upstream template change fails the build instead of
 * silently costing us the feature. If recovery fails anyway, the script bails
 * out without adding its controls, leaving the stock full graph working.
 *
 * The file is loaded on every page of the blueprint, not just this one; it
 * exits immediately when there is no graph to act on.
 */
(function () {
  'use strict';

  const graphDiv = document.getElementById('graph');
  if (!graphDiv || typeof d3 === 'undefined') return;

  /* ---------------------------------------------------------------- parsing */

  /* Split `text` on `sep`, ignoring separators inside quoted strings or
   * brackets. The generated dot has no nested brackets, but labels are
   * arbitrary text and may contain anything. */
  function splitTop(text, sep) {
    const out = [];
    let cur = '', depth = 0, inStr = false;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (inStr) {
        cur += c;
        if (c === '\\' && i + 1 < text.length) cur += text[++i];
        else if (c === '"') inStr = false;
        continue;
      }
      if (c === '"') { inStr = true; cur += c; continue; }
      if (c === '[' || c === '{') depth++;
      else if (c === ']' || c === '}') depth--;
      else if (c === sep && depth === 0) { out.push(cur); cur = ''; continue; }
      cur += c;
    }
    out.push(cur);
    return out;
  }

  /* Split a statement into its head and the raw text of its attribute list,
   * e.g. `"a" -> "b" [style=dashed]` into `"a" -> "b"` and `style=dashed`. */
  function splitHeadAttrs(stmt) {
    let inStr = false;
    for (let i = 0; i < stmt.length; i++) {
      const c = stmt[i];
      if (inStr) {
        if (c === '\\') i++;
        else if (c === '"') inStr = false;
        continue;
      }
      if (c === '"') { inStr = true; continue; }
      if (c === '[') {
        const end = stmt.lastIndexOf(']');
        return [stmt.slice(0, i).trim(), stmt.slice(i + 1, end > i ? end : undefined)];
      }
    }
    return [stmt.trim(), null];
  }

  /* Read the identifiers out of a statement head, dropping the `->` operators.
   * Handles both quoted (`"def:steane7"`) and bare (`node`) forms. */
  function parseHeadIds(head) {
    const ids = [];
    let i = 0;
    while (i < head.length) {
      if (/\s/.test(head[i])) { i++; continue; }
      if (head[i] === '-' && head[i + 1] === '>') { i += 2; continue; }
      if (head[i] === '"') {
        let s = '', j = i + 1;
        while (j < head.length && head[j] !== '"') {
          if (head[j] === '\\') { s += head[j + 1]; j += 2; }
          else s += head[j++];
        }
        ids.push(s);
        i = j + 1;
      } else {
        let k = i;
        while (k < head.length && !/\s/.test(head[k]) && !(head[k] === '-' && head[k + 1] === '>')) k++;
        ids.push(head.slice(i, k));
        i = k;
      }
    }
    return ids;
  }

  /* Parse the subset of dot that pygraphviz emits. Attribute lists are kept as
   * raw text and passed straight back out: this only needs the graph's shape,
   * and not reinterpreting styling means it cannot corrupt it. */
  function parseDot(dot) {
    const open = dot.indexOf('{');
    const close = dot.lastIndexOf('}');
    if (open < 0 || close <= open) return null;

    const model = {
      header: dot.slice(0, open + 1).trim(),
      defaults: [],
      order: [],
      attrs: new Map(),
      edges: []
    };

    for (const raw of splitTop(dot.slice(open + 1, close), ';')) {
      const stmt = raw.trim();
      if (!stmt) continue;
      const [head, attrs] = splitHeadAttrs(stmt);
      if (/^(graph|node|edge)$/.test(head)) { model.defaults.push(stmt); continue; }

      const ids = parseHeadIds(head);
      if (!ids.length) continue;
      for (const id of ids) {
        if (!model.attrs.has(id)) { model.attrs.set(id, null); model.order.push(id); }
      }
      if (ids.length === 1) {
        /* A bare `"id" [..]` statement carries the node's styling; an id that
         * only ever appeared inside an edge keeps its null attribute list. */
        if (attrs !== null) model.attrs.set(ids[0], attrs);
      } else {
        for (let k = 0; k + 1 < ids.length; k++) {
          model.edges.push({ from: ids[k], to: ids[k + 1], attrs: attrs });
        }
      }
    }
    return model;
  }

  /* ---------------------------------------------------------------- emitting */

  function quoteId(id) {
    return '"' + id.replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"';
  }

  /* Rewrite an attribute list, replacing any listed keys. Used only for the
   * focused node, whose marker must not disturb the colours -- the legend gives
   * border and fill colours a meaning (formalized, ready, in Mathlib), so the
   * focus is marked with a heavier double outline instead. */
  function overrideAttrs(raw, overrides) {
    const keys = Object.keys(overrides);
    const kept = (raw ? splitTop(raw, ',') : [])
      .map(function (s) { return s.trim(); })
      .filter(function (s) {
        if (!s) return false;
        const eq = s.indexOf('=');
        const key = (eq < 0 ? s : s.slice(0, eq)).trim().replace(/^"|"$/g, '');
        return keys.indexOf(key) === -1;
      });
    for (const k of keys) kept.push(k + '=' + overrides[k]);
    return kept.join(', ');
  }

  const FOCUS_MARKER = { penwidth: '4', peripheries: '2' };

  function emitDot(model, keep, focusId) {
    const lines = [model.header];
    for (const d of model.defaults) lines.push('\t' + d + ';');
    for (const id of model.order) {
      if (keep && !keep.has(id)) continue;
      let attrs = model.attrs.get(id);
      if (id === focusId) attrs = overrideAttrs(attrs, FOCUS_MARKER);
      lines.push('\t' + quoteId(id) + (attrs ? '\t[' + attrs + ']' : '') + ';');
    }
    for (const e of model.edges) {
      if (keep && (!keep.has(e.from) || !keep.has(e.to))) continue;
      lines.push('\t' + quoteId(e.from) + ' -> ' + quoteId(e.to) +
                 (e.attrs ? '\t[' + e.attrs + ']' : '') + ';');
    }
    lines.push('}');
    return lines.join('\n');
  }

  /* ------------------------------------------------------------------- setup */

  /* Recover the graphviz source from the template's inline `.renderDot(`...`)`
   * call. The text is read raw, so escapes such as the default `label="\N"`
   * reach graphviz as written rather than being eaten by the JS template
   * literal -- harmless either way, since every node carries an explicit
   * label. */
  function extractDot() {
    const scripts = document.querySelectorAll('script:not([src])');
    for (const s of scripts) {
      const m = /renderDot\(`([\s\S]*?)`\)/.exec(s.textContent);
      if (m) return m[1];
    }
    return null;
  }

  const source = extractDot();
  if (source === null) {
    console.warn('dep_graph_focus: could not read the graph source; ' +
                 'leaving the full graph as-is.');
    return;
  }
  const model = parseDot(source);
  if (!model || !model.order.length) {
    console.warn('dep_graph_focus: graph source did not parse; ' +
                 'leaving the full graph as-is.');
    return;
  }

  /* Adjacency, in both directions. `preds` walks towards dependencies. */
  const preds = new Map();
  const succs = new Map();
  for (const id of model.order) { preds.set(id, []); succs.set(id, []); }
  for (const e of model.edges) {
    if (!preds.has(e.to) || !succs.has(e.from)) continue;
    preds.get(e.to).push(e.from);
    succs.get(e.from).push(e.to);
  }

  /* Breadth-first reachability, so `depth` can cut the walk off at a distance
   * rather than only ever taking the whole transitive closure. */
  function reach(start, adj, maxDepth) {
    const seen = new Set([start]);
    let frontier = [start], depth = 0;
    while (frontier.length && (!maxDepth || depth < maxDepth)) {
      const next = [];
      for (const id of frontier) {
        for (const nb of adj.get(id) || []) {
          if (!seen.has(nb)) { seen.add(nb); next.push(nb); }
        }
      }
      frontier = next;
      depth++;
    }
    return seen;
  }

  /* ---------------------------------------------------------- node metadata */

  /* Human-readable names come from the statement modals the template already
   * emits, so the picker can say "Definition 12 -- Anticommutation" rather than
   * only `def:anticommute`. */
  const titles = new Map();
  for (const el of document.querySelectorAll('#statements div.thm[id]')) {
    const head = el.querySelector('.thm_thmheading');
    if (!head) continue;
    const part = function (suffix) {
      const n = head.querySelector('[class$="_thm' + suffix + '"]');
      return n ? n.textContent.trim() : '';
    };
    const words = [part('caption'), part('label')].filter(Boolean).join(' ');
    const title = part('title');
    titles.set(el.id, [words, title].filter(Boolean).join(' \u2014 '));
  }

  function shortName(id) {
    const i = id.lastIndexOf(':');
    return i < 0 ? id : id.slice(i + 1);
  }

  /* Accept a full id (`def:steane7`), the short name shown on the graph node
   * (`steane7`), or any unambiguous substring of either. */
  function resolve(text) {
    const q = text.trim();
    if (!q) return null;
    if (model.attrs.has(q)) return q;
    const lower = q.toLowerCase();
    const exact = model.order.filter(function (id) {
      return shortName(id).toLowerCase() === lower;
    });
    if (exact.length === 1) return exact[0];
    const partial = model.order.filter(function (id) {
      return id.toLowerCase().indexOf(lower) !== -1 ||
             (titles.get(id) || '').toLowerCase().indexOf(lower) !== -1;
    });
    return partial.length === 1 ? partial[0] : null;
  }

  /* ---------------------------------------------------------------- controls */

  const DIRECTIONS = [
    ['up', 'what it depends on'],
    ['down', 'what depends on it'],
    ['both', 'both directions']
  ];

  const bar = document.createElement('div');
  bar.id = 'focus-controls';
  bar.innerHTML =
    '<label for="focus-node">Focus on</label>' +
    '<input id="focus-node" list="focus-node-list" type="search" autocomplete="off" ' +
           'spellcheck="false" placeholder="a node name, e.g. steane7">' +
    '<datalist id="focus-node-list"></datalist>' +
    '<label for="focus-dir">show</label>' +
    '<select id="focus-dir">' +
      DIRECTIONS.map(function (d) {
        return '<option value="' + d[0] + '">' + d[1] + '</option>';
      }).join('') +
    '</select>' +
    '<label for="focus-depth">to depth</label>' +
    '<select id="focus-depth">' +
      '<option value="0">all the way</option>' +
      '<option value="1">1</option><option value="2">2</option>' +
      '<option value="3">3</option><option value="4">4</option>' +
    '</select>' +
    '<button id="focus-clear" type="button">Show everything</button>' +
    '<span id="focus-status"></span>';
  graphDiv.parentNode.insertBefore(bar, graphDiv);

  const nodeInput = bar.querySelector('#focus-node');
  const dirSelect = bar.querySelector('#focus-dir');
  const depthSelect = bar.querySelector('#focus-depth');
  const clearButton = bar.querySelector('#focus-clear');
  const status = bar.querySelector('#focus-status');

  const datalist = bar.querySelector('#focus-node-list');
  for (const id of model.order.slice().sort()) {
    const option = document.createElement('option');
    option.value = id;
    option.label = titles.get(id) || shortName(id);
    datalist.appendChild(option);
  }

  /* A "focus this" control on each statement modal, so a node found by reading
   * the graph can be focused without retyping its name into the picker. */
  for (const modal of document.querySelectorAll('#statements .dep-modal-container')) {
    const thm = modal.querySelector('div.thm[id]');
    if (!thm || !model.attrs.has(thm.id)) continue;
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'focus-link';
    button.textContent = 'Focus on this';
    button.addEventListener('click', function () {
      modal.style.display = 'none';
      const statements = document.getElementById('statements');
      if (statements) statements.style.display = 'none';
      apply(thm.id, dirSelect.value, Number(depthSelect.value), true);
    });
    thm.appendChild(button);
  }

  /* ------------------------------------------------------------- re-rendering */

  const graphviz = d3.select('#graph').graphviz();
  let rendering = false;
  let queued = null;
  let ready = false;

  /* Upstream binds the node click handlers inside its `interactive()`, which
   * also binds the legend toggle and the modal close buttons with jQuery.
   * Those two are on static markup that survives a re-render, and jQuery
   * handlers accumulate, so calling `interactive()` again would bind the legend
   * twice and leave it toggling to a no-op. Only the freshly created `.node`
   * elements need re-binding, so do just that. */
  function bindNodes() {
    d3.selectAll('.node')
      .attr('pointer-events', 'fill')
      .on('click', function () {
        const id = d3.select(this).selectAll('title').text().trim();
        const escaped = typeof latexLabelEscaper === 'function'
          ? latexLabelEscaper(id)
          : id.replace(/\./g, '\\.').replace(/:/g, '\\:');
        $('#statements > div').hide();
        $('.thm').hide();
        $('#' + escaped + '_modal').show().children().show().children().show();
        $('#statements').show();
      });
  }

  function onRenderEnd() {
    rendering = false;
    bindNodes();
    try { graphviz.resetZoom(); } catch (e) { /* zoom not initialised yet */ }
    drain();
  }

  function drain() {
    if (queued === null || rendering || !ready) return;
    const next = queued;
    queued = null;
    render(next);
  }

  function render(dot) {
    if (!ready || rendering) { queued = dot; return; }
    rendering = true;
    /* Attach the handler *before* rendering rather than chaining it onto
     * `renderDot`. Once the graphviz wasm has loaded a render runs
     * synchronously and dispatches `end` before `renderDot` returns, so a
     * handler attached afterwards is already too late and the completion is
     * never observed. Upstream gets away with chaining only because its render
     * is the one that waits for the wasm to arrive. */
    graphviz.on('end', onRenderEnd);
    graphviz.renderDot(dot);
  }

  /* Wait for upstream's initial render before taking the `end` event over.
   * That render is what triggers its `interactive()`, which binds the legend
   * toggle and the modal close buttons with jQuery handlers that accumulate on
   * every call -- so it has to run exactly once, and displacing it beforehand
   * would mean it never ran at all. Waiting also keeps a `?focus=` deep link
   * from starting a second render while the first is still in flight. */
  (function awaitInitialRender(attempt) {
    if (graphDiv.querySelector('svg .node')) { ready = true; drain(); return; }
    if (attempt > 300) return;          /* ~15s; the graph never came up */
    window.setTimeout(function () { awaitInitialRender(attempt + 1); }, 50);
  })(0);

  /* ------------------------------------------------------------------ state */

  let current = null;

  function describe(id, dir, kept) {
    if (!id) return model.order.length + ' nodes';
    const word = dir === 'up' ? 'dependencies of' : dir === 'down' ? 'results depending on' : 'neighbourhood of';
    return kept.size + ' of ' + model.order.length + ' nodes \u2014 ' +
           word + ' ' + shortName(id);
  }

  function syncUrl(id, dir, depth) {
    if (!window.history || !window.history.replaceState) return;
    const params = new URLSearchParams(window.location.search);
    if (id) {
      params.set('focus', id);
      params.set('dir', dir);
      if (depth) params.set('depth', String(depth)); else params.delete('depth');
    } else {
      params.delete('focus');
      params.delete('dir');
      params.delete('depth');
    }
    const query = params.toString();
    window.history.replaceState(null, '',
      window.location.pathname + (query ? '?' + query : '') + window.location.hash);
  }

  function apply(id, dir, depth, syncInput) {
    if (!id) {
      current = null;
      if (syncInput) nodeInput.value = '';
      status.textContent = describe(null, dir, null);
      syncUrl(null, dir, depth);
      render(emitDot(model, null, null));
      return;
    }
    let keep;
    if (dir === 'down') {
      keep = reach(id, succs, depth);
    } else if (dir === 'both') {
      keep = reach(id, preds, depth);
      for (const n of reach(id, succs, depth)) keep.add(n);
    } else {
      keep = reach(id, preds, depth);
    }
    current = id;
    if (syncInput) nodeInput.value = id;
    status.textContent = describe(id, dir, keep);
    syncUrl(id, dir, depth);
    render(emitDot(model, keep, id));
  }

  function reapply() {
    apply(current, dirSelect.value, Number(depthSelect.value), false);
  }

  let debounce = null;
  function onInput() {
    window.clearTimeout(debounce);
    debounce = window.setTimeout(function () {
      const text = nodeInput.value.trim();
      if (!text) { apply(null, dirSelect.value, Number(depthSelect.value), false); return; }
      const id = resolve(text);
      if (id) {
        apply(id, dirSelect.value, Number(depthSelect.value), false);
      } else {
        status.textContent = 'no single node matches \u201c' + text + '\u201d';
      }
    }, 200);
  }

  nodeInput.addEventListener('input', onInput);
  nodeInput.addEventListener('change', onInput);
  dirSelect.addEventListener('change', reapply);
  depthSelect.addEventListener('change', reapply);
  clearButton.addEventListener('click', function () {
    nodeInput.value = '';
    apply(null, dirSelect.value, Number(depthSelect.value), true);
  });

  /* A focused view is shareable: `?focus=def:steane7&dir=up` reproduces it. */
  const params = new URLSearchParams(window.location.search);
  const wanted = params.get('focus');
  const wantedDir = params.get('dir');
  const wantedDepth = Number(params.get('depth')) || 0;
  if (wantedDir && DIRECTIONS.some(function (d) { return d[0] === wantedDir; })) {
    dirSelect.value = wantedDir;
  }
  if (wantedDepth >= 1 && wantedDepth <= 4) depthSelect.value = String(wantedDepth);

  const initial = wanted ? resolve(wanted) : null;
  if (initial) {
    apply(initial, dirSelect.value, Number(depthSelect.value), true);
  } else {
    /* The stock render is already running; just describe it and pick up the
     * node click handlers it binds. */
    status.textContent = describe(null, dirSelect.value, null);
  }
})();
