// Use the pinned Glitnir renderer and exporter over read-only, prepared snapshots.
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const {readFileSync} = require('node:fs');
const path = require('node:path');
const {JSDOM} = require('jsdom');

const ROOT = path.resolve(__dirname, '../..');
const NOTEBOOK_NAVIGATION_CSS = readFileSync(path.join(ROOT, 'gallery/notebook-navigation.css'), 'utf8');
const escape = value => String(value).replace(/[&<>"']/g, char => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[char]));
const TOPICS = {
  basics: ['Start here', 'Small models introduce claims, saved evidence and refutations.'],
  circuits: ['Circuits', 'Composition, contracts, rewrites and discrete dynamics.'],
  dynamics: ['Dynamical systems', 'Continuous trajectories and their bounds.'],
  galerkin: ['Galerkin models', 'Finite-dimensional fluid models, energy and enstrophy.'],
  pdes: ['Partial differential equations', 'Stream contracts, formal expansions and analytic certificates.'],
};

function rewriteReferences(content, notebooks) {
  for (const link of content.querySelectorAll('a[href]')) {
    const url = new URL(link.getAttribute('href'), 'https://export.invalid');
    if (url.origin !== 'https://export.invalid' || url.pathname !== '/') continue;
    const module = url.searchParams.get('reference') || url.searchParams.get('notebook');
    const target = notebooks.find(item => item.snapshot.file === `${module}.lean`);
    if (target) link.href = `https://gallery.invalid/${target.html}`;
  }
}

function validateExport(html, entry) {
  const dom = new JSDOM(html);
  try {
    const doc = dom.window.document;
    assert.equal(doc.querySelectorAll('script,iframe,object,embed,form,.view-wait,.katex-error').length, 0, 'Unsafe or incomplete export');
    assert.ok(doc.body.textContent.includes(entry.snapshot.sha256), 'Missing source fingerprint');
    for (const claim of entry.snapshot.claims) {
      assert.ok(doc.getElementById(`cell-${claim.name}`), `Missing claim ${claim.name}`);
    }
    assert.equal(doc.querySelectorAll('.view-cell').length, entry.snapshot.views.length, 'Missing diagram');
    for (const view of doc.querySelectorAll('.view-cell')) {
      assert.ok(view.querySelector('svg.circuit-scene, .view-body img'), 'Diagram has no drawing');
    }
    for (const element of doc.querySelectorAll('*')) {
      for (const attribute of element.attributes) assert.ok(!/^on/i.test(attribute.name), 'Event handler in export');
    }
    for (const image of doc.images) assert.ok(image.src.startsWith('data:image/'), 'Image is not embedded');
  } finally { dom.window.close(); }
}

function addNotebookNavigation(doc, entry) {
  const app = doc.querySelector('.app');
  assert.ok(app, 'Missing notebook container');
  const nav = doc.createElement('nav');
  nav.className = 'gallery-nav';
  nav.setAttribute('aria-label', 'Notebook navigation');
  nav.innerHTML = `<a class="gallery-back" href="../index.html" aria-label="Back to notebook gallery"><svg viewBox="0 0 20 20" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><path d="m11 5-5 5 5 5M6 10h10"/></svg><span>Gallery</span></a><a class="gallery-source" href="${escape(entry.source_url)}" title="View ${escape(entry.snapshot.file)} on GitHub"><svg viewBox="0 0 20 20" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><path d="m7 5-5 5 5 5m6-10 5 5-5 5"/></svg><span>Lean source</span></a>`;
  app.prepend(nav);
  const style = doc.createElement('style');
  style.textContent = NOTEBOOK_NAVIGATION_CSS;
  doc.head.append(style);
}

async function renderNotebook(manifest, entry) {
  const dom = new JSDOM(await fs.readFile(path.join(manifest.media, 'index.html'), 'utf8'), {
    runScripts: 'outside-only', url: 'https://export.invalid/',
  });
  const {window} = dom;
  const errors = [];
  let exported;
  window.addEventListener('error', event => errors.push(event.error));
  window.matchMedia = () => ({matches: false});
  window.HTMLElement.prototype.scrollIntoView = () => {};
  const schedule = window.setTimeout.bind(window);
  window.setTimeout = (callback, delay) => [250, 1000, 4000].includes(delay) ? 0 : schedule(callback, delay);
  const OriginalDate = window.Date;
  window.Date = class extends OriginalDate {
    constructor(...args) { super(...(args.length ? args : [manifest.timestamp])); }
  };
  const assetURL = url => {
    const parsed = new URL(url, 'https://export.invalid');
    const asset = entry.figures[parsed.searchParams.get('path')];
    assert.ok(asset && asset.sha256 === parsed.searchParams.get('sha256'), 'Missing or changed figure');
    return asset.url;
  };
  window.forsetiHost = {
    assetURL, exportAsset: async url => assetURL(url),
    saveHTML: async html => { exported = html; },
    fetch: async (url, options = {}) => {
      try {
        assert.equal(options.method || 'GET', 'GET', 'Export must never write or replay');
        const parsed = new URL(url, 'https://export.invalid');
        let json;
        if (url === '/api/notebook') json = entry.snapshot;
        else if (url === '/api/export/styles') json = {css: manifest.css};
        else if (parsed.pathname === '/api/view') {
          json = entry.drawings[`${parsed.searchParams.get('cell')}:${parsed.searchParams.get('line')}`];
          assert.ok(json, `Missing prepared diagram ${url}`);
        } else throw new Error(`Unexpected exporter request: ${url}`);
        return {ok: true, status: 200, json: async () => structuredClone(json)};
      } catch (error) { errors.push(error); throw error; }
    },
  };
  try {
    for (const script of ['katex/katex.min.js', 'export.js', 'circuits.js', 'cards.js', 'app.js']) {
      window.eval(await fs.readFile(path.join(manifest.media, script), 'utf8'));
    }
    const originalExport = window.forsetiExport;
    window.forsetiExport = async options => {
      // Glitnir drops live-editor URLs. Translate only known corpus references
      // through an inert HTTPS marker, then make them relative after export.
      rewriteReferences(options.content, manifest.notebooks);
      return originalExport(options);
    };
    const deadline = Date.now() + 30_000;
    while (!window.document.querySelector('#doc .cell') || window.document.querySelector('.view-wait')) {
      if (errors.length) throw errors[0];
      if (Date.now() > deadline) throw new Error(`Renderer timed out: ${entry.path}`);
      await new Promise(resolve => setTimeout(resolve, 10));
    }
    window.document.getElementById('export-html').click();
    while (!exported) {
      if (errors.length) throw errors[0];
      if (Date.now() > deadline) throw new Error(`Export failed: ${entry.path}: ${window.document.body.textContent.slice(-1000)}`);
      await new Promise(resolve => setTimeout(resolve, 10));
    }
    assert.deepEqual(errors, []);
    validateExport(exported, entry);
    const page = new JSDOM(exported);
    try {
      const doc = page.window.document;
      for (const link of doc.querySelectorAll('a[href^="https://gallery.invalid/"]')) {
        const target = new URL(link.href).pathname.slice(1);
        link.href = path.posix.relative(path.posix.dirname(entry.html), target);
      }
      const snapshot = doc.querySelector('.snapshot');
      snapshot.textContent = snapshot.textContent.replace(' · exported ', ' · source revision dated ');
      addNotebookNavigation(doc, entry);
      return {html: '<!doctype html>\n' + doc.documentElement.outerHTML, title: doc.title};
    } finally { page.window.close(); }
  } finally { window.close(); }
}

function galleryIndex(manifest, entries) {
  const groups = Object.entries(TOPICS).map(([topic, [title, description]]) => {
    const notebooks = entries.filter(entry => entry.html.startsWith(topic + '/'));
    return `<section id="${topic}" class="topic"><header><h2>${title}</h2><p>${description}</p></header><ul>${notebooks.map(entry => `<li><a class="notebook-title" href="${escape(entry.html)}">${escape(entry.title)}</a></li>`).join('')}</ul></section>`;
  }).join('\n');
  return readFileSync(path.join(ROOT, 'gallery/index.html'), 'utf8')
    .replace('{{topics}}', groups)
    .replaceAll('{{repository}}', escape(manifest.repository))
    .replaceAll('{{revision}}', escape(manifest.revision));
}

async function main(inputs, output) {
  const manifest = JSON.parse(await fs.readFile(inputs, 'utf8'));
  const entries = [];
  await fs.mkdir(output, {recursive: true});
  for (const entry of manifest.notebooks) {
    assert.ok(TOPICS[entry.html.split('/')[0]], `Unknown gallery topic: ${entry.html}`);
    const rendered = await renderNotebook(manifest, entry);
    const destination = path.join(output, entry.html);
    await fs.mkdir(path.dirname(destination), {recursive: true});
    await fs.writeFile(destination, rendered.html);
    entries.push({html: entry.html, title: rendered.title, source_url: entry.source_url,
      source_sha256: entry.snapshot.sha256, claims: entry.snapshot.claims.length, diagrams: entry.snapshot.views.length});
    console.log(`Exported ${entry.html}`);
  }
  await fs.writeFile(path.join(output, 'index.html'), galleryIndex(manifest, entries));
  await fs.copyFile(path.join(ROOT, 'gallery/gallery.css'), path.join(output, 'gallery.css'));
  await fs.copyFile(path.join(ROOT, 'LICENSE'), path.join(output, 'LICENSE'));
  await fs.writeFile(path.join(output, '.nojekyll'), '');
  await fs.writeFile(path.join(output, 'manifest.json'), JSON.stringify({repository: manifest.repository, revision: manifest.revision, notebooks: entries}, null, 2) + '\n');
}

module.exports = {addNotebookNavigation, validateExport, galleryIndex, renderNotebook, rewriteReferences};
if (require.main === module) main(...process.argv.slice(2)).catch(error => { console.error(error); process.exitCode = 1; });
