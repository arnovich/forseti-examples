const assert = require('node:assert/strict');
const {test} = require('node:test');
const {JSDOM} = require('jsdom');
const {copyGalleryAssets, addNotebookNavigation, validateExport, galleryIndex, rewriteReferences} = require('../scripts/gallery/render.cjs');

test('export validation refuses missing claims, scripts and incomplete diagrams', () => {
  const entry = {snapshot: {sha256: 'abc', project_claims: [{name: 'first'}], views: []}};
  const valid = '<p>abc · Saved results, shown as recorded.</p><section id="cell-first">Open goal</section>';
  assert.doesNotThrow(() => validateExport(valid, entry));
  for (const html of [valid.replace('cell-first', 'lost'), valid.replace('shown as recorded', 'current'), valid + '<script>x()</script>', valid + '<p class="view-wait">Drawing</p>']) {
    assert.throws(() => validateExport(html, entry));
  }
});

test('an undrawn diagram is accepted only when declared unavailable and noted', () => {
  const drawn = '<section class="view-cell"><div class="view-body"><img src="data:image/svg+xml,x"></div></section>';
  const noted = '<section class="view-cell"><div class="note-line" data-tone="red">No drawing: failed</div></section>';
  const html = `<p>abc · Saved results, shown as recorded.</p>${drawn}${noted}`;
  const entry = errors => ({snapshot: {sha256: 'abc', project_claims: [], views: [{}, {}]}, diagram_errors: errors});
  assert.doesNotThrow(() => validateExport(html, entry(['1:9'])));
  assert.throws(() => validateExport(html, entry([])), /Diagram has no drawing/);
  assert.throws(() => validateExport(`<p>abc · Saved results, shown as recorded.</p>${drawn}<section class="view-cell"></section>`, entry(['1:9'])), /no note/);
});

test('gallery links survive a repository Pages prefix and escape notebook titles', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, [
    {html: 'basics/Test.html', title: '<img src=x>', source_url: 'https://github.com/owner/examples/blob/a/Test.lean'},
  ]);
  assert.ok(html.includes('href="basics/Test.html"'));
  assert.ok(html.includes('&lt;img src=x&gt;'));
  assert.ok(!html.includes('src=x>'));
  const dom = new JSDOM(html);
  try {
    const links = dom.window.document.querySelectorAll('.topic li a');
    assert.equal(links.length, 1);
    assert.equal(links[0].getAttribute('href'), 'basics/Test.html');
    assert.equal(links[0].textContent, '<img src=x>');
  } finally { dom.window.close(); }
});

test('known notebook cross-links survive export without rewriting external URLs', () => {
  const dom = new JSDOM('<a href="/?reference=ThreeState">Next</a><a href="https://other.invalid/?reference=ThreeState">External</a>');
  try {
    rewriteReferences(dom.window.document.body, [{snapshot: {file: 'ThreeState.lean'}, html: 'basics/ThreeState.html'}]);
    const links = dom.window.document.querySelectorAll('a');
    assert.equal(links[0].href, 'https://gallery.invalid/basics/ThreeState.html');
    assert.equal(links[1].href, 'https://other.invalid/?reference=ThreeState');
  } finally { dom.window.close(); }
});

test('notebook navigation preserves gallery and exact source links without changing content', () => {
  const dom = new JSDOM('<!doctype html><html><head></head><body><div class="app"><h1>Example</h1><p id="cell-first">Recorded claim</p></div></body></html>');
  const source = `https://github.com/owner/examples/blob/${'a'.repeat(40)}/examples/basics/A%22B.lean`;
  try {
    addNotebookNavigation(dom.window.document, {source_url: source, snapshot: {file: 'A"B.lean'}});
    const links = dom.window.document.querySelectorAll('.app > .gallery-nav a');
    assert.equal(links.length, 2);
    assert.equal(links[0].getAttribute('href'), '../index.html');
    assert.equal(links[1].getAttribute('href'), source);
    assert.equal(links[1].getAttribute('title'), 'View A"B.lean on GitHub');
    assert.equal(dom.window.document.querySelector('h1').textContent, 'Example');
    assert.equal(dom.window.document.getElementById('cell-first').textContent, 'Recorded claim');
    assert.equal(dom.window.document.querySelectorAll('script').length, 0);
  } finally { dom.window.close(); }
});


test('gallery provides related-product navigation without losing notebook entry points', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, []);
  const dom = new JSDOM(html);
  try {
    const doc = dom.window.document;
    assert.ok(doc.querySelector('nav[aria-label="Main navigation"] a[href="https://glitnir.gimlelabs.com/"]'));
    assert.ok(doc.querySelector('a[href="https://gimlelabs.com/"]'));
    assert.ok(doc.querySelector('a.start[href="basics/ScalarDecay.html"]'));
    assert.ok(doc.querySelector('nav[aria-label="Topics"] a[href="#pdes"]'));
    assert.ok(doc.querySelector('link[rel="icon"][href="assets/favicon.svg"]'));
    assert.equal(doc.querySelectorAll('h1').length, 1);
    assert.equal(doc.querySelectorAll('script').length, 0);
  } finally { dom.window.close(); }
});

test('gallery packages its local fonts, marks and font license for offline hosting', async () => {
  const fs = require('node:fs/promises');
  const os = require('node:os');
  const path = require('node:path');
  const output = await fs.mkdtemp(path.join(os.tmpdir(), 'forseti-gallery-assets-'));
  try {
    await copyGalleryAssets(output);
    for (const asset of ['gimle.svg', 'favicon.svg', 'inter-regular.ttf', 'inter-medium.ttf', 'LICENSE-Inter.txt']) {
      const source = await fs.readFile(path.join(__dirname, '../gallery/assets', asset));
      assert.deepEqual(await fs.readFile(path.join(output, 'assets', asset)), source);
    }
  } finally { await fs.rm(output, {recursive: true, force: true}); }
});
