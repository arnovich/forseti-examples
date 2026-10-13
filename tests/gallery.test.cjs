const assert = require('node:assert/strict');
const {test} = require('node:test');
const {JSDOM} = require('jsdom');
const {validateExport, galleryIndex, rewriteReferences} = require('../scripts/gallery/render.cjs');

test('export validation refuses missing claims, scripts and incomplete diagrams', () => {
  const entry = {snapshot: {sha256: 'abc', claims: [{name: 'first'}], views: []}};
  const valid = '<p>abc</p><section id="cell-first">Open goal</section>';
  assert.doesNotThrow(() => validateExport(valid, entry));
  for (const html of [valid.replace('cell-first', 'lost'), valid + '<script>x()</script>', valid + '<p class="view-wait">Drawing</p>']) {
    assert.throws(() => validateExport(html, entry));
  }
});

test('gallery links survive a repository Pages prefix and escape notebook titles', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, [
    {html: 'basics/Test.html', title: '<img src=x>', source_url: 'https://github.com/owner/examples/blob/a/Test.lean'},
  ]);
  assert.ok(html.includes('href="basics/Test.html"'));
  assert.ok(html.includes('&lt;img src=x&gt;'));
  assert.ok(!html.includes('src=x>'));
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
