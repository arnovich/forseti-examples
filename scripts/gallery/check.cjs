// Open the complete site in a real browser with scripts disabled and no network.
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const {pathToFileURL} = require('node:url');
const {chromium} = require('playwright');

async function main() {
  const root = path.resolve(process.argv[2] || '_site');
  const manifest = JSON.parse(await fs.readFile(path.join(root, 'manifest.json'), 'utf8'));
  const browser = await chromium.launch({executablePath: process.env.GALLERY_CHROMIUM_EXECUTABLE || undefined});
  const context = await browser.newContext({javaScriptEnabled: false, viewport: {width: 1100, height: 760}, deviceScaleFactor: 1});
  const network = [];
  await context.route(/^https?:/, route => { network.push(route.request().url()); return route.abort(); });
  const page = await context.newPage();
  await fs.mkdir(path.join(root, 'previews'), {recursive: true});
  try {
    for (const entry of manifest.notebooks) {
      await page.goto(pathToFileURL(path.join(root, entry.html)).href);
      assert.equal(await page.locator('h1').first().textContent(), entry.title);
      assert.equal(await page.locator('.view-cell').count(), entry.diagrams);
      assert.equal(await page.locator('.claim').count(), entry.claims);
      assert.equal(await page.locator('.katex-error,.view-wait,script').count(), 0);
      assert.ok(await page.locator('body').innerText().then(text => text.includes(entry.source_sha256)));
      const imagesOK = await page.locator('img').evaluateAll(images => images.every(image => image.complete && image.naturalWidth > 0));
      assert.ok(imagesOK, `Unloaded images: ${entry.html}`);
      for (const href of await page.locator('a[href]').evaluateAll(links => links.map(link => link.getAttribute('href')))) {
        if (!/^(https?:|mailto:|#)/.test(href)) await fs.access(path.resolve(root, path.dirname(entry.html), href.split('#')[0]));
      }
      if (['basics/ThreeState.html', 'circuits/CircuitProofs.html'].includes(entry.html)) {
        await page.locator('.view-cell').first().scrollIntoViewIfNeeded();
        await page.screenshot({path: path.join(root, 'previews', path.basename(entry.html, '.html') + '.png')});
      }
      console.log(`Browser checked ${entry.html}`);
    }
    for (const width of [1100, 390]) {
      await page.setViewportSize({width, height: 850});
      await page.goto(pathToFileURL(path.join(root, 'index.html')).href);
      assert.equal(await page.locator('.notebook-title').count(), manifest.notebooks.length);
      assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), 'Gallery overflows viewport');
      for (const href of await page.locator('a[href]').evaluateAll(links => links.map(link => link.getAttribute('href')))) {
        if (!/^(https?:|#)/.test(href)) await fs.access(path.join(root, href.split('#')[0]));
      }
      if (process.env.GALLERY_QA_DIRECTORY) {
        await fs.mkdir(process.env.GALLERY_QA_DIRECTORY, {recursive: true});
        await page.screenshot({path: path.join(process.env.GALLERY_QA_DIRECTORY, `gallery-${width}.png`), fullPage: true});
      }
    }
    assert.deepEqual(network, [], 'Exports must be readable offline');
  } finally { await browser.close(); }
}

main().catch(error => { console.error(error); process.exitCode = 1; });
