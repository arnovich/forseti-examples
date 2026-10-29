const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const {pathToFileURL} = require('node:url');
const {chromium} = require('playwright');

async function main() {
  const root = path.resolve(__dirname, '../..');
  const temporary = await fs.mkdtemp(path.join(os.tmpdir(), 'glitnir-triptych-'));
  const browser = await chromium.launch({executablePath: process.env.GALLERY_CHROMIUM_EXECUTABLE || undefined});
  const context = await browser.newContext({
    viewport: {width: 1280, height: 720},
    deviceScaleFactor: 1,
    recordVideo: {dir: temporary, size: {width: 1280, height: 720}},
  });
  const page = await context.newPage();
  const video = page.video();
  try {
    await page.goto(pathToFileURL(path.join(__dirname, 'triptych-recording.html')).href);
    await page.waitForFunction(
      () => document.body.dataset.done === 'true',
      null,
      {timeout: 45000},
    );
  } finally {
    await page.close();
    await context.close();
    await browser.close();
  }
  const recorded = await video.path();
  const output = path.join(root, 'gallery/assets/triptych.webm');
  const result = spawnSync(process.env.FFMPEG || 'ffmpeg', [
    '-y', '-i', recorded, '-an', '-vf', 'fps=15', '-c:v', 'libvpx-vp9',
    '-crf', '38', '-b:v', '0', '-row-mt', '1', output,
  ], {encoding: 'utf8'});
  assert.equal(result.status, 0, result.stderr);
  const size = (await fs.stat(output)).size;
  assert.ok(size <= 8 * 1024 * 1024, `Recording is ${(size / 1024 / 1024).toFixed(1)} MiB; limit is 8 MiB`);
  console.log(`Wrote ${path.relative(root, output)} (${(size / 1024 / 1024).toFixed(1)} MiB)`);
  await fs.rm(temporary, {recursive: true, force: true});
}

main().catch(error => { console.error(error); process.exitCode = 1; });
