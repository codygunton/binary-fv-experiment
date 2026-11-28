# Vendored files

Pinned third-party files used offline by the viewers in this directory. Do not edit them;
replace a file only together with its line here.

| File | Version | Source | sha256 |
|---|---|---|---|
| `pixi.min.js` | PixiJS 8.23.0 | `dist/pixi.min.js` of the npm tarball `https://registry.npmjs.org/pixi.js/-/pixi.js-8.23.0.tgz` (tarball sha256 `e0f016f60872f81449940b00bd359017c4de1a7071cdc2a6272325d9aa48689a`, npm integrity `sha512-RkWSwo+mAR0d7MKnJ20IjKkWGPdFh1C0adBRYYLa+SGdxTfbrr6RnQyZZRwjBaG/bDAIQqgBcTBbiNsN6iKFVQ==`) | `a2c8ff6d25df3c712e87c7e4a2ddd9e2e2387e2fba01ee9f26d935ed183c0a3b` |
| `d3.min.js` | D3 7.9.0 | https://d3js.org | `f2094bbf6141b359722c4fe454eb6c4b0f0e42cc10cc7af921fc158fceb86539` |
| `d3-flamegraph.min.js`, `d3-flamegraph.css` | d3-flame-graph | flamegraph page (`index.html`) | `1846f1e636ed1bd2c32fc87d1e24d63aff7e4f18629b4bbd819351f09ea22353` (js) |

`graph.html` (the proof graph) uses `d3.min.js` for zoom, scales, quadtrees and the HTML panels,
and `pixi.min.js` (global `PIXI`) for all drawing, through WebGL.
