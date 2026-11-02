/* Typeset the built wiki's actual formulas with its pinned MathJax release. */
const fs = require('node:fs');
const path = require('node:path');
const root = process.env.WIKI_MATHJAX_ROOT;
const {mathjax} = require(path.join(root, 'js/mathjax.js'));
const {TeX} = require(path.join(root, 'js/input/tex.js'));
const {SVG} = require(path.join(root, 'js/output/svg.js'));
const {liteAdaptor} = require(path.join(root, 'js/adaptors/liteAdaptor.js'));
const {RegisterHTMLHandler} = require(path.join(root, 'js/handlers/html.js'));
const {AllPackages} = require(path.join(root, 'js/input/tex/AllPackages.js'));

const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
let errors = [];
const tex = new TeX({
  packages: AllPackages.filter(name => name !== 'noundefined'),
  formatError(jax, error) {
    errors.push(error.message);
    return jax.formatError(error);
  },
});
const document = mathjax.document('', {InputJax: tex, OutputJax: new SVG({fontCache: 'none'})});
const formulas = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const checked = new Set();
const problems = [];
for (const formula of formulas) {
  const key = JSON.stringify([formula.tex, formula.display]);
  if (checked.has(key)) continue;
  checked.add(key);
  errors = [];
  try {
    const output = adaptor.outerHTML(document.convert(formula.tex, {display: formula.display}));
    if (errors.length || /data-mjx-error|mjx-merror/.test(output)) {
      problems.push({...formula, errors: errors.length ? errors : ['MathJax emitted an error element']});
    }
  } catch (error) {
    problems.push({...formula, errors: [String(error.message || error)]});
  }
}
console.log(`${formulas.length} published formulas; ${checked.size} distinct formulas typeset; ${problems.length} error(s)`);
for (const problem of problems.slice(0, 40)) console.log(JSON.stringify(problem));
fs.writeFileSync(process.env.WIKI_MATH_REPORT || 'wiki-math-report.json', JSON.stringify(problems, null, 2));
if (problems.length) process.exitCode = 1;
