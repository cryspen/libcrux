const fs = require('fs');

let lemmas = fs.readFileSync('RwLemmas.fst').toString();
let template_lines =
    lemmas
    .split('// START TEMPLATE')[1]
    .split('// END TEMPLATE')[0]
    .split('\n').map(x => x.trim());

let template = template_lines.join('\n');

let sizes = ['8', '16', '32', '64'];

let replace = (str, from_size, to_sign, to_size) =>
    str
    .replaceAll(`u${from_size}`, `${to_sign ? 'u' : 'i'}${to_size}`)
    .replaceAll(`UInt${from_size}`, `${to_sign ? 'U' : ''}Int${to_size}`)
    .replaceAll(`uint_to`, `${to_sign ? 'u' : ''}int_to`);

let all = "";
for(let n1 of sizes) {
    for(let s1 of [true, false]) {
        let s = template;
        console.log({n1, s1});
        s = replace(s, 8, s1, n1);
        all += s;
    }
}

let generated_lines = [...new Set(all.split('\n'))];
let names = generated_lines.map(x => x.split(' ')[1]).filter(x => x);
let generated = generated_lines.filter(x => !template_lines.includes(x)).join('\n');

generated += '\nlet rw_integers_list0 = [' + names.map(n => '`' + n).join(';') + ']';

let before = lemmas
    .split('// START GENERATED')[0];

let after = lemmas
    .split('// END GENERATED')[1];

fs.writeFileSync('RwLemmas.fst', before + '// START GENERATED\n' + generated + '\n// END GENERATED' + after);

