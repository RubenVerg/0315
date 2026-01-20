import run, { sequences } from './dist/lib.js';

const input = document.querySelector('#input');
const count = document.querySelector('#count');
const output = document.querySelector('#output');
const runB = document.querySelector('#run');
runB.addEventListener('click', async () => {
	const code = input.value;
	const max = Number.parseInt(count.value);
	output.innerHTML = '';
	try {
		await run(max, n => {
			output.textContent += n.toString() + ' ';
		}, '<playground code>', code);
	} catch (ex) {
		const p = document.createElement('pre');
		p.innerText = ex.message;
		output.appendChild(p);
	}
});
input.addEventListener('keyup', ev => {
	if (ev.key === 'Enter' && ev.ctrlKey) runB.click();
});

const seqs = document.querySelector('#sequences ul');
for (const [sequence, desc] of sequences.toSorted((a, b) => a[0] - b[0])) {
	const li = document.createElement('li');
	const a = document.createElement('a');
	a.href = `https://oeis.org/A${sequence.toString().padStart(6, '0')}`;
	const code = document.createElement('code');
	code.textContent = sequence.toString();
	a.appendChild(code);
	li.appendChild(a);
	if (desc !== undefined) li.appendChild(document.createTextNode(': ' + desc));
	seqs.appendChild(li);
}

const search = new URLSearchParams(window.location.search);

if (search.has('c')) try {
	count.value = Number.parseInt(search.get('c'));
} catch {}

if (search.has('p')) {
	input.value = atob(search.get('p'));
	if (search.has('r')) runB.click();
}

document.querySelector('#copy').addEventListener('click', async () => {
	const search = new URLSearchParams();
	search.set('p', btoa(input.value));
	search.set('c', Number.parseInt(count.value));
	const url = new URL(window.location.href);
	url.search = search.toString();
	try {
		await window.navigator.clipboard.write(url.toString());
	} catch {}
	window.history.replaceState(null, '', url.toString());
});
