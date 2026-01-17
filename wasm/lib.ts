// @ts-self-types="./tinyapl.d.ts"
// @ts-ignore Import from web not supported
import { WASI, OpenFile, File, ConsoleStdout } from 'https://unpkg.com/@bjorn3/browser_wasi_shim@0.4.1/dist/index.js';
// @ts-ignore
import ghc_wasm_jsffi from './ghc_wasm_jsffi.js';

declare global {
	interface ImportMeta {
		resolve(specifier: string): string;
	}
}

const files = [
	new OpenFile(new File([], {})), // stdin
	ConsoleStdout.lineBuffered((msg: string) => console.log(`[WASI] ${msg}`)), // stdout
	ConsoleStdout.lineBuffered((msg: string) => console.warn(`[WASI] ${msg}`)), // stderr
];
const options = {};
const wasi = new WASI([], [], files, options);

const instanceExports = {};
const url = 'resolve' in import.meta ? import.meta.resolve('./0315.wasm') : './0315.wasm';
const { instance } = await WebAssembly.instantiateStreaming(fetch(url), {
	wasi_snapshot_preview1: (wasi as any).wasiImport,
	ghc_wasm_jsffi: ghc_wasm_jsffi(instanceExports),
});
Object.assign(instanceExports, instance.exports);

wasi.initialize(instance);
const exports = instance.exports as any;
await exports.hs_start();

export default async function run(maxCount: number, callback: (n: bigint) => void | PromiseLike<void>, path: string, code: string): Promise<void> {
	const r = await exports.run(maxCount, callback, path, code);
	if (r !== undefined) throw new Error(r);
}

export const sequences: [number, string | undefined][] = await exports.sequences();
