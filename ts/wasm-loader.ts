// loads & instantiates perf-sandbox.wasm
export async function initWasm(): Promise<void> {
  const res = await fetch('wasm/perf-sandbox.wasm');
  const buf = await res.arrayBuffer();
  const { instance } = await WebAssembly.instantiate(buf, {});
  console.log('WASM double(7):', (instance.exports as any).double(7));
}

initWasm().catch(console.error);
