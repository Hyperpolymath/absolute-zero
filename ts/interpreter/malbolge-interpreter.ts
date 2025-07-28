// A minimal Malbolge VM in TypeScript
export async function runMalbolge(src: string): Promise<string> {
    // … your existing interpreter logic, typed …
    // return the program’s output
    return '…';
}

(async () => {
    const resp = await fetch('data/malbolge/nop.mlg');
    const src = await resp.text();
    const out = await runMalbolge(src);
    console.log('Malbolge output:', out);
})();
