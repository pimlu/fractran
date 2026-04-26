import { useEffect, useRef, useState } from 'react';
import Button from '@mui/material/Button';
import Stack from '@mui/material/Stack';
import Typography from '@mui/material/Typography';
import Box from '@mui/material/Box';
import type { RunMessage, WorkerOutgoing } from './fractran.worker.ts';
import fractranWasmUrl from './wasm/fractran-web.wasm?url';

type Status = 'loading' | 'ready' | 'running' | 'error';

// Hamming program from MainRuntime.lean, in the JsBridge wire format.
// Layout: cyclen fuel numFractions [for each: numFactorCount p e... denFactorCount p e...]
//         initFactorCount p e ...
//
// Fractions: 33/20, 5/11, 13/10, 1/5, 2/3, 10/7, 7/2
function buildHammingInput(): string {
  const tokens: bigint[] = [
    2n, 1_000_000n, 7n,
    // 33/20 = (3*11) / (2^2 * 5)
    2n, 3n, 1n, 11n, 1n,   2n, 2n, 2n, 5n, 1n,
    // 5/11
    1n, 5n, 1n,            1n, 11n, 1n,
    // 13/10 = 13 / (2*5)
    1n, 13n, 1n,           2n, 2n, 1n, 5n, 1n,
    // 1/5
    0n,                    1n, 5n, 1n,
    // 2/3
    1n, 2n, 1n,            1n, 3n, 1n,
    // 10/7 = (2*5) / 7
    2n, 2n, 1n, 5n, 1n,    1n, 7n, 1n,
    // 7/2
    1n, 7n, 1n,            1n, 2n, 1n,
    // init: 2^(2^128 - 1)
    1n, 2n, (1n << 128n) - 1n,
  ];
  return tokens.join(' ');
}

interface DecodedOk {
  kind: 'ok';
  halted: boolean;
  steps: bigint;
  factors: Map<bigint, bigint>;
}
interface DecodedErr {
  kind: 'err';
  reason: string;
}

function decodeResult(text: string): DecodedOk | DecodedErr {
  const parts = text.trim().split(/\s+/);
  if (parts[0] !== 'OK') return { kind: 'err', reason: text };
  const halted = parts[1] === '1';
  const steps = BigInt(parts[2] ?? '0');
  const count = Number(parts[3] ?? '0');
  const factors = new Map<bigint, bigint>();
  for (let i = 0; i < count; i++) {
    const p = BigInt(parts[4 + i * 2] ?? '0');
    const e = BigInt(parts[5 + i * 2] ?? '0');
    factors.set(p, e);
  }
  return { kind: 'ok', halted, steps, factors };
}

export default function App() {
  const wasmRef = useRef<ArrayBuffer | null>(null);
  const [status, setStatus] = useState<Status>('loading');
  const [errorMsg, setErrorMsg] = useState<string>('');
  const [decoded, setDecoded] = useState<DecodedOk | DecodedErr | null>(null);

  useEffect(() => {
    let cancelled = false;
    void (async () => {
      try {
        const res = await fetch(fractranWasmUrl);
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        const buf = await res.arrayBuffer();
        if (cancelled) return;
        wasmRef.current = buf;
        setStatus('ready');
      } catch (err) {
        if (cancelled) return;
        setErrorMsg(err instanceof Error ? err.message : String(err));
        setStatus('error');
      }
    })();
    return () => {
      cancelled = true;
    };
  }, []);

  const run = () => {
    const wasmBinary = wasmRef.current;
    if (!wasmBinary) return;
    setStatus('running');
    setDecoded(null);
    const worker = new Worker(
      new URL('./fractran.worker.ts', import.meta.url),
      { type: 'module' },
    );
    worker.onmessage = (e: MessageEvent<WorkerOutgoing>) => {
      const msg = e.data;
      switch (msg.type) {
        case 'result':
          setDecoded(decodeResult(msg.text));
          setStatus('ready');
          worker.terminate();
          break;
        case 'stderr':
          // eslint-disable-next-line no-console
          console.warn('[worker stderr]', msg.text);
          break;
        case 'error':
          setErrorMsg(msg.message);
          setStatus('error');
          worker.terminate();
          break;
      }
    };
    const initMsg: RunMessage = {
      type: 'run',
      wasmBinary,
      programInput: buildHammingInput(),
    };
    worker.postMessage(initMsg);
  };

  return (
    <Stack spacing={2} sx={{ p: 4, maxWidth: 720 }}>
      <Typography variant="h4">FRACTRAN</Typography>
      <Typography variant="body2">
        Phase 2a: passes a hardcoded Hamming program from JS to a Lean
        <code> @[export]</code> function via emscripten ccall, decodes the
        wire-format result. Phase 2b will add a real parser; 2c the UI.
      </Typography>
      <Stack direction="row" spacing={2} alignItems="center">
        <Button
          variant="contained"
          onClick={run}
          disabled={status !== 'ready'}
        >
          {status === 'loading'
            ? 'Loading WASM…'
            : status === 'running'
              ? 'Running…'
              : 'Run Hamming demo'}
        </Button>
        {status === 'error' && (
          <Typography color="error" variant="body2">
            {errorMsg}
          </Typography>
        )}
      </Stack>
      <Box
        component="pre"
        sx={{
          p: 2,
          bgcolor: 'grey.100',
          borderRadius: 1,
          minHeight: 200,
          fontSize: 13,
          overflow: 'auto',
        }}
      >
        {decoded === null
          ? '(no result yet)'
          : decoded.kind === 'err'
            ? `error: ${decoded.reason}`
            : [
                `halted: ${decoded.halted}`,
                `steps: ${decoded.steps.toString()}`,
                `final state:`,
                ...[...decoded.factors.entries()].map(
                  ([p, e]) => `  ${p}^${e}`,
                ),
                ``,
                `Hamming weight (exponent of 13): ${
                  decoded.factors.get(13n)?.toString() ?? '(missing)'
                }`,
              ].join('\n')}
      </Box>
    </Stack>
  );
}
