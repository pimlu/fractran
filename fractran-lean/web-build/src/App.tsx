import { useEffect, useRef, useState } from 'react';
import Button from '@mui/material/Button';
import Stack from '@mui/material/Stack';
import Typography from '@mui/material/Typography';
import TextField from '@mui/material/TextField';
import Box from '@mui/material/Box';
import type { RunMessage, WorkerOutgoing } from './fractran.worker.ts';
import { buildWireInput } from './wire.ts';
import fractranWasmUrl from './wasm/fractran-web.wasm?url';

type Status = 'loading' | 'ready' | 'running' | 'error';

const DEFAULT_PROGRAM = `3*11 % 2^2*5
5 % 11
13 % 2*5
1 % 5
2 % 3
2*5 % 7
7 % 2`;
const DEFAULT_INPUT = '[2, 2^128 - 1]';
const DEFAULT_CYCLEN = '2';

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
  const workerRef = useRef<Worker | null>(null);
  const [status, setStatus] = useState<Status>('loading');
  const [errorMsg, setErrorMsg] = useState<string>('');
  const [decoded, setDecoded] = useState<DecodedOk | DecodedErr | null>(null);

  const [programSrc, setProgramSrc] = useState(DEFAULT_PROGRAM);
  const [inputSrc, setInputSrc] = useState(DEFAULT_INPUT);
  const [cyclenSrc, setCyclenSrc] = useState(DEFAULT_CYCLEN);

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

  const stop = () => {
    if (workerRef.current) {
      workerRef.current.terminate();
      workerRef.current = null;
    }
    setStatus('ready');
  };

  const run = () => {
    const wasmBinary = wasmRef.current;
    if (!wasmBinary) return;
    setErrorMsg('');
    setDecoded(null);

    let programInput: string;
    try {
      programInput = buildWireInput({
        cyclen: BigInt(cyclenSrc),
        programSrc,
        inputSrc,
      });
    } catch (err) {
      setErrorMsg(err instanceof Error ? err.message : String(err));
      setStatus('error');
      return;
    }

    setStatus('running');
    const worker = new Worker(
      new URL('./fractran.worker.ts', import.meta.url),
      { type: 'module' },
    );
    workerRef.current = worker;
    worker.onmessage = (e: MessageEvent<WorkerOutgoing>) => {
      const msg = e.data;
      switch (msg.type) {
        case 'result':
          setDecoded(decodeResult(msg.text));
          setStatus('ready');
          worker.terminate();
          workerRef.current = null;
          break;
        case 'stderr':
          // eslint-disable-next-line no-console
          console.warn('[worker stderr]', msg.text);
          break;
        case 'error':
          setErrorMsg(msg.message);
          setStatus('error');
          worker.terminate();
          workerRef.current = null;
          break;
      }
    };
    const initMsg: RunMessage = { type: 'run', wasmBinary, programInput };
    worker.postMessage(initMsg);
  };

  const isRunning = status === 'running';
  const canStart = status === 'ready' || status === 'error';

  return (
    <Stack spacing={2} sx={{ p: 4, maxWidth: 720 }}>
      <Typography variant="h4">FRACTRAN</Typography>
      <Typography variant="body2">
        Write a FRACTRAN program (fractions separated by commas or newlines) and
        an initial state. Initial state is either an integer expression (will be
        prime-factorized) or a list of <code>[prime, value]</code> pairs.
      </Typography>

      <TextField
        label="Program"
        multiline
        minRows={6}
        value={programSrc}
        onChange={(e) => setProgramSrc(e.target.value)}
        slotProps={{ htmlInput: { style: { fontFamily: 'monospace' } } }}
      />
      <TextField
        label="Initial state"
        value={inputSrc}
        onChange={(e) => setInputSrc(e.target.value)}
        slotProps={{ htmlInput: { style: { fontFamily: 'monospace' } } }}
      />
      <TextField
        label="Cycle length"
        value={cyclenSrc}
        onChange={(e) => setCyclenSrc(e.target.value)}
        sx={{ width: 200 }}
      />

      <Stack direction="row" spacing={2} alignItems="center">
        {isRunning ? (
          <Button variant="contained" color="error" onClick={stop}>
            Stop
          </Button>
        ) : (
          <Button variant="contained" onClick={run} disabled={!canStart}>
            {status === 'loading' ? 'Loading WASM…' : 'Run'}
          </Button>
        )}
        {errorMsg && (
          <Typography color="error" variant="body2" sx={{ whiteSpace: 'pre-wrap' }}>
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
          ? isRunning
            ? '(running…)'
            : '(no result yet)'
          : decoded.kind === 'err'
            ? `error: ${decoded.reason}`
            : [
                `halted: ${decoded.halted}`,
                `steps: ${decoded.steps.toString()}`,
                `final state:`,
                ...[...decoded.factors.entries()].map(
                  ([p, e]) => `  ${p}^${e}`,
                ),
              ].join('\n')}
      </Box>
    </Stack>
  );
}
