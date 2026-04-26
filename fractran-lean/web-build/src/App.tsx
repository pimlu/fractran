import { useEffect, useRef, useState } from 'react';
import Button from '@mui/material/Button';
import Stack from '@mui/material/Stack';
import Typography from '@mui/material/Typography';
import Box from '@mui/material/Box';
import type { RunMessage, WorkerOutgoing } from './fractran.worker.ts';
import fractranWasmUrl from './wasm/fractran-web.wasm?url';

type Status = 'loading' | 'ready' | 'running' | 'error';

export default function App() {
  const wasmRef = useRef<ArrayBuffer | null>(null);
  const [status, setStatus] = useState<Status>('loading');
  const [errorMsg, setErrorMsg] = useState<string>('');
  const [output, setOutput] = useState<string>('');

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
    setOutput('');
    const worker = new Worker(
      new URL('./fractran.worker.ts', import.meta.url),
      { type: 'module' },
    );
    worker.onmessage = (e: MessageEvent<WorkerOutgoing>) => {
      const msg = e.data;
      switch (msg.type) {
        case 'stdout':
        case 'stderr':
          setOutput((prev) => prev + msg.text + '\n');
          break;
        case 'done':
          setStatus('ready');
          worker.terminate();
          break;
        case 'error':
          setErrorMsg(msg.message);
          setStatus('error');
          worker.terminate();
          break;
      }
    };
    // postMessage without a transfer list structured-clones the ArrayBuffer,
    // so wasmRef.current stays valid for future runs (no re-fetch).
    const initMsg: RunMessage = { type: 'run', wasmBinary };
    worker.postMessage(initMsg);
  };

  return (
    <Stack spacing={2} sx={{ p: 4, maxWidth: 720 }}>
      <Typography variant="h4">FRACTRAN</Typography>
      <Typography variant="body2">
        Phase 1 skeleton: runs the hardcoded Hamming demo from{' '}
        <code>MainRuntime.lean</code> in a Web Worker. Each click spawns a fresh
        Lean runtime; the WASM binary is fetched once and reused.
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
        {output || '(no output yet)'}
      </Box>
    </Stack>
  );
}
