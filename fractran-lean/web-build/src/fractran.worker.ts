/// <reference lib="webworker" />

// Messages flowing between the main thread and this worker.
export interface RunMessage {
  type: 'run';
  wasmBinary: ArrayBuffer;
}

export type WorkerOutgoing =
  | { type: 'stdout'; text: string }
  | { type: 'stderr'; text: string }
  | { type: 'done' }
  | { type: 'error'; message: string };

interface EmscriptenModule {
  callMain(args: string[]): number;
}

interface EmscriptenModuleConfig {
  wasmBinary: ArrayBuffer;
  noInitialRun?: boolean;
  print?: (s: string) => void;
  printErr?: (s: string) => void;
}

type EmscriptenModuleFactory = (
  config: EmscriptenModuleConfig,
) => Promise<EmscriptenModule>;

import fractranModuleUrl from './wasm/fractran-web.js?url';

const ctx = self as unknown as DedicatedWorkerGlobalScope;
const post = (msg: WorkerOutgoing) => ctx.postMessage(msg);

async function loadFractranFactory(): Promise<EmscriptenModuleFactory> {
  const mod = (await import(/* @vite-ignore */ fractranModuleUrl)) as {
    default: EmscriptenModuleFactory;
  };
  return mod.default;
}

ctx.onmessage = async (e: MessageEvent<RunMessage>) => {
  if (e.data.type !== 'run') return;
  try {
    const factory = await loadFractranFactory();
    const instance = await factory({
      wasmBinary: e.data.wasmBinary,
      noInitialRun: true,
      print: (text) => post({ type: 'stdout', text }),
      printErr: (text) => post({ type: 'stderr', text }),
    });
    instance.callMain([]);
    post({ type: 'done' });
  } catch (err) {
    post({
      type: 'error',
      message: err instanceof Error ? err.message : String(err),
    });
  }
};
