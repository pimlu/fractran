/// <reference lib="webworker" />

import fractranModuleUrl from './wasm/fractran-web.js?url';

// Messages flowing between the main thread and this worker.
export interface RunMessage {
  type: 'run';
  wasmBinary: ArrayBuffer;
  cyclen: string;
  programSrc: string;
  inputSrc: string;
}

export type WorkerOutgoing =
  | { type: 'result'; text: string }
  | { type: 'stderr'; text: string }
  | { type: 'error'; message: string };

interface EmscriptenModule {
  callMain(args: string[]): number;
  ccall(
    name: string,
    returnType: 'number' | 'string' | null,
    argTypes: ('number' | 'string')[],
    args: unknown[],
  ): number;
  UTF8ToString(ptr: number): string;
  _free(ptr: number): void;
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
      printErr: (text) => post({ type: 'stderr', text }),
    });
    // MainWeb.main is `pure ()`; this just initializes the Lean runtime.
    instance.callMain([]);
    const ptr = instance.ccall(
      'fractran_run',
      'number',
      ['string', 'string', 'string'],
      [e.data.cyclen, e.data.programSrc, e.data.inputSrc],
    );
    const text = instance.UTF8ToString(ptr);
    instance._free(ptr);
    post({ type: 'result', text });
  } catch (err) {
    post({
      type: 'error',
      message: err instanceof Error ? err.message : String(err),
    });
  }
};
