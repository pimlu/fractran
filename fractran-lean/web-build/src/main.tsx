import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import App from './App.tsx';

const container = document.getElementById('app');
if (!container) throw new Error('missing #app root');

createRoot(container).render(
  <StrictMode>
    <App />
  </StrictMode>,
);
