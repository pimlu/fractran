#!/usr/bin/python
import http.server
import socketserver

PORT = 8000

Handler = http.server.SimpleHTTPRequestHandler
Handler.extensions_map.update({
    '.wasm': 'application/wasm',
})
with socketserver.TCPServer(("127.0.0.1", PORT), Handler) as httpd:
    print("serving at port", PORT)
    httpd.serve_forever()
