#!/usr/bin/env python3
"""Starts FsAutoComplete on the sample project and checks that it understands polymorphic variants:
hovers show variant types, the valid file has no errors and a wrong tag is reported.

Usage: lsp_smoke.py <path to fsautocomplete.dll> <sample project folder>
"""

import json
import os
import pathlib
import queue
import subprocess
import sys
import threading
import time

fsac_dll = sys.argv[1]
project = pathlib.Path(sys.argv[2]).resolve()
source_path = project / "Colours.fs"
source_uri = source_path.as_uri()
source = source_path.read_text()

env = dict(os.environ, DOTNET_ROLL_FORWARD="LatestMajor", DOTNET_ROLL_FORWARD_TO_PRERELEASE="1")
server = subprocess.Popen(
    ["dotnet", fsac_dll],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=open(os.environ.get("FSAC_LOG", os.devnull), "wb"),
    env=env,
    cwd=project,
)

messages = queue.Queue()


def read_messages():
    while True:
        length = None
        while True:
            line = server.stdout.readline()
            if not line:
                return
            line = line.decode().strip()
            if not line:
                break
            name, _, value = line.partition(":")
            if name.lower() == "content-length":
                length = int(value)
        messages.put(json.loads(server.stdout.read(length)))


threading.Thread(target=read_messages, daemon=True).start()

next_id = 0
responses = {}
diagnostics = []


def send(message):
    body = json.dumps(message).encode()
    server.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
    server.stdin.flush()


def notify(method, params):
    send({"jsonrpc": "2.0", "method": method, "params": params})


def pump(timeout):
    try:
        message = messages.get(timeout=timeout)
    except queue.Empty:
        return
    if os.environ.get("SMOKE_DEBUG"):
        print("<-", message.get("method"), str(message.get("params", ""))[:150], file=sys.stderr)
    if "id" in message and "method" in message:
        # A request from the server (configuration, capability registration, progress): accept it.
        send({"jsonrpc": "2.0", "id": message["id"], "result": None})
    elif "id" in message:
        responses[message["id"]] = message
    elif message.get("method") == "textDocument/publishDiagnostics" and message["params"]["uri"].endswith("/Colours.fs"):
        diagnostics.append(message["params"]["diagnostics"])


def request(method, params, timeout=120):
    global next_id
    next_id += 1
    send({"jsonrpc": "2.0", "id": next_id, "method": method, "params": params})
    deadline = time.time() + timeout
    while next_id not in responses:
        if time.time() > deadline:
            sys.exit(f"FAIL: no response to {method}")
        pump(1)
    return responses.pop(next_id)


def wait_until(description, condition, timeout=180):
    deadline = time.time() + timeout
    while time.time() < deadline:
        result = condition()
        if result:
            return result
        pump(1)
    sys.exit(f"FAIL: {description() if callable(description) else description}")


def position_of(text, needle):
    offset = source.index(text) + text.index(needle)
    line = source.count("\n", 0, offset)
    return {"line": line, "character": offset - (source.rfind("\n", 0, offset) + 1)}


def hover_text(text, needle):
    response = request(
        "textDocument/hover", {"textDocument": {"uri": source_uri}, "position": position_of(text, needle)}
    )
    result = response.get("result") or {}
    contents = result.get("contents", "")
    return json.dumps(contents)


def expect_hover(text, needle, expected):
    last = [""]

    def contains_expected():
        last[0] = hover_text(text, needle)
        return expected in last[0] and last[0]

    found = wait_until(
        lambda: f"hover on '{needle}' never contained {expected!r}; last hover: {last[0]}", contains_expected
    )
    print(f"ok: hover on '{needle}' shows {expected!r}")
    return found


def errors(diags):
    return [d["message"] for d in diags if d.get("severity") == 1]


request(
    "initialize",
    {
        "processId": os.getpid(),
        "rootUri": project.as_uri(),
        "capabilities": {
            "textDocument": {
                "hover": {"contentFormat": ["markdown", "plaintext"]},
                "publishDiagnostics": {"relatedInformation": True},
            }
        },
        "initializationOptions": {"AutomaticWorkspaceInit": True},
    },
)
notify("initialized", {})
notify(
    "textDocument/didOpen",
    {"textDocument": {"uri": source_uri, "languageId": "fsharp", "version": 1, "text": source}},
)

expect_hover("let red = `Red", "red", "`Red")
expect_hover("let describe colour", "describe", "`Rgb")

wait_until("no diagnostics were published for the valid file", lambda: diagnostics)
time.sleep(5)
pump(1)
if errors(diagnostics[-1]):
    sys.exit(f"FAIL: valid file has errors: {errors(diagnostics[-1])}")
print("ok: valid file has no errors")

diagnostics.clear()
notify(
    "textDocument/didChange",
    {
        "textDocument": {"uri": source_uri, "version": 2},
        "contentChanges": [{"text": source + "\nlet bad = paint `Blue\n"}],
    },
)
reported = wait_until(
    "the wrong tag `Blue was not reported",
    lambda: next((e for diags in diagnostics for e in errors(diags) if "Blue" in e), None),
)
print(f"ok: wrong tag reported: {reported.splitlines()[0]}")

request("shutdown", None)
notify("exit", None)
server.wait(timeout=30)
print("PASS")
