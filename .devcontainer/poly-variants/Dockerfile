# Dev container image for trying polymorphic variants: the F# compiler from this branch, and an FsAutoComplete
# (the language server behind Ionide) built against its FSharp.Compiler.Service.
#
#   docker build -f .devcontainer/poly-variants/Dockerfile -t fsharp-poly-variants-demo .

ARG FSAC_VERSION=v0.85.2

# The build stages produce IL only, so they run on the build machine's platform for every target platform.
FROM --platform=$BUILDPLATFORM mcr.microsoft.com/dotnet/sdk:10.0 AS compiler
WORKDIR /src/fsharp
COPY . .
ENV BUILDING_USING_DOTNET=true
RUN ./eng/common/dotnet.sh --version \
 && export PATH=/src/fsharp/.dotnet:$PATH \
 && dotnet build src/fsc/fscProject/fsc.fsproj -c Release \
 && dotnet build src/fsi/fsiProject/fsi.fsproj -c Release \
 && dotnet build src/Compiler/FSharp.Compiler.Service.fsproj -c Release -f netstandard2.0

FROM --platform=$BUILDPLATFORM mcr.microsoft.com/dotnet/sdk:10.0 AS fsac
ARG FSAC_VERSION
RUN git clone --depth 1 --branch $FSAC_VERSION https://github.com/ionide/FsAutoComplete.git /src/fsac
COPY .devcontainer/poly-variants/build-fsac.sh .devcontainer/poly-variants/UseLocalFcs.targets .devcontainer/poly-variants/fsac.patch /src/fsac-build/
COPY --from=compiler /src/fsharp/artifacts/bin/FSharp.Compiler.Service/Release/netstandard2.0 /src/fcs
RUN /src/fsac-build/build-fsac.sh /src/fsac /src/fcs /out/fsautocomplete

FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04
COPY global.json /tmp/global.json
RUN apt-get update \
 && apt-get install -y --no-install-recommends libicu74 python3 \
 && rm -rf /var/lib/apt/lists/* \
 && curl -sSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh \
 && bash /tmp/dotnet-install.sh --jsonfile /tmp/global.json --install-dir /usr/share/dotnet \
 && ln -s /usr/share/dotnet/dotnet /usr/local/bin/dotnet \
 && rm /tmp/dotnet-install.sh /tmp/global.json

COPY --from=compiler /src/fsharp/artifacts/bin/fsc/Release/net11.0 /opt/fsharp-pv/fsc
COPY --from=compiler /src/fsharp/artifacts/bin/fsi/Release/net11.0 /opt/fsharp-pv/fsi
COPY --from=fsac /out/fsautocomplete /opt/fsharp-pv/fsautocomplete
COPY .devcontainer/poly-variants/smoke-test /opt/fsharp-pv/smoke-test
RUN printf '#!/bin/sh\nexec dotnet /opt/fsharp-pv/fsi/fsi.dll --langversion:preview "$@"\n' > /usr/local/bin/fsi-pv \
 && chmod +x /usr/local/bin/fsi-pv /opt/fsharp-pv/smoke-test/run.sh

# MSBuild reads environment variables as properties, so every F# project builds with the patched compiler.
# FsAutoComplete targets .NET 10 and rolls forward onto the .NET 11 prerelease runtime.
ENV DOTNET_ROOT=/usr/share/dotnet \
    DOTNET_NOLOGO=1 \
    DOTNET_CLI_TELEMETRY_OPTOUT=1 \
    DOTNET_ROLL_FORWARD_TO_PRERELEASE=1 \
    DotnetFscCompilerPath=/opt/fsharp-pv/fsc/fsc.dll

# VS Code runs as root, the user that owns the checked-out workspace both in Codespaces and with local Docker
LABEL devcontainer.metadata='[{ \
  "remoteUser": "root", \
  "customizations": { "vscode": { \
    "extensions": [ "Ionide.Ionide-fsharp" ], \
    "settings": { \
      "FSharp.fsac.netCoreDllPath": "/opt/fsharp-pv/fsautocomplete/fsautocomplete.dll", \
      "FSharp.enableAnalyzers": false \
    } \
  } } \
}]'
