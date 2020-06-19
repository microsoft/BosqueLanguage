FROM ubuntu:20.04

# Prepare development environment
ARG NODE_VERSION=14.x
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y curl
RUN curl --silent --location https://deb.nodesource.com/setup_$NODE_VERSION | bash -
RUN apt-get install -y nodejs \
    build-essential \
    clang-10 \
    git
RUN ln -s /usr/bin/clang-10 /usr/bin/clang
RUN ln -s /usr/bin/clang++-10 /usr/bin/clang++
RUN curl -s https://packagecloud.io/install/repositories/github/git-lfs/script.deb.sh | bash
RUN apt-get install -y git-lfs && \
    git lfs install

# Clone Bosque's sources
ARG BRANCH=master
ADD http://worldclockapi.com/api/json/utc/now timestamp.json
RUN git clone -b $BRANCH https://github.com/microsoft/BosqueLanguage.git bosque
# Copy language tools for VSCode integration (syntax highlighting)
RUN mkdir -p /root/.vscode-server/extensions && mv ./bosque/bosque-language-tools /root/.vscode-server/extensions
WORKDIR /bosque/impl
# Install Node packages
RUN npm install --global --silent typescript
RUN npm install --silent
# Make Bosque's exegen globally available
RUN npm run make-exe

WORKDIR /src

CMD ["/bin/bash"]
