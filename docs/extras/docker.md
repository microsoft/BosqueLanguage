## Using Bosque with VSCode and remote Docker server

To work with remote Docker instances you will need to install [Docker Desktop](https://www.docker.com/products/docker-desktop) and [Remote Development Extension Pack](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack) first.

After the installation, restart your VSCode and click the lower left icon `Open a remote Window` and then select `Reopen in container`.

After a few moments a new VSCode window will be opened. You are now communicating with the remote Docker server. 

More detailed information on developing inside containers can be found [here](https://code.visualstudio.com/docs/remote/containers).

## Manual Docker installation

Alternatively, you could also build and run Docker manually by entering these two commands:

`docker build --pull --rm -f Dockerfile -t bosquelanguage:latest .`

`docker run --rm -it  bosquelanguage:latest`

### Build arguments

To build Bosque from a specific branch use **BRANCH**.

#### Example 

```shell
docker build --build-arg BRANCH=my-other-branch --pull --rm -f Dockerfile -t bosquelanguage:latest .
```

To install a specific NodeJS version use **NODE_VERSION**.

#### Example

```shell
docker build --build-arg NODE_VERSION=14.x --pull --rm -f Dockerfile -t bosquelanguage:latest .
```
