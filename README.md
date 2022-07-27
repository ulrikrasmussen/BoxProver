# Building with Stack

To build locally, you first need to install Stack.
Follow the instructions at https://docs.haskellstack.org/en/stable/README/

Then execute

    stack build


# Building and running with Docker

The provided `Dockerfile` will build a small image for easy deployment and sandboxing.
Build it using the command

    docker build -t ulrikrasmussen/boxprover .

Run the image in a container using

    docker run --rm -it ulrikrasmussen/boxprover --ulimit nofile=1024:104875 -p 8000:8000 [public-url]

where `public-url` is an optional argument that specifies the public URL that the application will be accessed at.
It defaults to `http://localhost:8000`.

When the container is running, the application can be accessed in a browser by navigating to http://localhost:8000.

**Note**: The `--ulimit` argument is needed to work around a performance issue due to the default maximum number of file descriptors being quite high in Docker containers and inefficiencies in the implementation of [createProcess](https://hackage.haskell.org/package/process-1.6.10.0/docs/System-Process.html#v:createProcess) with `close_fds=True`.
