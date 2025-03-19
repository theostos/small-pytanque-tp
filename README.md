# small-TP

## Install

You should setup a virtual env:

```
pip install -r requirements.txt
```

## Usage

server.py has three global variables (argparse does not work with gunicorn..):
- NUM_PET_SERVER (default value=4), number of pet-servers to balance load.
- SRC_FILE (default to "example/ex1.v"), src file used.
- DESCR_FILE (default to "example/ex1.json"), description of theorems in SRC_FILE.

First start `pet-server` (one for each NUM_PET_SERVER, with ports starting from 8765, up to 8765 + NUM_PET_SERVER-1)

then to start the server (gunicorn):

```
gunicorn -w 4 -b 0.0.0.0:5000 server:app
```
