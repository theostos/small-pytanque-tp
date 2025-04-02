# small-TP

## Notebook

<a target="_blank" href="https://colab.research.google.com/github/theostos/small-pytanque-tp/blob/main/notebook.ipynb">
  <img src="https://colab.research.google.com/assets/colab-badge.svg" alt="Open In Colab"/>
</a>

## Server

### Install

You should setup a virtual env:

```
pip install -r requirements.txt
```

### Usage

server.py has two global variables (argparse does not work with gunicorn..):
- NUM_PET_SERVER (default value=4), number of pet-servers to balance load.
- DICT_SECTION, binding sections names to source and description files.

First start `pet-server` (one for each NUM_PET_SERVER, with ports starting from 8765, up to 8765 + NUM_PET_SERVER-1)

then to start the server (gunicorn):

```
gunicorn -w 4 -b 0.0.0.0:5000 server:app
```
