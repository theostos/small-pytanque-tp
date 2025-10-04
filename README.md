# small-TP

TP for hands-on session at [AI and Maths conference](https://csd.ens.psl.eu/?ai-and-maths) (@PSL)
## Notebook

**To use the notebook, please start the server.**

<a target="_blank" href="https://colab.research.google.com/github/theostos/small-pytanque-tp/blob/main/tp.ipynb">
  <img src="https://colab.research.google.com/assets/colab-badge.svg" alt="Open In Colab"/>
</a>

## Server

### Install

You should setup a virtual environment:

```
pip install -r requirements.txt
```

then install [petanque/pytanque](https://github.com/LLM4Rocq/pytanque).


### Usage

server.py has two global variables (argparse does not work with gunicorn..):
- NUM_PET_SERVER (default value=4): the number of pet-servers to balance load.
- DICT_SECTION: binds sections names to source and description files.

First, start the `pet-server` (one instance per NUM_PET_SERVER, with ports starting from 8765, up to 8765 + NUM_PET_SERVER-1).

For example if NUM_PET_SERVER = 2, you need to start two pet servers:

```
pet-server -p 8765 & pet-server -p 8766
```

Then start the server using Gunicorn:

```
gunicorn -w 4 -b 0.0.0.0:5000 server:app
```
