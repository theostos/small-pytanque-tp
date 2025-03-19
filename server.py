import json
from pytanque import Pytanque, State
from flask import Flask, request, jsonify

app = Flask(__name__)

# Configuration parameters
NUM_PET_SERVER = 4
SRC_FILE = "example/ex1.v"
DESCR_FILE = "example/ex1.json"

# Global index to balance load across pet servers
server_idx_counter = 0

# Initialize Pytanque instances for each server (assumed to run on ports 8765, 8766, ..., etc.)
pytanques = [Pytanque("127.0.0.1", 8765 + k) for k in range(NUM_PET_SERVER)]
for pet in pytanques:
    pet.connect()

# Load theorem descriptions from the JSON file
with open(DESCR_FILE, 'r') as file:
    descr_content = json.load(file)

@app.route('/login', methods=['GET'])
def login():
    """
    Return a server index (integer in 0 .. NUM_PET_SERVER-1) to help balance the load across pet servers.

    Returns:
            - status_code: HTTP status (200 on success)
            - output: the assigned server index
    """
    global server_idx_counter
    try:
        assigned_idx = server_idx_counter
        server_idx_counter = (server_idx_counter + 1) % NUM_PET_SERVER
        return jsonify({"status_code": 200, "output": assigned_idx})
    except Exception as e:
        return jsonify({"status_code": 500, "output": str(e)})

@app.route('/start_thm', methods=['POST'])
def start_thm():
    """
    Start a theorem by selecting a theorem based on its index.

    Expects:
        - idx (int): the index of the theorem in the description file.
        - login (int): the server index assigned from /login.

    Returns:
            - status_code: 200 on success
            - output: A dictionary containing:
                - state: The initial proof state (in JSON format)
                - goals: A list of pretty-printed goals
    """
    try:
        data = request.get_json()
        thm_idx = data['idx']
        login_idx = data['login']
        thm_name = descr_content[thm_idx]['name']

        worker = pytanques[login_idx]
        state = worker.start(file=SRC_FILE, thm=thm_name)
        goals = worker.goals(state)
        pretty_goals = [goal.pp for goal in goals]
        output = {"state": state.to_json(), "goals": pretty_goals}
        return jsonify({"status_code": 200, "output": output})
    except Exception as e:
        return jsonify({"status_code": 500, "output": str(e)})

@app.route('/run_tac', methods=['POST'])
def run_tac():
    """
    Execute a given tactic on the current proof state.

    Expects:
        - state: the current proof state.
        - tactic: the tactic command to execute.
        - login: the server index assigned from /login.

    Returns:
            - status_code
            - output:
                - state: new proof state
                - goals: goals
    """
    try:
        data = request.get_json()
        current_state = State.from_json(data['state'])
        tactic = data['tactic']
        login_idx = data['login']

        worker = pytanques[login_idx]
        new_state = worker.run_tac(current_state, tactic, verbose=False, timeout=10)
        goals = worker.goals(new_state)
        goals = [goal.pp for goal in goals]
        output = {"state": new_state.to_json(), "goals": goals}
        return jsonify({"status_code": 200, "output": output})
    except Exception as e:
        return jsonify({"status_code": 500, "output": str(e)})

@app.route('/get_thms', methods=['GET'])
def get_thms():
    """
    Retrieve the list of theorem descriptions from the description file.

    Returns:
            - status_code
            - output: the content of the description file
    """
    try:
        return jsonify({"status_code": 200, "output": descr_content})
    except Exception as e:
        return jsonify({"status_code": 500, "output": str(e)})

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
