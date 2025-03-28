from typing import Dict, Tuple, List

import requests

State = Dict[str, str]
Goal = Dict[str, str]
Theorem = Dict[str, str]

class ClientError(Exception):
    def __init__(self, code, message):
        self.code = code
        self.message = message


class ProofAssistantClientAPI:
    """
    A simple client API for interacting with the proof assistant Flask server.
    """
    def __init__(self, base_url: str):
        """
        Initialize the client by setting the base URL, logging in, and fetching theorem descriptions.
        """
        self.base_url = base_url.rstrip("/")
        self.descr_thms = {}
        self.login = None
        self._login()
        self._get_thms()

    def _login(self):
        """
        Log in to the server to retrieve a load-balanced server index.
        """
        url = f"{self.base_url}/login"
        response = requests.get(url)
        if response.status_code == 200:
            self.login = response.json()['idx']
        else:
            raise ClientError(response.status_code, response.text)

    def _get_thms(self):
        """
        Retrieve theorem descriptions from the server.
        """
        url = f"{self.base_url}/get_thms"
        response = requests.get(url)
        if response.status_code == 200:
            self.descr_thms = response.json()
        else:
            raise ClientError(response.status_code, response.text)

    def sections(self) -> List[str]:
        """
        Get all available sections
        """
        return list(self.descr_thms.keys())
    def num_thm(self, section: str) -> int:
        """
        Get the number of available theorems.
        """
        return len(self.descr_thms[section])

    def show_thm(self, section: str, idx: int) -> List[Theorem]:
        """
        Retrieve the theorem description at the specified index.
        """
        return self.descr_thms[section][idx]

    def start_thm(self, section: str, idx: int) -> Tuple[State, Goal]:
        """
        Start a theorem proving session for the theorem at the given index.
        """
        if idx < 0 or idx >= self.num_thm(section):
            raise IndexError("Theorem index out of range")
        url = f"{self.base_url}/start_thm"
        payload = {'login': self.login, 'section': section, 'idx': idx}
        response = requests.post(url, json=payload)
        if response.status_code == 200:
            output = response.json()
            return output['state'], output['goals']
        else:
            raise ClientError(response.status_code, response.text)

    def run_tac(self, state: State, tactic: str) -> Tuple[State, Goal]:
        """
        Execute a given tactic on the current proof state.
        """
        url = f"{self.base_url}/run_tac"
        payload = {'login': self.login, 'state': state, 'tactic': tactic}
        response = requests.post(url, json=payload)
        if response.status_code == 200:
            output = response.json()
            return output['state'], output['goals']
        else:
            raise ClientError(response.status_code, response.text)

def goals_to_str(goals):
    pp = "Status: finished\n" if not goals else "Status: ongoing\n"
    for k, goal in enumerate(goals, start=1):
        pp += f"Goal {k}:\n"
        pp += goal['pp'] + '\n'
    return pp

# Example usage:
if __name__ == '__main__':
    client = ProofAssistantClientAPI("http://127.0.0.1:5000")
    for section in ['introduction', 'logic', 'math']:
        for k in range(client.num_thm(section)):
            thm = client.show_thm(section, k)
            print(thm['name'], thm['statement'])
            print("Started theorem session")
            state, goals = client.start_thm(section, k)
            print(goals_to_str(goals))
            tactics = thm['solution']
            for step in tactics:
                print(step)
                state, output = client.run_tac(state, step)
            print(goals_to_str(output))