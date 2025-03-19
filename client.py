import requests

class ClientAPI:
    """
    A simple client API for interacting with the proof assistant Flask server.
    """
    def __init__(self, base_url: str):
        """
        Initialize the client by setting the base URL, logging in, and fetching theorem descriptions.
        """
        self.base_url = base_url.rstrip("/")
        self.state = None
        self.descr_thms = []
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
            self.login = response.json().get('output')
        else:
            raise Exception(f"Login Error: {response.status_code} {response.text}")

    def _get_thms(self):
        """
        Retrieve theorem descriptions from the server.
        """
        url = f"{self.base_url}/get_thms"
        response = requests.get(url)
        if response.status_code == 200:
            self.descr_thms = response.json().get('output', [])
        else:
            raise Exception(f"Error fetching theorems: {response.status_code} {response.text}")

    def num_thm(self) -> int:
        """
        Get the number of available theorems.
        """
        return len(self.descr_thms)

    def show_thm(self, idx: int):
        """
        Retrieve the theorem description at the specified index.
        """
        if idx < 0 or idx >= self.num_thm():
            raise IndexError("Theorem index out of range")
        return self.descr_thms[idx]

    def start_thm(self, idx: int):
        """
        Start a theorem proving session for the theorem at the given index.
        """
        if idx < 0 or idx >= self.num_thm():
            raise IndexError("Theorem index out of range")
        url = f"{self.base_url}/start_thm"
        payload = {'login': self.login, 'idx': idx}
        response = requests.post(url, json=payload)
        if response.status_code == 200:
            output = response.json().get('output', {})
            self.state = output.get('state')
            return output
        else:
            raise Exception(f"Error starting theorem: {response.status_code} {response.text}")

    def run_tac(self, tactic: str):
        """
        Execute a given tactic on the current proof state.
        """
        if self.state is None:
            raise Exception("Error: No theorem session started. Please call start_thm first.")
        url = f"{self.base_url}/run_tac"
        payload = {'login': self.login, 'state': self.state, 'tactic': tactic}
        response = requests.post(url, json=payload)
        if response.status_code == 200:
            output = response.json().get('output', {})
            self.state = output.get('state')
            return output
        else:
            raise Exception(f"Error running tactic: {response.status_code} {response.text}")

# Example usage:
if __name__ == '__main__':
    try:
        client = ClientAPI("http://localhost:5000")
        print("Theorem 0 description:", client.show_thm(0))
        start_output = client.start_thm(0)
        print("Started theorem session:", start_output)
        tactics = ['intros.', 'apply H0.', 'exact H.']
        for step in tactics:
            output = client.run_tac(step)
            print("Updated state and goals after tactic:", output)
    except Exception as e:
        print("An error occurred:", e)
