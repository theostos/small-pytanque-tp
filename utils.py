import heapq
import time
import logging
import time
import random
from typing import List, Tuple, Optional
import json

import requests

from client import ProofAssistantClientAPI, goals_to_str

logger = logging.getLogger()
logger.setLevel(logging.CRITICAL)

Tactic = str
Proof = List[Tactic]
Score = float


def generate_tactics_dummy(num_candidates: int, goals=[]
) -> Tuple[List[str], List[float]]:
    hyp_names = []
    for goal in goals:
        for hyps in goal['hyps']:
            hyp_names += hyps['names']
    tactics = [
        "unfold not.",
        "intros.",
        "split.",
        "left.",
        "right."
    ] + [f"exact {hyp}." for hyp in hyp_names] + [f"apply {hyp}." for hyp in hyp_names] + [f"inversion {hyp}." for hyp in hyp_names]
    return random.choices(tactics, k=num_candidates), [
        random.uniform(0, 1) for _ in range(num_candidates)
    ]

def beam_search(generate_tactics, client: ProofAssistantClientAPI, section: str, index_thm: int, max_depth: int, beam_size: int = 5, timeout: float = 10.) -> Optional[List[str]]:
    start_time = time.time()

    # Each beam item is a tuple: (state, proof_so_far)
    state, goals = client.start_thm(section, index_thm)
    thm =  client.show_thm(section, index_thm)

    theorems = []
    definitions = []

    for premise in thm['premises']:
        if premise.startswith('Definition '):
            premise = premise.replace('Definition ', '').strip()
            definitions.append(premise)
        elif premise.startswith('Notation '):
            premise = premise.replace('Notation ', '').strip()
            definitions.append(premise)
        else:
            theorems.append(premise)
    
    beam: List[Tuple[float, dict, List[str], List[str]]] = [(0., state, goals, [], [])]
    visited = set()
    for _ in range(max_depth):
        if time.time() - start_time > timeout:
            return None

        next_beam: List[Tuple[float, dict, dict, List[str], List[str]]] = []
        for score, state, goals, steps, incorrect_steps in beam:
            try:
                tactics, new_scores = generate_tactics(beam_size, goals, steps=steps, incorrect_steps=incorrect_steps, theorems=theorems, definitions=definitions)
                for tac, new_score in zip(tactics, new_scores):
                    if time.time() - start_time > timeout:
                        return None

                    try:
                        new_state, new_goals = client.run_tac(state, tac)
                        new_goals_pp = goals_to_str(new_goals)
                        if new_goals_pp in visited:
                            continue

                        visited.add(new_goals_pp)
                        new_steps = steps + [tac]

                        if new_state['proof_finished']:
                            return new_steps

                        # Use negative score because heapq is a min-heap
                        next_beam.append((-new_score, new_state, new_goals, new_steps, []))

                    except Exception as e:
                        if tac not in incorrect_steps:
                            incorrect_steps.append(tac)                      
                        logging.warning(f"Invalid Tactic: {tac} {e}")
            except Exception as e:
                print(e)
                logging.warning(f"Tactic generation failed: {e}")
        if not next_beam:
            return None

        # Keep top `beam_size` candidates
        beam = [(score, state, goals, steps, incorrect_steps) for score, state, goals, steps, incorrect_steps in heapq.nsmallest(beam_size, next_beam)]

    return None
