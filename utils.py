import heapq
import time
import logging
import time
import random
from typing import List, Tuple, Optional
import json

import requests

from client import ProofAssistantClientAPI

logger = logging.getLogger()
logger.setLevel(logging.CRITICAL)

Tactic = str
Proof = List[Tactic]
Score = float


def generate_tactics(num_candidates: int, goals=[]
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

def beam_search(client: ProofAssistantClientAPI, section: str, index_thm: int, max_depth: int, beam_size: int = 5, timeout: float = 10.) -> Optional[List[str]]:
    start_time = time.time()

    # Each beam item is a tuple: (state, proof_so_far)
    state, goals = client.start_thm(section, index_thm)
    beam: List[Tuple[dict, List[str]]] = [(state, goals, [])]

    for _ in range(max_depth):
        if time.time() - start_time > timeout:
            return None

        next_beam: List[Tuple[float, dict, dict, List[str]]] = []

        for state, goals, proof_so_far in beam:
            try:
                tactics, scores = generate_tactics(beam_size, goals)

                for tac, score in zip(tactics, scores):
                    if time.time() - start_time > timeout:
                        return None

                    try:
                        new_state, new_goals = client.run_tac(state, tac)
                        new_proof = proof_so_far + [tac]

                        if new_state['proof_finished']:
                            return new_proof

                        # Use negative score because heapq is a min-heap
                        next_beam.append((-score, new_state, new_goals, new_proof))

                    except Exception as e:
                        logging.warning(f"Invalid Tactic: {tac} {e}")
            except Exception as e:
                logging.warning(f"Tactic generation failed: {e}")

        if not next_beam:
            return None

        # Keep top `beam_size` candidates
        beam = [(state, goals, proof) for _, state, goals, proof in heapq.nsmallest(beam_size, next_beam)]

    return None
