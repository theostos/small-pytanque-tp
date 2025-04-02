import heapq
import time
import logging
import time
import random
from typing import List, Tuple, Optional
from enum import Enum
import re

import torch.nn.functional as F
import ollama

from client import ProofAssistantClientAPI, goals_to_str

logger = logging.getLogger()
logger.setLevel(logging.CRITICAL)

Tactic = str
Proof = List[Tactic]
Score = float

def generate_tactics_dummy(num_candidates: int, goals=[]
) -> Tuple[List[str], List[float]]:
    """
    Generate random tactics and random scores for testing purposes.
    """
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
    """
    Perform a beam search to find a valid proof using generated tactics.

    Args:
        generate_tactics (function): Function to generate candidate tactics.
        client (ProofAssistantClientAPI): Client API to interact with the theorem prover.
        section (str): Section identifier of the theorem.
        index_thm (int): Index of the theorem within the section.
        max_depth (int): Maximum depth for the search.
        beam_size (int, optional): Number of candidates to keep at each step. Defaults to 5.
        timeout (float, optional): Maximum allowed time in seconds. Defaults to 10.

    Returns:
        Optional[List[str]]: List of tactic steps leading to a proof if found, otherwise None.
    """
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


def get_response(prompt: str, model="gemma3:12b"):
    """
    Retrieve a response from the specified model using ollama.

    Args:
        prompt (str): The input prompt to send to the model.
        model (str, optional): Model identifier. Defaults to "gemma3:12b".

    Returns:
        str: The model's response content.
    """
    response = ollama.chat(
        model=model,
        messages=[
            {"role": "user", "content": prompt},
        ]
    )
    return response["message"]["content"]

class Keywords(Enum):
    GOALS = "[GOALS]"
    GOAL = "[GOAL]"
    HYPOTHESES = "[HYPOTHESES]"
    HYPOTHESIS = "[HYPOTHESIS]"
    STEPS = "[STEPS]"
    STEP = "[STEP]"
    INCORRECT_STEPS = "[INCORRECT STEPS]"
    DEFINITIONS = "[DEFINITIONS]"
    DEFINITION = "[DEFINITION]"
    THEOREMS = "[THEOREMS]"
    THEOREM = "[THEOREM]"
    ERROR = "[ERROR]"
    ERROR_MESSAGE = "[ERROR MESSAGE]"
    SUCCESS = "[SUCCESS]"
    END = "[END]"
    DESCRIPTION = "[DESCRIPTION]"
    LAST_STEP = "[LAST STEP]"
    INFORMAL_PROOF = "[INFORMAL-PROOF]"
    INFORMAL_THEOREM = "[INFORMAL-THEOREM]"

    def __str__(self) -> str:
            return self.value

def generate_prompt_wala(goals, steps=[], incorrect_steps=[], theorems=[], definitions=[]):
    prompt = f"Goals to prove:\n{Keywords.GOALS}\n"

    for k, goal in enumerate(goals):
        prompt += f"{Keywords.GOAL} {k + 1}\n{goal['ty']}\n"
        if goal['hyps']:
            prompt += f"{Keywords.HYPOTHESES} {k + 1}\n"
        for hyp in goal['hyps']:
            names = ", ".join(hyp['names'])
            ty = hyp['ty']
            prompt += f"{Keywords.HYPOTHESIS} {names}: {ty}\n"

    if definitions:
        prompt += f"{Keywords.DEFINITIONS} 1\n"
        for definition in definitions:
            prompt += f"{Keywords.DEFINITION} {definition}\n"

    if theorems:
        prompt +=  f"{Keywords.THEOREMS} 1\n"
        for theorem in theorems:
            prompt += f"{Keywords.THEOREM} {theorem}\n"

    if steps:
        prompt += f"{Keywords.STEPS} {1}\n"
        for step in steps:
            prompt += f"{Keywords.STEP} {step}\n"

    if incorrect_steps:
        prompt += f"{Keywords.INCORRECT_STEPS} {1}\n"
        for step in incorrect_steps:
            prompt += f"{Keywords.STEP} {step}\n"
    
    prompt += f"{Keywords.END}"
    return prompt

def parsed_output_wala(output):
    # to avoid some parsing issue, we accept instruction to not end with a point as normally required.
    pattern = r'\[RUN TACTIC\]\n(.*)\n\[END\]'
    match_output = re.search(pattern, output)
    if match_output:
      output = match_output.group(1).strip()
      return output
    return ''

def generate_tactics_wala(pipeline, model, tokenizer, max_beam_size, goals, steps=[], incorrect_steps=[], theorems=[], definitions=[]):
    device = 0
    prompt = generate_prompt_wala(goals, steps=steps, incorrect_steps=incorrect_steps, theorems=theorems, definitions=definitions)
    prompt_tokenized = tokenizer(prompt, return_tensors='pt')
    output = pipeline(prompt, max_length=100, num_return_sequences=max_beam_size, do_sample=True, temperature=1.2)
    input_ids, attention_mask = prompt_tokenized.values()

    result_output = []
    result_scores = []
    done = set()
    for output_str in output:
        output_str = parsed_output_wala(output_str['generated_text'])

        if output_str in done:
            continue
        decoder_input_ids, decoder_attention_mask = tokenizer(output_str, return_tensors='pt').values()
        scores = model.forward(input_ids=input_ids.to(device), attention_mask=attention_mask.to(device), decoder_input_ids=decoder_input_ids.to(device), decoder_attention_mask=decoder_attention_mask.to(device))['logits']
        
        shifted_logits = scores[:, :-1, :]

        # Shift decoder tokens to remove the first token (which is typically the start token)
        shifted_target = decoder_input_ids.to(scores.device)[:, 1:]
        logprobs = F.log_softmax(shifted_logits, dim=-1)
        token_logprobs = logprobs.gather(dim=-1, index=shifted_target.unsqueeze(-1)).squeeze(-1).mean(dim=-1)
        result_output.append(output_str)
        result_scores.append(float(token_logprobs))

        done.add(output_str)
    return result_output, result_scores
