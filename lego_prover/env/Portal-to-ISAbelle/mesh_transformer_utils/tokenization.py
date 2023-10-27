from transformers import GPT2TokenizerFast

from abc import ABC, abstractmethod
from typing import List
from tokenizers import Tokenizer


class TokenizerWrapper(ABC):
    @abstractmethod
    def encode(self, sequence) -> List[int]:
        raise NotImplementedError

    @abstractmethod
    def decode(self, ids) -> str:
        raise NotImplementedError

    @property
    @abstractmethod
    def eos_token_id(self):
        raise NotImplementedError

    @property
    def eos_token_str(self):
        return '<|endoftext|>'

    @property
    def sep_token_str(self):
        return ' Cambridge'

    @property
    def pad_token_str(self):
        return ' Oxford'

    @property
    def sep_token_id(self):
        tokens = self.encode(self.sep_token_str)
        assert len(tokens) == 1
        return tokens[0]

    @property
    def pad_token_id(self):
        tokens = self.encode(self.pad_token_str)
        assert len(tokens) == 1
        return tokens[0]

    @classmethod
    def from_file_or_gpt(cls, tokenizer_path):
        if tokenizer_path:
            print(f'Using BPE tokenizer from: {tokenizer_path}')
            return BPETokenizerWrapper(Tokenizer.from_file(tokenizer_path))
        else:
            print('Tokenizer not provided - using default gpt2')
            GPT2TokenizerFast.max_model_input_sizes[
                'gpt2'] = 1e20  # disables a misleading warning
            tokenizer = GPT2TokenizerFast.from_pretrained('gpt2')
            return GPTTokenizerWrapper(tokenizer)


class GPTTokenizerWrapper(TokenizerWrapper):
    def __init__(self, tokenizer: GPT2TokenizerFast):
        self.tokenizer = tokenizer

    def encode(self, sequence):
        return self.tokenizer.encode(sequence)

    def decode(self, ids):
        return self.tokenizer.decode(ids)

    @property
    def eos_token_id(self):
        return self.tokenizer.eos_token_id


class BPETokenizerWrapper(TokenizerWrapper):
    def __init__(self, tokenizer: Tokenizer):
        self.tokenizer = tokenizer

    def encode(self, sequence):
        return self.tokenizer.encode(sequence).ids

    def decode(self, ids):
        return self.tokenizer.decode(ids)

    @property
    def eos_token_id(self):
        return self.tokenizer.token_to_id(self.eos_token_str)
