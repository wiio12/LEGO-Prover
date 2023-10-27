import argparse
import os
import random

from pathlib import Path

import numpy as np
import tensorflow as tf
from lm_dataformat import Reader
from tqdm import tqdm

from mesh_transformer_utils.tokenization import TokenizerWrapper


def parse_args():
    parser = argparse.ArgumentParser(description="""
    Converts a text dataset into the training data format expected by the model.

    Adapted from the script create_tfrecords.py in the gpt-neo repo.

    - Your text dataset:
        - can be provided as .txt files, or as an archive (.tar.gz, .xz, jsonl.zst).
        - can be one file or multiple
            - using a single large file may use too much memory and crash - if this occurs, split the file up into a few files
        - the model's end-of-text separator is added between the contents of each file
        - if the string '<|endoftext|>' appears inside a file, it is treated as the model's end-of-text separator (not the actual string '<|endoftext|>')
            - this behavior can be disabled with --treat-eot-as-text

    This script creates a single .tfrecords file as output
        - Why: the model's data loader ignores "trailing" data (< 1 batch) at the end of a .tfrecords file
            - this causes data loss if you have many .tfrecords files
        - This is probably not appropriate for very large datasets
    """, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--input-dir", type=str, default=None,
                        help="Path to where your files are located.")
    parser.add_argument("--name", type=str, default=None,
                        help="Name of output file will be {name}_{seqnum}.tfrecords, where seqnum is total sequence count")
    parser.add_argument("--output-dir", type=str, default="",
                        help="Output directory (default: current directory)")
    parser.add_argument("--tokenizer-path", type=str, default=None,
                        help="Path to a custom BPE tokenizer (default: None, gpt2 tokenizer)")

    cleaning_args = parser.add_argument_group('data cleaning arguments')

    cleaning_args.add_argument("--normalize-with-ftfy", action="store_true",
                               help="Normalize text with ftfy")
    cleaning_args.add_argument("--normalize-with-wikitext-detokenize",
                               action="store_true",
                               help="Use wikitext detokenizer")
    minu_help = "Exclude repetitive documents made up of < MIN_UNIQUE_TOKENS unique tokens. These can produce large gradients."
    minu_help += " Set <= 0 to disable. If enabled, 200 is a good default value. (Default: 0)"
    cleaning_args.add_argument("--min-unique-tokens", type=int, default=0,
                               help=minu_help)

    shuffle_pack_args = parser.add_argument_group(
        'data shuffling/packing arguments')
    repack_ep_help = "Repeat the data N_REPACK_EPOCHS times, shuffled differently in each repetition. Recommended for multi-epoch training (set this to your intended number of epochs)."
    shuffle_pack_args.add_argument("--n-repack-epochs",
                                   type=int, default=1,
                                   help=repack_ep_help
                                   )
    shuffle_pack_args.add_argument("--seed", type=int, default=10,
                                   help="random seed for shuffling data (default: 10)")
    shuffle_pack_args.add_argument("--preserve-data-order",
                                   default=False, action="store_true",
                                   help="Disables shuffling, so the input and output data have the same order.")

    misc_args = parser.add_argument_group('miscellaneous arguments')
    misc_args.add_argument("--verbose",
                           default=False, action="store_true",
                           help="Prints extra information, such as the text removed by --min-unique-tokens")

    args, unknown = parser.parse_known_args()
    print(f'Unknown args: {unknown}')

    return args


def get_files(input_dir):
    filetypes = ["jsonl.zst", ".txt", ".xz", ".tar.gz"]
    files = [list(Path(input_dir).glob(f"*{ft}")) for ft in filetypes]
    # flatten list of list -> list and stringify Paths
    return [str(item) for sublist in files for item in sublist]


def _int64_feature(value):
    """
    Returns an int64_list from a bool / enum / int / uint.
    """
    return tf.train.Feature(int64_list=tf.train.Int64List(value=value))


def write_to_file(writer, data):
    """
    writes data to tfrecord file
    """
    feature = {
        "text": _int64_feature(data)
    }
    tf_example = tf.train.Example(features=tf.train.Features(feature=feature))
    writer.write(tf_example.SerializeToString())


def write_tfrecord(sequences, fp):
    with tf.io.TFRecordWriter(fp) as writer:
        for seq in sequences:
            write_to_file(writer, seq)


def split_list(l, n):
    # splits list/string into n size chunks
    return [l[i:i + n] for i in range(0, len(l), n)]


def enforce_min_unique(seqs, min_unique_tokens, enc, verbose=False):
    for seq in tqdm(seqs, mininterval=1, smoothing=0):
        if len(set(seq)) >= min_unique_tokens:
            yield seq
        elif verbose:
            text = enc.decode(seq)
            print(
                f"excluding with {len(set(seq))} unique tokens:\n\n{repr(text)}\n\n")


def eot_splitting_generator(string_iterable, encoder: TokenizerWrapper):
    """
    Given strings, splits them internally on <|endoftext|> and yields (generally more) strings
    """
    for doc in string_iterable:
        for d in doc.split(encoder.eos_token_str):
            if len(d.strip()) > 0:
                yield d


def prep_and_tokenize_generator(string_iterable, encoder: TokenizerWrapper,
                                normalize_with_ftfy,
                                normalize_with_wikitext_detokenize):
    """
    Given strings, does data cleaning / tokenization and yields arrays of tokens
    """
    for doc in string_iterable:
        tokens = encoder.encode(doc) + [encoder.eos_token_id]
        yield np.array(tokens, dtype=np.uint16)


def file_to_tokenized_docs_generator(file_path, encoder, args):
    """
    Given a file path, reads the file and tokenizes the contents

    Yields token arrays of arbitrary, unequal length
    """
    reader = Reader(file_path)
    string_iterable = reader.stream_data(threaded=False)
    string_iterable = eot_splitting_generator(string_iterable, encoder)

    token_list_gen = prep_and_tokenize_generator(string_iterable,
                                                 encoder,
                                                 normalize_with_ftfy=args.normalize_with_ftfy,
                                                 normalize_with_wikitext_detokenize=args.normalize_with_wikitext_detokenize
                                                 )
    return token_list_gen


def read_files_to_tokenized_docs(files, args, encoder):
    docs = []

    if args.preserve_data_order:
        files = sorted(files)
    else:
        random.shuffle(files)

    for f in tqdm(files, mininterval=10, smoothing=0):
        docs.extend(file_to_tokenized_docs_generator(f, encoder, args))

    if not args.preserve_data_order:
        # shuffle at individual document level
        random.shuffle(docs)

    return docs


def arrays_to_sequences(token_list_iterable, sequence_length=2049):
    """
    Given token arrays of arbitrary lengths, concats/splits them into arrays of equal length

    Returns equal-length token arrays, followed by a a final array of trailing tokens (which may be shorter)
    """
    print('Chunking in standard LM mode')
    accum = []

    for l in token_list_iterable:
        accum.extend(l)

        if len(accum) > sequence_length:
            chunks = split_list(accum, sequence_length)
            for chunk in chunks[:-1]:
                yield chunk
            accum = chunks[-1]

    if len(accum) > 0:
        yield accum


def arrays_to_sequences_pad(token_list_iterable, pad_token_id,
                            sequence_length=2049,
                            sep_token_id=None,
                            eos_token_id=None):
    print('Chunking in seq2seq mode')
    accum = []
    too_long = 0
    for chunk in tqdm(token_list_iterable):
        chunk = chunk.tolist()
        n_sep_tokens = sum(x == sep_token_id for x in chunk)
        n_eos_tokens = sum(x == eos_token_id for x in chunk)
        assert n_sep_tokens == n_eos_tokens, print(n_sep_tokens,
                                                   n_eos_tokens)
        if len(chunk) > sequence_length:
            too_long += 1
        elif len(accum) + len(chunk) > sequence_length:
            res = accum + [pad_token_id] * (sequence_length - len(accum))
            n_sep_tokens = sum(x == sep_token_id for x in res)
            n_eos_tokens = sum(x == eos_token_id for x in res)
            assert n_sep_tokens == n_eos_tokens, print(n_sep_tokens,
                                                       n_eos_tokens)
            yield res
            accum = chunk
        else:
            accum.extend(chunk)

    print(f'Discarded {too_long} examples longer than {sequence_length}')
    if len(accum) > 0:
        yield accum


def chunk_and_finalize(arrays, args, encoder):
    seq2seq = getattr(args, 'seq2seq', True)

    if seq2seq:
        sequences = list(
            arrays_to_sequences_pad(arrays, pad_token_id=encoder.pad_token_id,
                                    sep_token_id=encoder.sep_token_id,
                                    eos_token_id=encoder.eos_token_id))
    else:
        sequences = list(map(lambda x: np.array(x, dtype=np.uint16),
                             arrays_to_sequences(arrays)))

    full_seqs, trailing_data = sequences[:-1], sequences[-1]

    if args.min_unique_tokens > 0:
        full_seqs = list(
            enforce_min_unique(full_seqs, args.min_unique_tokens, encoder,
                               args.verbose))

    if not args.preserve_data_order:
        random.shuffle(full_seqs)

    return full_seqs, trailing_data


def create_tfrecords(files, args):
    encoder = TokenizerWrapper.from_file_or_gpt(args.tokenizer_path)

    random.seed(args.seed)

    docs = read_files_to_tokenized_docs(files, args, encoder)

    full_seqs, trailing_data = chunk_and_finalize(docs, args, encoder)

    if getattr(args, 'seq2seq', True):
        # Seq2seq sanity checks
        assert all(
            encoder.decode(x[:20]).strip().startswith('<') for x in full_seqs)
        sep_id = encoder.sep_token_id
        eos_id = encoder.eos_token_id
        pad_id = encoder.pad_token_id
        for seq in full_seqs:
            last_non_pad_idx = max(
                i for i in range(len(seq)) if seq[i] != pad_id)
            assert seq[last_non_pad_idx] == eos_id
            n_sep_tokens = sum(x == sep_id for x in seq)
            n_eos_tokens = sum(x == eos_id for x in seq)
            assert n_sep_tokens == n_eos_tokens, print(n_sep_tokens,
                                                       n_eos_tokens)

    # final
    print(f"dropped {len(trailing_data)} tokens of trailing data")

    total_sequence_len = len(full_seqs)

    fp = os.path.join(args.output_dir,
                      f"{args.name}_{total_sequence_len}.tfrecords")
    write_tfrecord(full_seqs, fp)


def create_finetune_tfrecords(**kwargs):
    args = parse_args()

    # Update by kwargs
    for k, v in kwargs.items():
        setattr(args, k, v)
    if not args.input_dir.endswith("/"):
        args.input_dir = args.input_dir + "/"

    if args.output_dir:
        os.makedirs(args.output_dir, exist_ok=True)
    files = get_files(args.input_dir)
    create_tfrecords(files, args)


if __name__ == "__main__":
    create_finetune_tfrecords()
