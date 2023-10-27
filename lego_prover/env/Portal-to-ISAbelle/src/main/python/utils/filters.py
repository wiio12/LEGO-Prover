import re


def filter_comments(input_text, opening_marks, closing_marks):
    output_text = re.sub(re.compile("{}.*?{}".format(opening_marks, closing_marks), re.DOTALL), "", input_text)
    return output_text


def filter_isar_comments(input_text):
    text = filter_comments(input_text, "\(\*", "\*\)")
    text = filter_comments(text, "text\\\<open\>", "\\\<close\>")
    return text


def spit_out_first_parsable_segment(input_text: str):
    find_first_line_separator = input_text.find("\n")
    if find_first_line_separator == -1:
        return input_text.strip(), ""

    first_line = input_text[:find_first_line_separator]

    # Theorem definitions must be read until the proof starts
    if "theorem" in first_line or "lemma" in first_line:
        find_first_proof = input_text.find("proof")
        find_first_apply = input_text.find("apply")
        find_first_by = input_text.find("by")

        if find_first_proof != -1 and find_first_proof < find_first_apply and find_first_proof < find_first_by:
            truncation_index = find_first_proof
        elif find_first_apply != -1 and find_first_apply < find_first_proof and find_first_apply < find_first_by:
            truncation_index = find_first_apply
        elif find_first_by != -1 and find_first_by < find_first_proof and find_first_by < find_first_apply:
            truncation_index = find_first_by
        else:
            raise NotImplementedError("We haven't thought of this situation. The Isar proof is as follows:\n" + input_text)

        first_bit = input_text[:truncation_index].strip()
        first_bit = first_bit.replace("\n", " ")

        return first_bit, input_text[truncation_index:].strip()

    # Inner syntax must not be read in two segments
    if first_line.count('"') % 2 == 0:
        return first_line.strip(), input_text[find_first_line_separator:].strip()
    # Find the next first double quotation mark as the end
    find_first_double_quotation = input_text[find_first_line_separator:].find('"')
    if find_first_double_quotation == -1:
        raise AssertionError
    return first_line.strip() + " " + input_text[find_first_line_separator:][:find_first_double_quotation+1].strip(), \
        input_text[find_first_line_separator:][find_first_double_quotation + 1:]


def spit_out_all_parsable_segments(input_text: str):
    segments = list()
    rest_of_the_text = input_text.strip()
    while rest_of_the_text:
        first_segment, rest_of_the_text = spit_out_first_parsable_segment(rest_of_the_text)
        segments.append(first_segment)
    return segments
