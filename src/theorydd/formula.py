"""this module simplifies interactions with the pysmt library for handling SMT formulas"""

import json
import os
from io import StringIO
from typing import Dict, List, Tuple, cast

from pysmt.fnode import FNode
from pysmt.shortcuts import And, Symbol, read_smtlib, write_smtlib
from pysmt.smtlib.parser.parser import get_formula
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.typing import BOOL

from theorydd.util._string_generator import SequentialStringGenerator
from theorydd.walkers.normalizer import NormalizerWalker


def read_phi(filename: str) -> FNode:
    """Reads the SMT formula from a file and returns the corresponding root FNode

    Args:
        filename (str): the name of the file

    Returns:
        FNode: the pysmt formula read from the file
    """
    return cast(FNode, read_smtlib(filename))


def save_phi(phi: FNode, filename: str) -> None:
    """Saves the formula phi on a SMT file

    Args:
        filename (str): the name of the file
    """
    write_smtlib(phi, filename)


def get_atoms(phi: FNode) -> List[FNode]:
    """Returns a list of all the atoms in the SMT formula

    Args:
        phi (FNode): a pysmt formula

    Returns:
        List[FNode]: the atoms in the formula
    """
    return list(phi.get_atoms())


def get_normalized(phi: FNode, converter) -> FNode:
    """Returns a normalized version of phi

    Args:
        phi (FNode): a pysmt formula

    Returns:
        FNode: the provided formula normalized according to the converter
    """
    walker = NormalizerWalker(converter)
    return walker.walk(phi)


def get_phi_and_lemmas(phi: FNode, tlemmas: List[FNode]) -> FNode:
    """Returns a formula that is equivalent to phi and lemmas as an FNode

    Args:
        phi (FNode): a pysmt formula
        tlemmas (List[FNode]): a list of pysmt formulas

    Returns:
        FNode: the big and of phi and the lemmas
    """
    return And(phi, *tlemmas)


def get_boolean_mapping(phi: FNode) -> Dict[FNode, FNode]:
    """Generates a new fresh atom for each T-atom in phi and maps them

    Args:
        phi (FNode): a pysmt formula

    Returns:
        Dict[FNode,FNode]: a dictionary containing the mapping,
            where the fresh boolean atoms are keys and the T-atoms are items
    """
    phi_atoms = get_atoms(phi)
    res: Dict[FNode, FNode] = {}
    gen = SequentialStringGenerator()
    for atom in phi_atoms:
        if not atom.is_symbol():
            res.update({Symbol(f"fresh_{gen.next_string()}", BOOL): atom})
    return res


def atoms_difference(original: List[FNode], expanded: List[FNode]) -> List[FNode]:
    """Computes the diffrence between expanded and original

    Args:
        original (List[FNode]): a list the atoms of the original pysmt formula,
            before adding the lemmas
        tlemmas (List[FNode]): a list of the atoms the expanded formula,
            with the lemmas

    Returns:
        List[FNode]: the atoms that appear in expanded, but do not appear in original
    """
    return list(set(expanded) - set(original))


def save_refinement(mapping: Dict[object, FNode], mapping_file: str) -> None:
    """
    Saves a mapping from objects to pysmt atoms in a file.
    This mapping is used to define the REFINEMENT function

    Args:
        mapping (Dict[object,FNode]) -> a mapping that associates to objects a pysmt atom
        mapping_file (str) -> the path to the file where the mapping file will be saved
    """

    # collect serialized mapping items
    mapping_items: List[Tuple[object, str]] = []
    for k, v in mapping.items():
        # serialize formula into SMTlib script and read it on a string stream
        script = smtlibscript_from_formula(v)
        output_stream = StringIO()
        script.serialize(output_stream)
        serialized_item = output_stream.getvalue()
        # add serialized item to list
        mapping_items.append((k, serialized_item))

    # write mapping_items in mapping file
    with open(mapping_file, "w", encoding="utf8") as out:
        json.dump(mapping_items, out)


def save_abstraction_function(mapping: Dict[FNode, object], mapping_file: str) -> None:
    """
    Saves a mapping from pysmt atoms to objects in a file.
    This mapping is used to define the ABSTRACTION function

    Args:
        mapping (Dict[FNode,object]) -> a mapping that associates to each pysmt atom an object
        mapping_file (str) -> the path to the file where the mapping file will be saved
    """
    # collect serialized mapping items
    mapping_items: List[Tuple[str, object]] = []
    for k, v in mapping.items():
        # serialize formula into SMTlib script and read it on a string stream
        script = smtlibscript_from_formula(k)
        output_stream = StringIO()
        script.serialize(output_stream)
        serialized_item = output_stream.getvalue()
        # add serialized item to list
        mapping_items.append((serialized_item, v))

    # write mapping_items in mapping file
    with open(mapping_file, "w", encoding="utf8") as out:
        json.dump(mapping_items, out)


def load_refinement(mapping_path: str) -> Dict[object, FNode]:
    """
    Loads a mapping from objects to pysmt atoms from a file.
    This mapping is used to define the REFINEMENT function

    Args:
        mapping_path (str) -> the path to the folder where the mapping is saved

    Returns:
        (Dict[object,FNode]) -> a mapping that associates to objects a pysmt atom
    """
    if not os.path.exists(mapping_path):
        raise FileNotFoundError(f"The path {mapping_path} does not exist. Please create it before loading the mapping.")

    mapping: Dict[object, FNode] = {}
    with open(mapping_path, "r", encoding="utf8") as input_data:
        mapping_items: List[Tuple[int, str]] = json.load(input_data)
        for item in mapping_items:
            key = item[0]
            serialized_formula = item[1]
            # read serialized formula from string stream
            input_stream = StringIO(serialized_formula)
            mapping[key] = cast(FNode, get_formula(input_stream))
    return mapping


def load_abstraction_function(mapping_path: str) -> Dict[FNode, object]:
    """
    Loads a mapping from pysmt atoms to objects from a file.
    This mapping is used to define the ABSTRACTION function

    Args:
        mapping_path (str) -> the path to the folder where the mapping is saved

    Returns:
        (Dict[FNode,object]) -> a mapping that associates to each pysmt atom an object
    """
    if not os.path.exists(mapping_path):
        raise FileNotFoundError(f"The path {mapping_path} does not exist. Please create it before loading the mapping.")

    mapping: Dict[FNode, object] = {}
    with open(mapping_path, "r", encoding="utf8") as input_data:
        mapping_items: List[Tuple[int, str]] = json.load(input_data)
        for item in mapping_items:
            key = item[1]
            serialized_formula = item[0]
            # read serialized formula from string stream
            input_stream = StringIO(serialized_formula)
            f = cast(FNode, get_formula(input_stream))
            mapping[f] = key
    return mapping
