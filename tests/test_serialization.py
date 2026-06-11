"""Serialization tests for theorydd package"""

from theorydd.abstractdd.abstraction_bdd import AbstractionBDD, abstraction_bdd_load_from_folder
from theorydd.abstractdd.abstraction_sdd import AbstractionSDD, abstraction_sdd_load_from_folder
from theorydd.tdd.theory_bdd import TheoryBDD, tbdd_load_from_folder
from theorydd.tdd.theory_sdd import TheorySDD, tsdd_load_from_folder


def test_abstraction_bdd_serialization(default_phi):
    """tests abstraction BDD serialization"""
    phi = default_phi
    original_dd = AbstractionBDD(phi)
    original_dd.save_to_folder("tests/test_data/abstraction_bdd")
    loaded_dd = abstraction_bdd_load_from_folder("tests/test_data/abstraction_bdd")
    assert len(original_dd) == len(loaded_dd), "Loaded BDD has different number of nodes"
    assert original_dd.count_models() == loaded_dd.count_models(), "Loaded BDD has different number of models"


def test_abstraction_sdd_serialization(default_phi):
    """tests abstraction SDD serialization"""
    phi = default_phi
    original_dd = AbstractionSDD(phi)
    original_dd.save_to_folder("tests/test_data/abstraction_sdd")

    loaded_dd = abstraction_sdd_load_from_folder("tests/test_data/abstraction_sdd")
    assert len(original_dd) == len(loaded_dd), "Loaded SDD has different number of nodes"
    assert original_dd.count_models() == loaded_dd.count_models(), "Loaded SDD has different number of models"


def test_theory_bdd_serialization(default_phi):
    """tests theory BDD serialization"""
    phi = default_phi
    original_dd = TheoryBDD(phi)
    original_dd.save_to_folder("tests/test_data/theory_bdd")

    loaded_dd = tbdd_load_from_folder("tests/test_data/theory_bdd")
    assert len(original_dd) == len(loaded_dd), "Loaded BDD has different number of nodes"
    assert original_dd.count_models() == loaded_dd.count_models(), "Loaded BDD has different number of models"


def test_theory_sdd_serialization(default_phi):
    """tests theory SDD serialization"""
    phi = default_phi
    original_dd = TheorySDD(phi)
    original_dd.save_to_folder("tests/test_data/theory_sdd")

    loaded_dd = tsdd_load_from_folder("tests/test_data/theory_sdd")
    assert len(original_dd) == len(loaded_dd), "Loaded SDD has different number of nodes"
    assert original_dd.count_models() == loaded_dd.count_models(), "Loaded SDD has different number of models"
