import pysmt.environment


def pytest_runtest_setup():
    pysmt.environment.reset_env()
