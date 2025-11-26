import pysmt.environment


def pytest_runtest_setup():
    env: pysmt.environment.Environment = pysmt.environment.reset_env()
    env.enable_infix_notation = True
