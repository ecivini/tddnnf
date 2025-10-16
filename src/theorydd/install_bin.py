"""setup file"""

from argparse import ArgumentParser, Namespace
import os
import stat

from git import Repo


class InstallException(Exception):
    """an exception that is raised when installing goes wrong"""

    def __init__(self, msg):
        super().__init__(msg)


C2D_SOURCE = "http://reasoning.cs.ucla.edu/c2d/fetchme.php"
C2D_DOWNLOAD_ZIP = r"Linux%20i386"

D4_REPO = "https://github.com/crillab/d4v2"
LIBPATOH_DOWNLOAD_TAR = "patoh-Linux-x86_64.tar.gz"
LIBPATOH_DOWNLOAD_URL = f"https://faculty.cc.gatech.edu/~umit/PaToH/{LIBPATOH_DOWNLOAD_TAR}"

TABULAR_REPO = "https://github.com/giuspek/tabularAllSMT"


def get_args() -> Namespace:
    """Get arguments from command line"""
    parser = ArgumentParser()
    parser.add_argument(
        "--c2d",
        help="Installs the c2d dDNNF compiler in the provided directory",
        action="store_true",
    )
    parser.add_argument(
        "--d4",
        help="Installs the d4 dDNNF compiler in the provided directory",
        action="store_true",
    )
    parser.add_argument(
        "--tabular",
        help="Installs the tabular SMT solver in the provided directory",
        action="store_true",
    )
    return parser.parse_args()


def setup_c2d(install_path: str) -> None:
    """Installs c2d in the provided directory

    HAVEN'T TESTED YET: CAN'T CONNECT TO UCLA WEBSITE

    Args:
        install_path (str): the directory to install c2d
    """
    install_path += "/c2d"
    create_binary_folder(install_path)

    print("This data is required in order to to install c2d")
    name = input("Enter your name: ")
    name = name.replace(" ", "%20")
    email = input("Enter your e-mail: ")
    email = email.replace(" ", "%20")
    organization = input("Enter your organization: ")
    organization = organization.replace(" ", "%20")

    download_command = (
        "curl -d 'os="
        + C2D_DOWNLOAD_ZIP
        + f"&n={name}&e={email}&o={organization}' {C2D_SOURCE} --output {install_path}/c2d_linux.zip"
    )
    result = os.system(download_command)
    if result != 0:
        raise InstallException(f"Failed to download c2d from {C2D_SOURCE}")
    result = os.system(f"unzip {install_path}/c2d_linux.zip")
    if result != 0:
        raise InstallException("Failed to unzip c2d")

    # clean install directory from everything except the binary
    os.system(f"rm {install_path}/c2d_linux.zip")

    # make binary executable
    result = os.chmod(install_path + "/c2d_linux", stat.S_IXUSR)
    if result != 0:
        raise InstallException("Failed to make c2d executable")


def setup_d4(install_path: str) -> None:
    """Installs d4 in the provided directory

    Args:
        install_path (str): the directory to install d4
    """
    install_path += "/d4"
    create_binary_folder(install_path)

    old_working_directory = os.getcwd()

    # clone d4 repo
    repo_path = install_path + "/repo"
    clone_repo(D4_REPO, repo_path)
    os.chdir(repo_path)

    # manually install libpatoh.a 
    # tracking issue: https://github.com/crillab/d4v2/issues/1
    libpatoh_install_path = os.path.join(repo_path, "3rdParty", "patoh")
    setup_libpatoh(repo_path, libpatoh_install_path)

    print("Compiling D4...")
    # cd into repo/demo/compiler
    compiler_path = os.path.join(repo_path, "demo", "compiler")
    os.chdir(compiler_path)
    # compile with make
    result = os.system("./build.sh")
    if result != 0:
        raise InstallException("Failed to compile the D4 compiler!")

    # copy binary outside of repo folder
    os.system(f"cp {repo_path}/demo/compiler/build/compiler {install_path}/d4.bin")

    # make binary executable
    os.chmod(install_path + "/d4.bin", stat.S_IXUSR)

    # clean everything
    clean_repo(repo_path)

    # go back to old working directory
    os.chdir(old_working_directory)


def setup_libpatoh(download_path: str, install_path: str) -> None:
    """
    Installs libpatoh.a in the provided directory
    """
    print("Downloading libpatoh...")

    libpatoh_tar_download_path = os.path.join(download_path, LIBPATOH_DOWNLOAD_TAR)
    libpatoh_extracted_path = os.path.join(download_path, "tmp_libpatoh")
    libpatoh_lib_path = os.path.join(libpatoh_extracted_path, "build", "Linux-x86_64", "libpatoh.a")

    download_file(LIBPATOH_DOWNLOAD_URL, libpatoh_tar_download_path)

    # unzip libpatoh
    if not os.path.exists(libpatoh_extracted_path):
        os.mkdir(libpatoh_extracted_path)
    result = os.system(f"tar -xvzf {libpatoh_tar_download_path} -C tmp_libpatoh")
    if result != 0:
        raise InstallException("Failed to unzip libpatoh")
    
    # copy libpatoh files into d4 repo
    os.system(f"cp {libpatoh_lib_path} {install_path}/libpatoh.a")

    # remove files and folders
    os.system(f"rm {download_path}/{LIBPATOH_DOWNLOAD_TAR}")
    os.system(f"rm -r {libpatoh_extracted_path}")


def setup_tabular(install_path: str) -> None:
    """Installs tabular in the provided directory

    Args:
        install_path (str): the directory to install tabular
    """
    install_path += "/tabular"
    create_binary_folder(install_path)

    # clone repo
    repo_path = install_path + "/repo"
    clone_repo(TABULAR_REPO, repo_path)

    # copy binary outside of repo folder
    os.system(f"cp {repo_path}/tabularAllSMT {install_path}/tabularAllSMT.bin")

    # make binary executable
    os.chmod(install_path + "/tabularAllSMT.bin", stat.S_IXUSR)

    clean_repo(repo_path)


def clean_repo(repo_path: str) -> None:
    """Removes the cloned repository"""
    # clean everything
    print("Cleaning up...")
    if os.path.exists(repo_path):
        os.system("rm -rdf --interactive=never " + repo_path)


def clone_repo(repo_url: str, repo_path: str) -> None:
    """clones a git repo"""
    # clean up for cloning
    print(f"Cloning repository {repo_url}...")
    if os.path.exists(repo_path):
        os.system("rm -rdf --interactive=never " + repo_path)
    # clone repo
    Repo.clone_from(repo_url, repo_path)

def download_file(url: str, output_path: str) -> None:
    """Downloads a file from a URL to the specified output path"""
    result = os.system(f"curl -L {url} --output {output_path}")
    if result != 0:
        raise InstallException(f"Failed to download file from {url}")

def create_binary_folder(binary_path: str) -> None:
    """Creates the binary folder if it doesn't exist"""
    if not os.path.exists(binary_path):
        os.mkdir(binary_path)

def run_setup():
    """Run setup"""
    args = get_args()
    module_path = os.path.dirname(os.path.realpath(__file__))
    binary_path = module_path + "/bin"
    if not os.path.exists(binary_path):
        os.mkdir(binary_path)
    if args.c2d:
        print("Installing the c2d compiler...")
        try:
            setup_c2d(binary_path)
            print("c2d successfully installed")
        except InstallException as e:
            print(f"Failed to install c2d: {e}")
    if args.d4:
        print("Installing the d4 compiler...")
        try:
            setup_d4(binary_path)
            print("d4 successfully installed")
        except InstallException as e:
            print(f"Failed to install d4: {e}")
    if args.tabular:
        print("Installing tabular AllSMT...")
        try:
            setup_tabular(binary_path)
            print("TabularAllSMT successfully installed")
        except InstallException as e:
            print(f"Failed to install tabular: {e}")


if __name__ == "__main__":
    run_setup()
