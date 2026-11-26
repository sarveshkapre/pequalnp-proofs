from pathlib import Path
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "line"))
from triple_line import Encoder, project
from cases import allowed, verify
