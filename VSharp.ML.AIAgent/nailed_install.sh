conda create --name agent_env python=3.10.9
conda activate agent_env

conda install numpy pandas tabulate
conda install pytorch=1.13.1 torchvision=0.14.1 torchaudio=0.13.1 -c pytorch
python3 -m pip install --force-reinstall -v "torch-scatter==2.1.0" "torch-geometric==2.2.0" "torch-sparse==0.6.16"
conda install -c conda-forge dataclasses-json websocket-client pre_commit
pre-commit install
