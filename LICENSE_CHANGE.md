# Licence change, November 5, 2026

From this commit on (November 5, 2026), the code in this repository is licensed under the Apache License 2.0
(`LICENSE`, `NOTICE`).
In every file whose header carried the copyright line, that line now reads "Copyright (C) Dave Goel 2026--now.
Licensed under the Apache License 2.0; see LICENSE." Nothing else changed in those files, except
`interval/README.md`, which also has a new version line and one new sentence pointing here.
Python parses each program to the same syntax tree as before, apart from that one line where it stands in a module
docstring. The version that the paper links, tag v3.90, is unchanged and keeps its own licence line.

The records of earlier runs are kept byte for byte, so they still show the checksums from before this change:
`interval/REPLAY_RECEIPT.json`, `interval/SOURCE_PROVENANCE.json`, `interval/AST_EQUIVALENCE.json` and
`interval/replays/release_primary/`. The file lists `interval/MANIFEST.json`, `interval/SUPPLEMENTAL_MANIFEST.json`
and `FILE_MANIFEST.json` are rebuilt and describe the current files.
The table lists every file whose bytes changed (`FILE_MANIFEST.json` is left out: it lists this file).

| File | sha256 at tag v3.90 | sha256 now |
|---|---|---|
| `LICENSE` | 77edf2bbf032f4186ccda312f22f19d32ae029a03b1d2bff501ed8450903aca7 | cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30 |
| `NOTICE` | (new file) | 97ebe2984c6b9f0cfe433671a358313abc7a015207d82080ad45cde78dfdd5b9 |
| `illustration/README.md` | 97e24ef94b908b33d1d8695c26e3239d85970820f5773ed744b4f9210f450fda | 077f62318304942f4396e7c92da3fa1f52e746aaae883b3a75e703942291cb70 |
| `illustration/lambda_one.py` | f12970b95fe1649a6b268cde4df377c14f5c3a309239c5ac8db366ef41628e22 | ff95c5a453938c692b7401d2e140b1292e432657aa7f11b04d384d6db21aea78 |
| `interval/MANIFEST.json` | 2cd2ebae3d608acbedc18a782560d11c79cc07c49b71c667a5d4c4a872db7f09 | 5e79785b46f086185369621de3e283631649e222dc24d37adc032423cfd60dda |
| `interval/README.md` | 98eff1b4cb264b5f997da2e3e81a3b13052936c1985fab978998eefbf9dc5701 | c43cefec00c690aaa95a276bd3a16a818e2f62501f9ad8a236a7f280205390ba |
| `interval/SUPPLEMENTAL_MANIFEST.json` | 5f7853d9578df7108e2382ddc09a379202c22853bbc7d80564c830d7d16f350b | d04419cd920c5208c8dae75acbffbae1c32ada33e411d7c22e1b42166c2d6e20 |
| `interval/certify_wide_chord.py` | dcd73dd834e8e6cf99f5feb5666d7fd1feaf3bf040aa4fa2ac5e2106e3823b79 | d4d0618182139ec7ba0dd2e338a61750ea13df9b4c0f870fba177eaf462d0f43 |
| `interval/programs/arch_search.py` | c001c75423e8e2b91b01b6b2e047cb192238df194c0efc29041848be319102ab | f1925a10d22794bad60a0decbbe12125dfd5eeb272bf04498b96139037adf179 |
| `interval/programs/boundary_bulk.py` | 0dccc82bf3b991345beb3298fb11579c2cc0d136a46d2b3f0d3fa710435756a5 | 44c4a88d30ff08ccb0d2f0a29fc97a54eb272dfd0c6a0b1a685fd345c7d76da7 |
| `interval/programs/boundary_bulk_extended.py` | 6f9c45efaadd6d566e5ab6d9c4e98bbc49cbc4732a1384b6fdaabb1027df744e | c5449e9eb0e732928375e530aa267b2f597902b1972faf2af4f257b4ea71fed2 |
| `interval/programs/boundary_sliver.py` | 238d1dd8a20ba406d41114826f5dfd4810c663efc9e60c0b528b45b1183047f3 | 7b8c3e1bfbe6909dcd67b803d2078169660b319c4c90472665ceb8b5ec0497ba |
| `interval/programs/corner_comparison.py` | 605ff7191f5a98a0befbe801150e2fbe61b1d85e1e32a3b424884dc0e10b7e47 | cf38788a11ef16051161c9d68badf2b68ed3fc2e929760dc5e7b93a759941e74 |
| `interval/programs/local_threshold.py` | 31d6481e269c040d6b56d258760574ad2c4d4b2e3dbd2b7ef284ef8353097d93 | 6e86d1ce014a87c5c9689e47b4b0efcc512984c2149d64c0389ead4284b65b9c |
| `interval/programs/omega_negative.py` | 3062875f5de991f48932a7de27aa09519be640473f1892e6215b9c2bcb26ed7b | 52d9fc08f515808be84100e382256c44860c59b6e81cfded72b4dd07c9caca72 |
| `interval/programs/omega_negative_alternate.py` | 31e351bdbbf6f620483d2823936f5062d3deb1793f8cd76c9769613e2c423911 | a44c44150c5cc6b77db6da8fa412b677694dce1d3cfe4a97c10a3c15722c81fa |
| `interval/programs/omega_positive.py` | 79616e8fb82d1cfb29baea485cf8268a36180ed89946e6fe8be0e11af58407bd | 210a701014132bc588059b28dde3be53b54ec4b34cc189a28ae454cb3a35ae47 |
| `interval/programs/omega_positive_alternate.py` | 975e1e536ba1fb39df1398bc3866311d0290673caa15f0a04755d2d8f089e383 | a082119375a6e5ae0b02171e7c9ec4baf7a474dc5f0692f14de7436f9e5dd719 |
| `interval/programs/omega_positive_independent.py` | 303655a20831a2582468f4c0088b8930f5573f592d4b6c1e5cc7a164e3f8bf26 | 8e3e5bc6d8d006a87cc98ea46bd21bad7007d9de5fd9b1ccefdb1a9504ddfdb3 |
| `interval/programs/pencil_search.py` | f48b3c38995ee329fc203492d59d869e4d78d336b475d02bf2a3896c56726531 | 6a85149e3484d2fea51489af3d7691c43247623effcd8b9d35268cc6062eaa5e |
| `interval/programs/spline_certificate.py` | ed3ea8a2ecea421918581d8021447c471683901fdbed5eb7c96954ce0ad635c8 | 3c68e47617d16d75ea9182dcffda68acb5340eac19714998b41a9034e6846f65 |
| `interval/programs/strip_bulk.py` | a45015ce62fbe0da64d5ececd5d1d47b2fa0908d4882afe31db2c66f9b269f73 | c8e62b2e1bb4c92290e1bb409cdab7d36fc24fcc5e5e5e235b6e3f7e4b86ff75 |
| `interval/programs/strip_bulk_independent.py` | 8e21ed1fcb72b94f97077087e0b0d23fe326c3c37e9ef93ab58ae30e85e4229c | d85c95c9694393c20ecbd8253c3c4671998fc5ca8f94b1070c8f3470185367a8 |
| `interval/programs/strip_corner.py` | dbf3c961b6d3ba33613f5e33b96f2a9a57aa513545f473eea82ce254bd4d1199 | 9f3e71f87dcc14f9a67f8355e6ae407085cde7f2a35e87e184ac2a08b3489514 |
| `interval/programs/strip_corner_independent.py` | b78927622208ce050749a1104f3103094cc4f7fb9de50b7ec85b590979b3d549 | e2e14cb389ad24abc625a331869d567bdce2c6aebb54e3d6016a5f4072edeeb2 |
| `interval/programs/wide_chord_comparison.py` | e2c860f776b614111ea6f0781f1092c04aad93d1a377184d5acf8a476b88c5ed | 0171a8974b25f7382f0fc138308b99d55675311061742aa41f82c92b40491221 |
| `interval/programs/wide_chord_independent.py` | 21c6d99e18be3f0bb735bbd3b473572988f92ac1450e9ece3c2bc4a430cb86cd | 8d4a496d0199ac13bcfd92a3e09ec3457879481bf5ab281293c51e39c20323d6 |
| `interval/prop_6_3_check/README.md` | dddefd6d80b33450ee7551498158ca42584c0c785fa65714c3cfa0ca38db2a6f | 4ed4de0fdc97fc12a9c1e3078959a696e9d1651a2fa8756aae4797b376b6ffb9 |
| `interval/prop_6_3_check/certify_wide_chord.py` | 7f72227c81ab826bc530fafa1c3d500a6c9ed771fc1655003fc7a54ef720eaa7 | b56afa4b3321cdb37541b5271654a565c7481b7489bbf12d97305ad04e665153 |
| `interval/replay_primary.py` | c95cede87267541807771861412b678a1a9beb054128a96c66334159a34c26f5 | 58e06af8dbd4a4461aaf984d8dec83ba1896de9b81a70a4faac412c8b450f9fc |
| `lean/GKSharp/Proofs/Envelope.lean` | 285be37559fbd78c556aba92a11bbb1ea94ae9fc44ea98da98dd972fd0e74841 | 31ef0fca282c3210c8b5c6929ed8416d34203cf91424cad393a80290f55ae928 |
| `lean/README.md` | 08eebc9c8d3d24f9d5d9fe453f212549020354ccae076b5d079668579a70b490 | 8f4fd7d0c09b2bea1ca4a1f1e370fd04bf51ce5653d199737baf0214d5347b7e |
