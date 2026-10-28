import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t284 = true := by
  decide +kernel

theorem tot284 : totK PA10K2 A10K2.t284 = [0, 0, 342944423181, 1597433163098, 1941491189452, 604093590789, 38180250037, 0, 0, 0] := by
  decide +kernel

theorem rows285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t285 = true := by
  decide +kernel

theorem tot285 : totK PA10K2 A10K2.t285 = [0, 0, 0, 759166782860, 2160078470413, 1362557914199, 194163860899, 6354482628, 0, 0] := by
  decide +kernel

theorem rows286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t286 = true := by
  decide +kernel

theorem tot286 : totK PA10K2 A10K2.t286 = [0, 0, 0, 459000065289, 1856753942360, 1884718285300, 441022142507, 25633273041, 0, 0] := by
  decide +kernel

theorem rows287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t287 = true := by
  decide +kernel

theorem tot287 : totK PA10K2 A10K2.t287 = [0, 0, 0, 636147052472, 2045160876955, 1672854412161, 343216196125, 12918102615, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
