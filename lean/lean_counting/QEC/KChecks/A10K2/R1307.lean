import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5228 = true := by
  decide +kernel

theorem tot5228 : totK PA10K2 A10K2.t5228 = [0, 0, 0, 444587546458, 1761440899051, 1950360345947, 513093673129, 31222411477, 0, 0] := by
  decide +kernel

theorem rows5229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5229 = true := by
  decide +kernel

theorem tot5229 : totK PA10K2 A10K2.t5229 = [0, 0, 0, 96890305222, 889821949642, 1940991789847, 1415068949827, 358352176653, 25239774317, 0] := by
  decide +kernel

theorem rows5230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5230 = true := by
  decide +kernel

theorem tot5230 : totK PA10K2 A10K2.t5230 = [0, 0, 0, 287930791013, 1163953064560, 1824661315973, 1114835598066, 186084294959, 5365973533, 0] := by
  decide +kernel

theorem rows5231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5231 = true := by
  decide +kernel

theorem tot5231 : totK PA10K2 A10K2.t5231 = [0, 0, 0, 431181007177, 1756034527558, 1870178795521, 479840845538, 30954851499, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
