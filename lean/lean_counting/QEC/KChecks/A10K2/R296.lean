import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1184 = true := by
  decide +kernel

theorem tot1184 : totK PA10K2 A10K2.t1184 = [0, 0, 165509237836, 1117845315732, 2117207968389, 1329700959815, 204016572962, 6066958478, 0, 0] := by
  decide +kernel

theorem rows1185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1185 = true := by
  decide +kernel

theorem tot1185 : totK PA10K2 A10K2.t1185 = [0, 0, 0, 542229138063, 1982401138261, 1984092921104, 414558798885, 5753308685, 0, 0] := by
  decide +kernel

theorem rows1186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1186 = true := by
  decide +kernel

theorem tot1186 : totK PA10K2 A10K2.t1186 = [0, 0, 507353961997, 1607097296116, 1645189042620, 780813896689, 319440819439, 35510771247, 0, 0] := by
  decide +kernel

theorem rows1187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1187 = true := by
  decide +kernel

theorem tot1187 : totK PA10K2 A10K2.t1187 = [0, 0, 354088205557, 1688812272405, 2091728717598, 702265518286, 47192218651, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
