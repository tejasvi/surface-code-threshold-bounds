import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2240 = true := by
  decide +kernel

theorem tot2240 : totK PA10K2 A10K2.t2240 = [0, 0, 567717919021, 1992162428590, 1901002694119, 387509088611, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows2241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2241 = true := by
  decide +kernel

theorem tot2241 : totK PA10K2 A10K2.t2241 = [0, 542445699397, 1853580221050, 1883632487848, 599089252200, 54342172495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2242 = true := by
  decide +kernel

theorem tot2242 : totK PA10K2 A10K2.t2242 = [0, 330364443976, 1555325649491, 2167835925069, 866469558027, 68436273338, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2243 = true := by
  decide +kernel

theorem tot2243 : totK PA10K2 A10K2.t2243 = [0, 0, 539493877462, 1972362526090, 1958765778938, 436705204701, 13653259670, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
