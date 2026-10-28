import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2252 = true := by
  decide +kernel

theorem tot2252 : totK PA10K2 A10K2.t2252 = [0, 322245181260, 903573226476, 798418200898, 1049474160513, 1320287039223, 522012413546, 48886019071, 0, 0] := by
  decide +kernel

theorem rows2253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2253 = true := by
  decide +kernel

theorem tot2253 : totK PA10K2 A10K2.t2253 = [0, 492378065510, 1769197975030, 1911855710287, 563698559801, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2254 = true := by
  decide +kernel

theorem tot2254 : totK PA10K2 A10K2.t2254 = [0, 44718331091, 853700727385, 2092022786819, 1569067620340, 368806801166, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2255 = true := by
  decide +kernel

theorem tot2255 : totK PA10K2 A10K2.t2255 = [0, 146033389842, 884803189799, 1908837988298, 1522175707212, 264024661158, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
