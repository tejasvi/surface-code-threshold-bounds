import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t352 = true := by
  decide +kernel

theorem tot352 : totK PA10K2 A10K2.t352 = [0, 0, 0, 463540887127, 1771496883180, 1844947192868, 473540353846, 31193351345, 0, 0] := by
  decide +kernel

theorem rows353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t353 = true := by
  decide +kernel

theorem tot353 : totK PA10K2 A10K2.t353 = [0, 0, 0, 762554861951, 2164884715861, 1449423228576, 251631509207, 6354609102, 0, 0] := by
  decide +kernel

theorem rows354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t354 = true := by
  decide +kernel

theorem tot354 : totK PA10K2 A10K2.t354 = [0, 0, 0, 543327738956, 1829620564297, 1682997983898, 429995801847, 30559085710, 0, 0] := by
  decide +kernel

theorem rows355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t355 = true := by
  decide +kernel

theorem tot355 : totK PA10K2 A10K2.t355 = [0, 0, 0, 141281642770, 1412718778175, 2150999132574, 753911894596, 57856469163, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
