import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12500 = true := by
  decide +kernel

theorem tot12500 : totK PD2M8K2 D2M8K2.t12500 = [0, 176625348125, 458410308533, 242765987775, 17111991321, 0, 0, 0] := by
  decide +kernel

theorem rows12501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12501 = true := by
  decide +kernel

theorem tot12501 : totK PD2M8K2 D2M8K2.t12501 = [0, 151487960372, 448632262759, 265645405131, 18952422838, 0, 0, 0] := by
  decide +kernel

theorem rows12502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12502 = true := by
  decide +kernel

theorem tot12502 : totK PD2M8K2 D2M8K2.t12502 = [0, 0, 273088729032, 505175673284, 112112760189, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12503 = true := by
  decide +kernel

theorem tot12503 : totK PD2M8K2 D2M8K2.t12503 = [0, 142288836322, 422735765929, 330099897684, 35257920277, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
