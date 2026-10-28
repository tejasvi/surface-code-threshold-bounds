import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6256 = true := by
  decide +kernel

theorem tot6256 : totK PD2M8K2 D2M8K2.t6256 = [0, 203135734602, 492320227056, 202290967025, 9986849518, 0, 0, 0] := by
  decide +kernel

theorem rows6257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6257 = true := by
  decide +kernel

theorem tot6257 : totK PD2M8K2 D2M8K2.t6257 = [0, 183952773034, 476493525938, 222778918179, 13589010565, 0, 0, 0] := by
  decide +kernel

theorem rows6258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6258 = true := by
  decide +kernel

theorem tot6258 : totK PD2M8K2 D2M8K2.t6258 = [0, 180171611555, 467067228340, 243164153824, 13820419321, 0, 0, 0] := by
  decide +kernel

theorem rows6259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6259 = true := by
  decide +kernel

theorem tot6259 : totK PD2M8K2 D2M8K2.t6259 = [0, 185300393801, 469760764043, 217990256646, 7852808158, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
