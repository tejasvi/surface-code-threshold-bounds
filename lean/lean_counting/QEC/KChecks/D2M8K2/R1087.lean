import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4348 = true := by
  decide +kernel

theorem tot4348 : totK PD2M8K2 D2M8K2.t4348 = [0, 0, 172400999523, 454058812693, 267216973614, 30732635182, 0, 0] := by
  decide +kernel

theorem rows4349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4349 = true := by
  decide +kernel

theorem tot4349 : totK PD2M8K2 D2M8K2.t4349 = [0, 0, 175878735128, 454250260671, 249809113119, 19974426625, 0, 0] := by
  decide +kernel

theorem rows4350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4350 = true := by
  decide +kernel

theorem tot4350 : totK PD2M8K2 D2M8K2.t4350 = [0, 0, 93768764846, 359762675439, 386723457965, 73784723054, 0, 0] := by
  decide +kernel

theorem rows4351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4351 = true := by
  decide +kernel

theorem tot4351 : totK PD2M8K2 D2M8K2.t4351 = [0, 0, 0, 226620889774, 500052313582, 157642353189, 2418991907, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
