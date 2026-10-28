import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3372 = true := by
  decide +kernel

theorem tot3372 : totK PD2M8K2 D2M8K2.t3372 = [0, 0, 206041237620, 488698517508, 175773896887, 5253830308, 0, 0] := by
  decide +kernel

theorem rows3373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3373 = true := by
  decide +kernel

theorem tot3373 : totK PD2M8K2 D2M8K2.t3373 = [0, 0, 188427075854, 466413940990, 195690982012, 10622372770, 0, 0] := by
  decide +kernel

theorem rows3374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3374 = true := by
  decide +kernel

theorem tot3374 : totK PD2M8K2 D2M8K2.t3374 = [0, 0, 52782444535, 346313639941, 367875456255, 55229002564, 1138244013, 0] := by
  decide +kernel

theorem rows3375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3375 = true := by
  decide +kernel

theorem tot3375 : totK PD2M8K2 D2M8K2.t3375 = [0, 0, 91474059103, 421402067005, 339908583229, 30001438954, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
