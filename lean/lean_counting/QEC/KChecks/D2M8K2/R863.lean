import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3452 = true := by
  decide +kernel

theorem tot3452 : totK PD2M8K2 D2M8K2.t3452 = [0, 206494954477, 487351841891, 220895322870, 8977779328, 0, 0, 0] := by
  decide +kernel

theorem rows3453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3453 = true := by
  decide +kernel

theorem tot3453 : totK PD2M8K2 D2M8K2.t3453 = [0, 55193762837, 290234086068, 371182040788, 174477887782, 21385604922, 0, 0] := by
  decide +kernel

theorem rows3454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3454 = true := by
  decide +kernel

theorem tot3454 : totK PD2M8K2 D2M8K2.t3454 = [0, 0, 210855065281, 482442778998, 192979551619, 7658844075, 0, 0] := by
  decide +kernel

theorem rows3455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3455 = true := by
  decide +kernel

theorem tot3455 : totK PD2M8K2 D2M8K2.t3455 = [0, 65194258425, 238300115304, 394922052399, 172990255516, 7877424857, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
