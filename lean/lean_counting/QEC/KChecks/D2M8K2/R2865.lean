import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11460 = true := by
  decide +kernel

theorem tot11460 : totK PD2M8K2 D2M8K2.t11460 = [0, 0, 19168557488, 413988025014, 410154886984, 37042247584, 0, 0] := by
  decide +kernel

theorem rows11461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11461 = true := by
  decide +kernel

theorem tot11461 : totK PD2M8K2 D2M8K2.t11461 = [0, 0, 148244400496, 358914431610, 298858846641, 58501049344, 1225787871, 0] := by
  decide +kernel

theorem rows11462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11462 = true := by
  decide +kernel

theorem tot11462 : totK PD2M8K2 D2M8K2.t11462 = [0, 0, 146612666503, 452227269992, 283097476700, 24996295453, 0, 0] := by
  decide +kernel

theorem rows11463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11463 = true := by
  decide +kernel

theorem tot11463 : totK PD2M8K2 D2M8K2.t11463 = [0, 85430600343, 298390827695, 324847532738, 163258332958, 13065910070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
