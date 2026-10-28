import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6664 = true := by
  decide +kernel

theorem tot6664 : totK PD2M8K2 D2M8K2.t6664 = [0, 0, 197480299590, 482167275940, 221678278157, 13604428459, 0, 0] := by
  decide +kernel

theorem rows6665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6665 = true := by
  decide +kernel

theorem tot6665 : totK PD2M8K2 D2M8K2.t6665 = [0, 85714291646, 301480683928, 406600500903, 112389735636, 1409560813, 0, 0] := by
  decide +kernel

theorem rows6666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6666 = true := by
  decide +kernel

theorem tot6666 : totK PD2M8K2 D2M8K2.t6666 = [0, 182284617381, 468740450812, 252751884500, 22674457381, 0, 0, 0] := by
  decide +kernel

theorem rows6667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6667 = true := by
  decide +kernel

theorem tot6667 : totK PD2M8K2 D2M8K2.t6667 = [0, 172345213079, 473120861795, 242923926970, 13632511348, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
