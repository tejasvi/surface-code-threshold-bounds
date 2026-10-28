import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t952 = true := by
  decide +kernel

theorem tot952 : totK PD2M8K2 D2M8K2.t952 = [0, 0, 321643303197, 484566564401, 93264175316, 0, 0, 0] := by
  decide +kernel

theorem rows953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t953 = true := by
  decide +kernel

theorem tot953 : totK PD2M8K2 D2M8K2.t953 = [0, 70079983307, 288941160241, 385878151781, 116451124956, 5218872685, 0, 0] := by
  decide +kernel

theorem rows954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t954 = true := by
  decide +kernel

theorem tot954 : totK PD2M8K2 D2M8K2.t954 = [0, 175164747206, 457485595886, 258914423142, 24079649925, 0, 0, 0] := by
  decide +kernel

theorem rows955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t955 = true := by
  decide +kernel

theorem tot955 : totK PD2M8K2 D2M8K2.t955 = [0, 177226638563, 467065622413, 230713739229, 15765530719, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
