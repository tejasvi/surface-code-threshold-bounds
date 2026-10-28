import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4304 = true := by
  decide +kernel

theorem tot4304 : totK PD2M8K2 D2M8K2.t4304 = [0, 0, 75211705367, 378099053297, 416018506710, 42880747447, 0, 0] := by
  decide +kernel

theorem rows4305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4305 = true := by
  decide +kernel

theorem tot4305 : totK PD2M8K2 D2M8K2.t4305 = [0, 0, 169389590540, 436124734008, 278834846309, 30225738344, 0, 0] := by
  decide +kernel

theorem rows4306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4306 = true := by
  decide +kernel

theorem tot4306 : totK PD2M8K2 D2M8K2.t4306 = [0, 0, 179880361390, 485700130332, 230741355933, 11903887087, 0, 0] := by
  decide +kernel

theorem rows4307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4307 = true := by
  decide +kernel

theorem tot4307 : totK PD2M8K2 D2M8K2.t4307 = [0, 0, 0, 240963831781, 450098069681, 195061834898, 21396654552, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
