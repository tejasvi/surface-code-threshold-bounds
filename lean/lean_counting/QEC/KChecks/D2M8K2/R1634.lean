import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6536 = true := by
  decide +kernel

theorem tot6536 : totK PD2M8K2 D2M8K2.t6536 = [0, 169515922385, 460625521722, 267745865873, 23282239808, 0, 0, 0] := by
  decide +kernel

theorem rows6537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6537 = true := by
  decide +kernel

theorem tot6537 : totK PD2M8K2 D2M8K2.t6537 = [0, 160878688799, 470031926897, 256034379672, 15136521286, 0, 0, 0] := by
  decide +kernel

theorem rows6538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6538 = true := by
  decide +kernel

theorem tot6538 : totK PD2M8K2 D2M8K2.t6538 = [0, 0, 223847967334, 471779997108, 162720221083, 7162593164, 0, 0] := by
  decide +kernel

theorem rows6539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6539 = true := by
  decide +kernel

theorem tot6539 : totK PD2M8K2 D2M8K2.t6539 = [0, 83655740246, 309179321293, 353069685759, 105918058136, 4879115834, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
