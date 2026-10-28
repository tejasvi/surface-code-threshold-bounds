import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10960 = true := by
  decide +kernel

theorem tot10960 : totK PD2M8K2 D2M8K2.t10960 = [0, 195593853481, 472295244557, 188624126069, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows10961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10961 = true := by
  decide +kernel

theorem tot10961 : totK PD2M8K2 D2M8K2.t10961 = [0, 195477142692, 471519379093, 216110380290, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows10962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10962 = true := by
  decide +kernel

theorem tot10962 : totK PD2M8K2 D2M8K2.t10962 = [0, 184522781806, 454876752774, 220406185243, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows10963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10963 = true := by
  decide +kernel

theorem tot10963 : totK PD2M8K2 D2M8K2.t10963 = [0, 94885094023, 416520027837, 325173142205, 33638808570, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
