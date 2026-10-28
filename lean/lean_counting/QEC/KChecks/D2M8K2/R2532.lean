import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10128 = true := by
  decide +kernel

theorem tot10128 : totK PD2M8K2 D2M8K2.t10128 = [0, 188191614521, 473537178822, 239318069087, 13862485851, 0, 0, 0] := by
  decide +kernel

theorem rows10129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10129 = true := by
  decide +kernel

theorem tot10129 : totK PD2M8K2 D2M8K2.t10129 = [0, 61228868694, 287729887347, 360682087353, 175506504628, 21396654552, 0, 0] := by
  decide +kernel

theorem rows10130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10130 = true := by
  decide +kernel

theorem tot10130 : totK PD2M8K2 D2M8K2.t10130 = [0, 0, 200705635001, 484066243161, 207037595596, 7994456143, 0, 0] := by
  decide +kernel

theorem rows10131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10131 = true := by
  decide +kernel

theorem tot10131 : totK PD2M8K2 D2M8K2.t10131 = [0, 63557947097, 241377087456, 392787039261, 184722790972, 8210597527, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
