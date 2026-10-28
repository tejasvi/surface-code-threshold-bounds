import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16140 = true := by
  decide +kernel

theorem tot16140 : totK PD2M8K2 D2M8K2.t16140 = [0, 0, 202293926946, 480142585693, 185405473263, 11885407614, 0, 0] := by
  decide +kernel

theorem rows16141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16141 = true := by
  decide +kernel

theorem tot16141 : totK PD2M8K2 D2M8K2.t16141 = [0, 173960204262, 440287939624, 263465423611, 28919679125, 0, 0, 0] := by
  decide +kernel

theorem rows16142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16142 = true := by
  decide +kernel

theorem tot16142 : totK PD2M8K2 D2M8K2.t16142 = [0, 150009753740, 454177440467, 268670800709, 21598398773, 0, 0, 0] := by
  decide +kernel

theorem rows16143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16143 = true := by
  decide +kernel

theorem tot16143 : totK PD2M8K2 D2M8K2.t16143 = [0, 18464490943, 296312882611, 496374598455, 92743242427, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
