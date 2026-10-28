import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8560 = true := by
  decide +kernel

theorem tot8560 : totK PD2M8K2 D2M8K2.t8560 = [90510562517, 311690045976, 336078392340, 157255765483, 13552619715, 0, 0, 0] := by
  decide +kernel

theorem rows8561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8561 = true := by
  decide +kernel

theorem tot8561 : totK PD2M8K2 D2M8K2.t8561 = [199730311162, 475416523893, 221075325346, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8562 = true := by
  decide +kernel

theorem tot8562 : totK PD2M8K2 D2M8K2.t8562 = [51412906490, 320478197056, 427885321393, 97142445901, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8563 = true := by
  decide +kernel

theorem tot8563 : totK PD2M8K2 D2M8K2.t8563 = [93574619190, 380706788671, 395041603382, 54640869560, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
