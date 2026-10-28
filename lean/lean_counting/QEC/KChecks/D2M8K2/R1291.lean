import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5164 = true := by
  decide +kernel

theorem tot5164 : totK PD2M8K2 D2M8K2.t5164 = [0, 0, 0, 193742640805, 484363080910, 228402277733, 13656771860, 0] := by
  decide +kernel

theorem rows5165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5165 = true := by
  decide +kernel

theorem tot5165 : totK PD2M8K2 D2M8K2.t5165 = [0, 0, 88388825251, 340832781654, 368837850303, 94841753206, 1409560813, 0] := by
  decide +kernel

theorem rows5166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5166 = true := by
  decide +kernel

theorem tot5166 : totK PD2M8K2 D2M8K2.t5166 = [0, 0, 178076243657, 447514221465, 274217430370, 28463383122, 0, 0] := by
  decide +kernel

theorem rows5167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5167 = true := by
  decide +kernel

theorem tot5167 : totK PD2M8K2 D2M8K2.t5167 = [0, 0, 171251246847, 471751877102, 247952468145, 15693468341, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
