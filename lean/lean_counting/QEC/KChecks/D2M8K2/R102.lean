import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t408 = true := by
  decide +kernel

theorem tot408 : totK PD2M8K2 D2M8K2.t408 = [0, 152269250939, 444667013424, 277269440380, 29084825710, 0, 0, 0] := by
  decide +kernel

theorem rows409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t409 = true := by
  decide +kernel

theorem tot409 : totK PD2M8K2 D2M8K2.t409 = [0, 192271141592, 464182848867, 223887378834, 15822533856, 0, 0, 0] := by
  decide +kernel

theorem rows410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t410 = true := by
  decide +kernel

theorem tot410 : totK PD2M8K2 D2M8K2.t410 = [0, 198379568420, 480145627736, 212654243380, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t411 = true := by
  decide +kernel

theorem tot411 : totK PD2M8K2 D2M8K2.t411 = [0, 166085612973, 465550703573, 238264387896, 13494115512, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
