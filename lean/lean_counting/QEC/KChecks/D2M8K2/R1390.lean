import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5560 = true := by
  decide +kernel

theorem tot5560 : totK PD2M8K2 D2M8K2.t5560 = [0, 86538753630, 341273211475, 372819446405, 69871818269, 1206465782, 0, 0] := by
  decide +kernel

theorem rows5561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5561 = true := by
  decide +kernel

theorem tot5561 : totK PD2M8K2 D2M8K2.t5561 = [0, 71454938186, 382319659386, 396568158597, 38217878931, 0, 0, 0] := by
  decide +kernel

theorem rows5562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5562 = true := by
  decide +kernel

theorem tot5562 : totK PD2M8K2 D2M8K2.t5562 = [0, 171368979081, 450232891442, 268620155698, 29048003836, 0, 0, 0] := by
  decide +kernel

theorem rows5563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5563 = true := by
  decide +kernel

theorem tot5563 : totK PD2M8K2 D2M8K2.t5563 = [0, 189682363638, 481003971147, 221192250285, 14210185855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
