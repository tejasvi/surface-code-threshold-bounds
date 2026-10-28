import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11624 = true := by
  decide +kernel

theorem tot11624 : totK PD2M8K2 D2M8K2.t11624 = [0, 58762601873, 402260671972, 407030399115, 40295321243, 0, 0, 0] := by
  decide +kernel

theorem rows11625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11625 = true := by
  decide +kernel

theorem tot11625 : totK PD2M8K2 D2M8K2.t11625 = [0, 52654094294, 302643225247, 437831482414, 101517492018, 1415142070, 0, 0] := by
  decide +kernel

theorem rows11626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11626 = true := by
  decide +kernel

theorem tot11626 : totK PD2M8K2 D2M8K2.t11626 = [0, 176094856900, 449675114598, 266433448906, 27343338882, 0, 0, 0] := by
  decide +kernel

theorem rows11627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11627 = true := by
  decide +kernel

theorem tot11627 : totK PD2M8K2 D2M8K2.t11627 = [0, 157332909390, 452907866691, 276742199890, 21371213000, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
