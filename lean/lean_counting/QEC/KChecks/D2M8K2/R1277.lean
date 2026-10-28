import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5108 = true := by
  decide +kernel

theorem tot5108 : totK PD2M8K2 D2M8K2.t5108 = [0, 0, 0, 290025548910, 515871264751, 87857256602, 1369150432, 0] := by
  decide +kernel

theorem rows5109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5109 = true := by
  decide +kernel

theorem tot5109 : totK PD2M8K2 D2M8K2.t5109 = [0, 0, 176369658508, 461265205835, 260213232338, 13627218743, 0, 0] := by
  decide +kernel

theorem rows5110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5110 = true := by
  decide +kernel

theorem tot5110 : totK PD2M8K2 D2M8K2.t5110 = [0, 0, 188726117879, 467969629685, 217433419183, 12373752831, 0, 0] := by
  decide +kernel

theorem rows5111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5111 = true := by
  decide +kernel

theorem tot5111 : totK PD2M8K2 D2M8K2.t5111 = [0, 0, 29729080133, 326520340886, 456689665386, 71299971569, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
