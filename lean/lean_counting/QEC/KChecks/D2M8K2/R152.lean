import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t608 = true := by
  decide +kernel

theorem tot608 : totK PD2M8K2 D2M8K2.t608 = [0, 194632937419, 469205128764, 203832260573, 12206147664, 0, 0, 0] := by
  decide +kernel

theorem rows609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t609 = true := by
  decide +kernel

theorem tot609 : totK PD2M8K2 D2M8K2.t609 = [0, 26146271661, 308978987755, 429525398529, 97993228380, 1369150432, 0, 0] := by
  decide +kernel

theorem rows610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t610 = true := by
  decide +kernel

theorem tot610 : totK PD2M8K2 D2M8K2.t610 = [0, 87092486433, 392009823083, 353362389763, 43138632098, 0, 0, 0] := by
  decide +kernel

theorem rows611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t611 = true := by
  decide +kernel

theorem tot611 : totK PD2M8K2 D2M8K2.t611 = [0, 170003699201, 477375840632, 229436924258, 10904930701, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
