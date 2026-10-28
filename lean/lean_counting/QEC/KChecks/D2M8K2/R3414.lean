import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13656 = true := by
  decide +kernel

theorem tot13656 : totK PD2M8K2 D2M8K2.t13656 = [0, 0, 282670965196, 506467015225, 83379685999, 1310285577, 0, 0] := by
  decide +kernel

theorem rows13657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13657 = true := by
  decide +kernel

theorem tot13657 : totK PD2M8K2 D2M8K2.t13657 = [0, 173929479270, 427803282205, 294026138231, 38861692627, 0, 0, 0] := by
  decide +kernel

theorem rows13658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13658 = true := by
  decide +kernel

theorem tot13658 : totK PD2M8K2 D2M8K2.t13658 = [0, 173474269613, 470759243139, 258151015461, 14332825664, 0, 0, 0] := by
  decide +kernel

theorem rows13659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13659 = true := by
  decide +kernel

theorem tot13659 : totK PD2M8K2 D2M8K2.t13659 = [0, 165581325127, 451981034292, 263927889917, 27435908694, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
