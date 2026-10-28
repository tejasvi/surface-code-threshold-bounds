import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9752 = true := by
  decide +kernel

theorem tot9752 : totK PD2M8K2 D2M8K2.t9752 = [0, 0, 171998504557, 452578670803, 229205666611, 13563057169, 0, 0] := by
  decide +kernel

theorem rows9753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9753 = true := by
  decide +kernel

theorem tot9753 : totK PD2M8K2 D2M8K2.t9753 = [0, 0, 53162786565, 351499656132, 397643561611, 67117698892, 1054738420, 0] := by
  decide +kernel

theorem rows9754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9754 = true := by
  decide +kernel

theorem tot9754 : totK PD2M8K2 D2M8K2.t9754 = [0, 0, 50317622654, 290665198939, 408426627067, 99737695152, 3732315745, 0] := by
  decide +kernel

theorem rows9755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9755 = true := by
  decide +kernel

theorem tot9755 : totK PD2M8K2 D2M8K2.t9755 = [0, 0, 210545773663, 476048311904, 199864211182, 11433198393, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
