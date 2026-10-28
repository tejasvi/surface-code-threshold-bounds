import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11828 = true := by
  decide +kernel

theorem tot11828 : totK PD2M8K2 D2M8K2.t11828 = [0, 176587901273, 478284400242, 244883206634, 13993426319, 0, 0, 0] := by
  decide +kernel

theorem rows11829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11829 = true := by
  decide +kernel

theorem tot11829 : totK PD2M8K2 D2M8K2.t11829 = [0, 0, 282893092546, 513397702852, 93356693608, 1104198603, 0, 0] := by
  decide +kernel

theorem rows11830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11830 = true := by
  decide +kernel

theorem tot11830 : totK PD2M8K2 D2M8K2.t11830 = [0, 159431464963, 368718065084, 277528068026, 75654180550, 3581949829, 0, 0] := by
  decide +kernel

theorem rows11831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11831 = true := by
  decide +kernel

theorem tot11831 : totK PD2M8K2 D2M8K2.t11831 = [0, 168007180739, 442478978604, 278588144239, 29827517865, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
