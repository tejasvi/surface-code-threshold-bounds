import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9692 = true := by
  decide +kernel

theorem tot9692 : totK PD2M8K2 D2M8K2.t9692 = [0, 172984074532, 419459625816, 202125391406, 75477626542, 12306479239, 0, 0] := by
  decide +kernel

theorem rows9693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9693 = true := by
  decide +kernel

theorem tot9693 : totK PD2M8K2 D2M8K2.t9693 = [0, 192921693255, 466571161701, 219604584761, 12430109507, 0, 0, 0] := by
  decide +kernel

theorem rows9694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9694 = true := by
  decide +kernel

theorem tot9694 : totK PD2M8K2 D2M8K2.t9694 = [0, 37567887526, 306111863336, 440456716785, 94434271843, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9695 = true := by
  decide +kernel

theorem tot9695 : totK PD2M8K2 D2M8K2.t9695 = [0, 88833259043, 373482015805, 408130833161, 47112820347, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
