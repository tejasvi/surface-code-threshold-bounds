import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5740 = true := by
  decide +kernel

theorem tot5740 : totK PD2M8K2 D2M8K2.t5740 = [0, 191626582841, 487585928707, 205912764337, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows5741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5741 = true := by
  decide +kernel

theorem tot5741 : totK PD2M8K2 D2M8K2.t5741 = [0, 192158505887, 462491194412, 215698216464, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows5742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5742 = true := by
  decide +kernel

theorem tot5742 : totK PD2M8K2 D2M8K2.t5742 = [0, 18544188537, 288644012188, 460732639589, 105118462915, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5743 = true := by
  decide +kernel

theorem tot5743 : totK PD2M8K2 D2M8K2.t5743 = [0, 88686713164, 379354377250, 395025886635, 46293646232, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
