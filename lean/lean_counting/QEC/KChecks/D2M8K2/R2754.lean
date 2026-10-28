import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11016 = true := by
  decide +kernel

theorem tot11016 : totK PD2M8K2 D2M8K2.t11016 = [171270522578, 397420923296, 253376591973, 86396748261, 5558641093, 0, 0, 0] := by
  decide +kernel

theorem rows11017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11017 = true := by
  decide +kernel

theorem tot11017 : totK PD2M8K2 D2M8K2.t11017 = [180194882581, 438351167429, 274728753505, 28270955552, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11018 = true := by
  decide +kernel

theorem tot11018 : totK PD2M8K2 D2M8K2.t11018 = [86218514020, 411069703917, 356684091525, 37557485599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11019 = true := by
  decide +kernel

theorem tot11019 : totK PD2M8K2 D2M8K2.t11019 = [0, 214486219771, 487391696058, 183977256811, 9668735432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
