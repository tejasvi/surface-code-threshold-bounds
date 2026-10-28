import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11524 = true := by
  decide +kernel

theorem tot11524 : totK PD2M8K2 D2M8K2.t11524 = [0, 0, 223388331280, 487126834189, 184766562371, 5194285841, 0, 0] := by
  decide +kernel

theorem rows11525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11525 = true := by
  decide +kernel

theorem tot11525 : totK PD2M8K2 D2M8K2.t11525 = [0, 0, 186861100866, 475592312474, 223747825023, 15844255384, 0, 0] := by
  decide +kernel

theorem rows11526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11526 = true := by
  decide +kernel

theorem tot11526 : totK PD2M8K2 D2M8K2.t11526 = [0, 0, 179858698636, 462616782722, 226411953416, 16702988424, 0, 0] := by
  decide +kernel

theorem rows11527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11527 = true := by
  decide +kernel

theorem tot11527 : totK PD2M8K2 D2M8K2.t11527 = [0, 0, 0, 366317089408, 445617952300, 50949468081, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
