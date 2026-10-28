import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t716 = true := by
  decide +kernel

theorem tot716 : totK PD2M8K2 D2M8K2.t716 = [0, 194869342388, 479038045753, 216577763047, 11066126582, 0, 0, 0] := by
  decide +kernel

theorem rows717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t717 = true := by
  decide +kernel

theorem tot717 : totK PD2M8K2 D2M8K2.t717 = [0, 191668632899, 469831168672, 223263592438, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t718 = true := by
  decide +kernel

theorem tot718 : totK PD2M8K2 D2M8K2.t718 = [0, 171413320796, 479069961119, 221400859126, 12606028130, 0, 0, 0] := by
  decide +kernel

theorem rows719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t719 = true := by
  decide +kernel

theorem tot719 : totK PD2M8K2 D2M8K2.t719 = [0, 169684987765, 447408370767, 247242481202, 17575085233, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
