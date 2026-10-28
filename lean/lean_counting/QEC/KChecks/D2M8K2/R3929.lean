import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15716 = true := by
  decide +kernel

theorem tot15716 : totK PD2M8K2 D2M8K2.t15716 = [0, 0, 0, 276076022659, 502485184396, 126450465311, 3693668399, 0] := by
  decide +kernel

theorem rows15717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15717 = true := by
  decide +kernel

theorem tot15717 : totK PD2M8K2 D2M8K2.t15717 = [0, 0, 156837995044, 366842110042, 271029837768, 104652040628, 8907841751, 0] := by
  decide +kernel

theorem rows15718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15718 = true := by
  decide +kernel

theorem tot15718 : totK PD2M8K2 D2M8K2.t15718 = [0, 0, 166960648896, 462516150044, 215155135288, 10749708610, 0, 0] := by
  decide +kernel

theorem rows15719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15719 = true := by
  decide +kernel

theorem tot15719 : totK PD2M8K2 D2M8K2.t15719 = [0, 0, 86341316635, 342606360387, 369849779644, 72000910955, 1334361349, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
