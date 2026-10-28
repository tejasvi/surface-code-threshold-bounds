import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3460 = true := by
  decide +kernel

theorem tot3460 : totK PD2M8K2 D2M8K2.t3460 = [0, 167805406930, 442086835327, 281834450195, 30435711819, 0, 0, 0] := by
  decide +kernel

theorem rows3461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3461 = true := by
  decide +kernel

theorem tot3461 : totK PD2M8K2 D2M8K2.t3461 = [0, 156632724252, 465777270045, 261564603000, 16578598723, 0, 0, 0] := by
  decide +kernel

theorem rows3462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3462 = true := by
  decide +kernel

theorem tot3462 : totK PD2M8K2 D2M8K2.t3462 = [0, 0, 265102306043, 493514079095, 133000533151, 4031931762, 0, 0] := by
  decide +kernel

theorem rows3463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3463 = true := by
  decide +kernel

theorem tot3463 : totK PD2M8K2 D2M8K2.t3463 = [0, 136082462504, 364162838033, 311947686473, 70259146981, 1186940923, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
