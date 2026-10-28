import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15208 = true := by
  decide +kernel

theorem tot15208 : totK PD2M8K2 D2M8K2.t15208 = [0, 181674658392, 464638746693, 251882908218, 18778638214, 0, 0, 0] := by
  decide +kernel

theorem rows15209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15209 = true := by
  decide +kernel

theorem tot15209 : totK PD2M8K2 D2M8K2.t15209 = [0, 0, 274627007705, 510275434133, 121642539666, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15210 = true := by
  decide +kernel

theorem tot15210 : totK PD2M8K2 D2M8K2.t15210 = [0, 0, 199227356324, 487481469965, 190750923526, 7442000727, 0, 0] := by
  decide +kernel

theorem rows15211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15211 = true := by
  decide +kernel

theorem tot15211 : totK PD2M8K2 D2M8K2.t15211 = [0, 0, 176266447934, 464004460566, 235004783858, 15859045170, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
