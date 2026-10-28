import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2564 = true := by
  decide +kernel

theorem tot2564 : totK PD2M8K2 D2M8K2.t2564 = [17442593718, 196866950064, 455934625904, 195872541956, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows2565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2565 = true := by
  decide +kernel

theorem tot2565 : totK PD2M8K2 D2M8K2.t2565 = [188770124744, 456541591864, 246766429528, 23236262830, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2566 = true := by
  decide +kernel

theorem tot2566 : totK PD2M8K2 D2M8K2.t2566 = [187261973574, 460517174419, 240803945000, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2567 = true := by
  decide +kernel

theorem tot2567 : totK PD2M8K2 D2M8K2.t2567 = [44583298060, 338917372121, 425445410022, 82836113947, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
