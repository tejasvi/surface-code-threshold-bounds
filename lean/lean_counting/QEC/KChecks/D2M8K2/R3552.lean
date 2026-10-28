import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14208 = true := by
  decide +kernel

theorem tot14208 : totK PD2M8K2 D2M8K2.t14208 = [179818945336, 462063130758, 246542377911, 23054447867, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14209 = true := by
  decide +kernel

theorem tot14209 : totK PD2M8K2 D2M8K2.t14209 = [209596290868, 478917729288, 222917998363, 12957177548, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14210 = true := by
  decide +kernel

theorem tot14210 : totK PD2M8K2 D2M8K2.t14210 = [23713104488, 310851713104, 456147253784, 101895597128, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14211 = true := by
  decide +kernel

theorem tot14211 : totK PD2M8K2 D2M8K2.t14211 = [0, 216196462334, 486374711703, 184980645650, 7423899238, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
