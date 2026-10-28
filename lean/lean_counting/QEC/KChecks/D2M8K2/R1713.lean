import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6852 = true := by
  decide +kernel

theorem tot6852 : totK PD2M8K2 D2M8K2.t6852 = [0, 44561602076, 363684177034, 434270078452, 46397948620, 0, 0, 0] := by
  decide +kernel

theorem rows6853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6853 = true := by
  decide +kernel

theorem tot6853 : totK PD2M8K2 D2M8K2.t6853 = [0, 182877373343, 453353614653, 258939830574, 25969295659, 0, 0, 0] := by
  decide +kernel

theorem rows6854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6854 = true := by
  decide +kernel

theorem tot6854 : totK PD2M8K2 D2M8K2.t6854 = [0, 175899221893, 485896858554, 240768030057, 12309185191, 0, 0, 0] := by
  decide +kernel

theorem rows6855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6855 = true := by
  decide +kernel

theorem tot6855 : totK PD2M8K2 D2M8K2.t6855 = [0, 171982751285, 448036742100, 248942470760, 23859846630, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
