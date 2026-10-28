import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14004 = true := by
  decide +kernel

theorem tot14004 : totK PD2M8K2 D2M8K2.t14004 = [0, 0, 204926134126, 467281539395, 188080562830, 11885407614, 0, 0] := by
  decide +kernel

theorem rows14005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14005 = true := by
  decide +kernel

theorem tot14005 : totK PD2M8K2 D2M8K2.t14005 = [0, 151660303848, 426992095835, 296067205473, 40214852490, 0, 0, 0] := by
  decide +kernel

theorem rows14006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14006 = true := by
  decide +kernel

theorem tot14006 : totK PD2M8K2 D2M8K2.t14006 = [0, 176660981710, 444909593926, 259998802324, 22592241082, 0, 0, 0] := by
  decide +kernel

theorem rows14007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14007 = true := by
  decide +kernel

theorem tot14007 : totK PD2M8K2 D2M8K2.t14007 = [0, 53863044318, 344609875458, 407731895009, 73194165355, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
