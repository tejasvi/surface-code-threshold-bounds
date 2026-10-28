import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3728 = true := by
  decide +kernel

theorem tot3728 : totK PD2M8K2 D2M8K2.t3728 = [167333634553, 466793873076, 257479585143, 16280491352, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3729 = true := by
  decide +kernel

theorem tot3729 : totK PD2M8K2 D2M8K2.t3729 = [0, 246190412609, 503625580251, 142917569457, 2345745033, 0, 0, 0] := by
  decide +kernel

theorem rows3730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3730 = true := by
  decide +kernel

theorem tot3730 : totK PD2M8K2 D2M8K2.t3730 = [66702123594, 264003029969, 404636920581, 151755036067, 10734237504, 0, 0, 0] := by
  decide +kernel

theorem rows3731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3731 = true := by
  decide +kernel

theorem tot3731 : totK PD2M8K2 D2M8K2.t3731 = [172486767466, 443826649622, 278508806455, 30399014434, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
