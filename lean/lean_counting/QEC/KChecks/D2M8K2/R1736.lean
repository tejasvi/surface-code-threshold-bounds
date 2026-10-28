import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6944 = true := by
  decide +kernel

theorem tot6944 : totK PD2M8K2 D2M8K2.t6944 = [0, 160323446548, 446659034892, 281357038149, 24359691996, 0, 0, 0] := by
  decide +kernel

theorem rows6945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6945 = true := by
  decide +kernel

theorem tot6945 : totK PD2M8K2 D2M8K2.t6945 = [0, 79844485789, 408456918466, 389383712122, 49643532545, 0, 0, 0] := by
  decide +kernel

theorem rows6946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6946 = true := by
  decide +kernel

theorem tot6946 : totK PD2M8K2 D2M8K2.t6946 = [0, 90805814765, 345984058585, 370005361775, 86161709346, 1429815836, 0, 0] := by
  decide +kernel

theorem rows6947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6947 = true := by
  decide +kernel

theorem tot6947 : totK PD2M8K2 D2M8K2.t6947 = [0, 173585018239, 438567639990, 272546493360, 29853396860, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
