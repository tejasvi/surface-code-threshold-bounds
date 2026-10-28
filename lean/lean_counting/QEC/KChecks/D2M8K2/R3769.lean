import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15076 = true := by
  decide +kernel

theorem tot15076 : totK PD2M8K2 D2M8K2.t15076 = [0, 140110859336, 446301278925, 285023023967, 20074333972, 0, 0, 0] := by
  decide +kernel

theorem rows15077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15077 = true := by
  decide +kernel

theorem tot15077 : totK PD2M8K2 D2M8K2.t15077 = [0, 0, 200387295186, 483460306218, 185655773435, 9668735432, 0, 0] := by
  decide +kernel

theorem rows15078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15078 = true := by
  decide +kernel

theorem tot15078 : totK PD2M8K2 D2M8K2.t15078 = [0, 87770539582, 311334320019, 376029941362, 101209822458, 3581949829, 0, 0] := by
  decide +kernel

theorem rows15079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15079 = true := by
  decide +kernel

theorem tot15079 : totK PD2M8K2 D2M8K2.t15079 = [0, 153075924431, 439066891102, 261773179399, 17019330593, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
