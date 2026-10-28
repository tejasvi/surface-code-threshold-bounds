import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14336 = true := by
  decide +kernel

theorem tot14336 : totK PD2M8K2 D2M8K2.t14336 = [0, 204985722309, 456890722390, 227796081335, 18933214105, 0, 0, 0] := by
  decide +kernel

theorem rows14337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14337 = true := by
  decide +kernel

theorem tot14337 : totK PD2M8K2 D2M8K2.t14337 = [0, 36101142161, 385582496449, 429716609534, 51662321458, 0, 0, 0] := by
  decide +kernel

theorem rows14338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14338 = true := by
  decide +kernel

theorem tot14338 : totK PD2M8K2 D2M8K2.t14338 = [0, 68245153917, 324218091964, 391541423472, 105504298516, 3880716147, 0, 0] := by
  decide +kernel

theorem rows14339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14339 = true := by
  decide +kernel

theorem tot14339 : totK PD2M8K2 D2M8K2.t14339 = [0, 177671727350, 447322316331, 274121703195, 29322329664, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
