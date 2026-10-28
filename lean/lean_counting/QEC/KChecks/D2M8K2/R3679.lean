import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14716 = true := by
  decide +kernel

theorem tot14716 : totK PD2M8K2 D2M8K2.t14716 = [0, 37815634106, 282112901024, 398446164295, 177837260528, 19374288140, 0, 0] := by
  decide +kernel

theorem rows14717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14717 = true := by
  decide +kernel

theorem tot14717 : totK PD2M8K2 D2M8K2.t14717 = [0, 0, 205772383864, 496716312854, 190625433034, 5352136967, 0, 0] := by
  decide +kernel

theorem rows14718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14718 = true := by
  decide +kernel

theorem tot14718 : totK PD2M8K2 D2M8K2.t14718 = [0, 81086874887, 283430486063, 352476095140, 157593219601, 8078182869, 0, 0] := by
  decide +kernel

theorem rows14719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14719 = true := by
  decide +kernel

theorem tot14719 : totK PD2M8K2 D2M8K2.t14719 = [0, 177741805421, 454916660098, 268566118910, 25712697137, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
