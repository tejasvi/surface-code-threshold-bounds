import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t396 = true := by
  decide +kernel

theorem tot396 : totK PD2M8K2 D2M8K2.t396 = [7199099248, 195796265390, 471435744940, 190977932909, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t397 = true := by
  decide +kernel

theorem tot397 : totK PD2M8K2 D2M8K2.t397 = [198541509922, 469081932179, 225678351416, 18895410991, 0, 0, 0, 0] := by
  decide +kernel

theorem rows398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t398 = true := by
  decide +kernel

theorem tot398 : totK PD2M8K2 D2M8K2.t398 = [117156360000, 441203339209, 314517898070, 22822684289, 0, 0, 0, 0] := by
  decide +kernel

theorem rows399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t399 = true := by
  decide +kernel

theorem tot399 : totK PD2M8K2 D2M8K2.t399 = [0, 204812199272, 478129731100, 188168852851, 9668735432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
