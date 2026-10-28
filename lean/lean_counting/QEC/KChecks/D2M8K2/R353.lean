import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1412 = true := by
  decide +kernel

theorem tot1412 : totK PD2M8K2 D2M8K2.t1412 = [0, 0, 195379908654, 470652274266, 194816152983, 11885407614, 0, 0] := by
  decide +kernel

theorem rows1413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1413 = true := by
  decide +kernel

theorem tot1413 : totK PD2M8K2 D2M8K2.t1413 = [0, 182857076785, 454834719725, 250282342454, 21107630635, 0, 0, 0] := by
  decide +kernel

theorem rows1414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1414 = true := by
  decide +kernel

theorem tot1414 : totK PD2M8K2 D2M8K2.t1414 = [0, 139006180021, 457537324433, 276675956039, 18570747137, 0, 0, 0] := by
  decide +kernel

theorem rows1415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1415 = true := by
  decide +kernel

theorem tot1415 : totK PD2M8K2 D2M8K2.t1415 = [0, 0, 271997754418, 515111281444, 100000467430, 1062926506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
