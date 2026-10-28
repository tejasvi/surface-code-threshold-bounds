import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7344 = true := by
  decide +kernel

theorem tot7344 : totK PD2M8K2 D2M8K2.t7344 = [0, 61199238661, 80840006607, 156757094452, 403351826425, 171398487267, 8063697217, 0] := by
  decide +kernel

theorem rows7345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7345 = true := by
  decide +kernel

theorem tot7345 : totK PD2M8K2 D2M8K2.t7345 = [0, 196225097327, 488794853235, 206355182752, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows7346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7346 = true := by
  decide +kernel

theorem tot7346 : totK PD2M8K2 D2M8K2.t7346 = [0, 84125543773, 379604069253, 359885802029, 63947064377, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7347 = true := by
  decide +kernel

theorem tot7347 : totK PD2M8K2 D2M8K2.t7347 = [0, 59183207246, 344589209687, 448568601877, 64009365554, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
