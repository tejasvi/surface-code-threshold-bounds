import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15436 = true := by
  decide +kernel

theorem tot15436 : totK PD2M8K2 D2M8K2.t15436 = [0, 0, 63523070268, 322192706352, 405077787125, 78294807529, 1376099875, 0] := by
  decide +kernel

theorem rows15437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15437 = true := by
  decide +kernel

theorem tot15437 : totK PD2M8K2 D2M8K2.t15437 = [0, 0, 173056832879, 458273867242, 258715123867, 21973649153, 0, 0] := by
  decide +kernel

theorem rows15438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15438 = true := by
  decide +kernel

theorem tot15438 : totK PD2M8K2 D2M8K2.t15438 = [0, 0, 180937872387, 480597225996, 243387775759, 12296333469, 0, 0] := by
  decide +kernel

theorem rows15439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15439 = true := by
  decide +kernel

theorem tot15439 : totK PD2M8K2 D2M8K2.t15439 = [0, 180280610855, 391433016387, 252626458217, 87551556545, 11282097018, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
