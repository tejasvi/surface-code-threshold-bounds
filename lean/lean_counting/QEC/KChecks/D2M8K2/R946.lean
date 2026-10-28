import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3784 = true := by
  decide +kernel

theorem tot3784 : totK PD2M8K2 D2M8K2.t3784 = [0, 167548478164, 457819011397, 266238497254, 23282239808, 0, 0, 0] := by
  decide +kernel

theorem rows3785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3785 = true := by
  decide +kernel

theorem tot3785 : totK PD2M8K2 D2M8K2.t3785 = [0, 111079033344, 432067012287, 309763806393, 25415650466, 0, 0, 0] := by
  decide +kernel

theorem rows3786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3786 = true := by
  decide +kernel

theorem tot3786 : totK PD2M8K2 D2M8K2.t3786 = [0, 0, 213535007998, 466162919939, 176621731562, 9579374723, 0, 0] := by
  decide +kernel

theorem rows3787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3787 = true := by
  decide +kernel

theorem tot3787 : totK PD2M8K2 D2M8K2.t3787 = [0, 103967259011, 345957787942, 328821857074, 81978008844, 3436822651, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
