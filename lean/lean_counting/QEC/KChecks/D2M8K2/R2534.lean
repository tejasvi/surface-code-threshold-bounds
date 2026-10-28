import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10136 = true := by
  decide +kernel

theorem tot10136 : totK PD2M8K2 D2M8K2.t10136 = [0, 159456292539, 442843185962, 283692934834, 30508507079, 0, 0, 0] := by
  decide +kernel

theorem rows10137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10137 = true := by
  decide +kernel

theorem tot10137 : totK PD2M8K2 D2M8K2.t10137 = [0, 107057073325, 401485013509, 330384902850, 52318639815, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10138 = true := by
  decide +kernel

theorem tot10138 : totK PD2M8K2 D2M8K2.t10138 = [0, 0, 228729665184, 489224587500, 169341443932, 8470662040, 0, 0] := by
  decide +kernel

theorem rows10139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10139 = true := by
  decide +kernel

theorem tot10139 : totK PD2M8K2 D2M8K2.t10139 = [0, 103462568247, 343543690969, 337129064445, 94108489470, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
