import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13768 = true := by
  decide +kernel

theorem tot13768 : totK PD2M8K2 D2M8K2.t13768 = [0, 176085565224, 446124253101, 266222457729, 28430628693, 0, 0, 0] := by
  decide +kernel

theorem rows13769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13769 = true := by
  decide +kernel

theorem tot13769 : totK PD2M8K2 D2M8K2.t13769 = [0, 105748163471, 419207417144, 338041703992, 32729287250, 0, 0, 0] := by
  decide +kernel

theorem rows13770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13770 = true := by
  decide +kernel

theorem tot13770 : totK PD2M8K2 D2M8K2.t13770 = [0, 0, 220219605684, 501372044175, 163450243396, 5193381917, 0, 0] := by
  decide +kernel

theorem rows13771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13771 = true := by
  decide +kernel

theorem tot13771 : totK PD2M8K2 D2M8K2.t13771 = [0, 173127692068, 446454294457, 270852377509, 29871776970, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
