import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13692 = true := by
  decide +kernel

theorem tot13692 : totK PD2M8K2 D2M8K2.t13692 = [0, 0, 169965993499, 446980833419, 226126913497, 17714277454, 0, 0] := by
  decide +kernel

theorem rows13693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13693 = true := by
  decide +kernel

theorem tot13693 : totK PD2M8K2 D2M8K2.t13693 = [0, 0, 86408083722, 358959714188, 345515892190, 76048351171, 1369150432, 0] := by
  decide +kernel

theorem rows13694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13694 = true := by
  decide +kernel

theorem tot13694 : totK PD2M8K2 D2M8K2.t13694 = [0, 0, 0, 333345577498, 447678459606, 66683406972, 0, 0] := by
  decide +kernel

theorem rows13695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13695 = true := by
  decide +kernel

theorem tot13695 : totK PD2M8K2 D2M8K2.t13695 = [0, 0, 242881387150, 502216343035, 146540667346, 2519764721, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
