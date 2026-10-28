import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7684 = true := by
  decide +kernel

theorem tot7684 : totK PD2M8K2 D2M8K2.t7684 = [0, 0, 191584127927, 467866180383, 247874543594, 21660034663, 0, 0] := by
  decide +kernel

theorem rows7685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7685 = true := by
  decide +kernel

theorem tot7685 : totK PD2M8K2 D2M8K2.t7685 = [0, 0, 185637286462, 468986135538, 220095819070, 12313560678, 0, 0] := by
  decide +kernel

theorem rows7686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7686 = true := by
  decide +kernel

theorem tot7686 : totK PD2M8K2 D2M8K2.t7686 = [0, 0, 11817147487, 358725206442, 482024315909, 64532082069, 0, 0] := by
  decide +kernel

theorem rows7687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7687 = true := by
  decide +kernel

theorem tot7687 : totK PD2M8K2 D2M8K2.t7687 = [0, 0, 35351919140, 228929741054, 462914472241, 155153894440, 9751947372, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
