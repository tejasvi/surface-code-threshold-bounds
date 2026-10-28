import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3844 = true := by
  decide +kernel

theorem tot3844 : totK PD2M8K2 D2M8K2.t3844 = [160572908506, 423463723271, 274908576242, 54938025658, 2428283778, 0, 0, 0] := by
  decide +kernel

theorem rows3845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3845 = true := by
  decide +kernel

theorem tot3845 : totK PD2M8K2 D2M8K2.t3845 = [170008876499, 445377088300, 279209430999, 29922129656, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3846 = true := by
  decide +kernel

theorem tot3846 : totK PD2M8K2 D2M8K2.t3846 = [112931552984, 432311613357, 340432829905, 30257218484, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3847 = true := by
  decide +kernel

theorem tot3847 : totK PD2M8K2 D2M8K2.t3847 = [0, 213623013292, 493097207241, 178113229706, 4967996017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
