import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2132 = true := by
  decide +kernel

theorem tot2132 : totK PD2M8K2 D2M8K2.t2132 = [0, 0, 154249941093, 463167119648, 247997097473, 14324129885, 0, 0] := by
  decide +kernel

theorem rows2133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2133 = true := by
  decide +kernel

theorem tot2133 : totK PD2M8K2 D2M8K2.t2133 = [0, 0, 194719066528, 463863897469, 212963347872, 12319708528, 0, 0] := by
  decide +kernel

theorem rows2134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2134 = true := by
  decide +kernel

theorem tot2134 : totK PD2M8K2 D2M8K2.t2134 = [0, 0, 202501545749, 476086647575, 202411469404, 10178307621, 0, 0] := by
  decide +kernel

theorem rows2135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2135 = true := by
  decide +kernel

theorem tot2135 : totK PD2M8K2 D2M8K2.t2135 = [0, 0, 190339195163, 482127794555, 201888674576, 9757737807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
