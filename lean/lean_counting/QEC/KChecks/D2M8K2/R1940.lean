import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7760 = true := by
  decide +kernel

theorem tot7760 : totK PD2M8K2 D2M8K2.t7760 = [0, 0, 0, 200178935900, 461945418253, 181925211246, 11898096860, 0] := by
  decide +kernel

theorem rows7761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7761 = true := by
  decide +kernel

theorem tot7761 : totK PD2M8K2 D2M8K2.t7761 = [0, 0, 0, 0, 333015690912, 419499297252, 70277738800, 1061529118] := by
  decide +kernel

theorem rows7762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7762 = true := by
  decide +kernel

theorem tot7762 : totK PD2M8K2 D2M8K2.t7762 = [0, 0, 89921373910, 168016910644, 221643175021, 281618944305, 80533501329, 3718133097] := by
  decide +kernel

theorem rows7763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7763 = true := by
  decide +kernel

theorem tot7763 : totK PD2M8K2 D2M8K2.t7763 = [0, 0, 179584054633, 478582495077, 217398307101, 9661342824, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
