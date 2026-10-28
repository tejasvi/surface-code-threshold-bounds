import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5844 = true := by
  decide +kernel

theorem tot5844 : totK PD2M8K2 D2M8K2.t5844 = [0, 195997371641, 473748438725, 217748878432, 14305851669, 0, 0, 0] := by
  decide +kernel

theorem rows5845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5845 = true := by
  decide +kernel

theorem tot5845 : totK PD2M8K2 D2M8K2.t5845 = [0, 182638964787, 483589195200, 239675492789, 16104584588, 0, 0, 0] := by
  decide +kernel

theorem rows5846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5846 = true := by
  decide +kernel

theorem tot5846 : totK PD2M8K2 D2M8K2.t5846 = [0, 174790829062, 467835963271, 237181240277, 13389191926, 0, 0, 0] := by
  decide +kernel

theorem rows5847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5847 = true := by
  decide +kernel

theorem tot5847 : totK PD2M8K2 D2M8K2.t5847 = [0, 0, 294511652064, 484318427761, 100173397704, 1162935789, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
