import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3616 = true := by
  decide +kernel

theorem tot3616 : totK PD2M8K2 D2M8K2.t3616 = [0, 90617022387, 324763370496, 396033975723, 109152769994, 3880716147, 0, 0] := by
  decide +kernel

theorem rows3617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3617 = true := by
  decide +kernel

theorem tot3617 : totK PD2M8K2 D2M8K2.t3617 = [0, 201227334125, 465814460014, 230470804074, 16634960421, 0, 0, 0] := by
  decide +kernel

theorem rows3618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3618 = true := by
  decide +kernel

theorem tot3618 : totK PD2M8K2 D2M8K2.t3618 = [0, 55806134399, 365263330209, 428531957169, 70263248041, 0, 0, 0] := by
  decide +kernel

theorem rows3619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3619 = true := by
  decide +kernel

theorem tot3619 : totK PD2M8K2 D2M8K2.t3619 = [0, 3766812078, 172455009012, 484767087184, 214873032383, 9730542555, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
