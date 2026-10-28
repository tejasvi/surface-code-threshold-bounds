import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5948 = true := by
  decide +kernel

theorem tot5948 : totK PD2M8K2 D2M8K2.t5948 = [0, 0, 318089090427, 487343808537, 85402885476, 1107157161, 0, 0] := by
  decide +kernel

theorem rows5949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5949 = true := by
  decide +kernel

theorem tot5949 : totK PD2M8K2 D2M8K2.t5949 = [0, 90448202333, 347818953231, 338524848572, 90507974711, 3824247485, 0, 0] := by
  decide +kernel

theorem rows5950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5950 = true := by
  decide +kernel

theorem tot5950 : totK PD2M8K2 D2M8K2.t5950 = [0, 169109211069, 450470064112, 272321181493, 24998281750, 0, 0, 0] := by
  decide +kernel

theorem rows5951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5951 = true := by
  decide +kernel

theorem tot5951 : totK PD2M8K2 D2M8K2.t5951 = [0, 179666956704, 460467287901, 252525006738, 15537508227, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
