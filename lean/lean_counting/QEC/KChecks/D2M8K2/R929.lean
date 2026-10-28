import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3716 = true := by
  decide +kernel

theorem tot3716 : totK PD2M8K2 D2M8K2.t3716 = [0, 197967710579, 469450417573, 220863750597, 10929898537, 0, 0, 0] := by
  decide +kernel

theorem rows3717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3717 = true := by
  decide +kernel

theorem tot3717 : totK PD2M8K2 D2M8K2.t3717 = [63854606315, 211274750721, 391254789692, 226511163267, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows3718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3718 = true := by
  decide +kernel

theorem tot3718 : totK PD2M8K2 D2M8K2.t3718 = [170981103524, 440877330393, 281759380142, 30268796398, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3719 = true := by
  decide +kernel

theorem tot3719 : totK PD2M8K2 D2M8K2.t3719 = [198470975901, 488326776142, 219926852940, 10989864463, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
