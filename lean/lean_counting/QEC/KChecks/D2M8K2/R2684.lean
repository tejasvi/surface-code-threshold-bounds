import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10736 = true := by
  decide +kernel

theorem tot10736 : totK PD2M8K2 D2M8K2.t10736 = [0, 0, 0, 243463410691, 496436116379, 152908069688, 4934554315, 0] := by
  decide +kernel

theorem rows10737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10737 = true := by
  decide +kernel

theorem tot10737 : totK PD2M8K2 D2M8K2.t10737 = [0, 0, 171679621030, 451056559101, 233750988786, 18544992316, 0, 0] := by
  decide +kernel

theorem rows10738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10738 = true := by
  decide +kernel

theorem tot10738 : totK PD2M8K2 D2M8K2.t10738 = [0, 0, 194301001143, 469030612114, 217328853645, 12534051746, 0, 0] := by
  decide +kernel

theorem rows10739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10739 = true := by
  decide +kernel

theorem tot10739 : totK PD2M8K2 D2M8K2.t10739 = [0, 0, 40728413139, 309534037071, 411015117137, 78577349835, 1326647619, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
