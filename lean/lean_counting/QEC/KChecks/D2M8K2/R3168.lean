import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12672 = true := by
  decide +kernel

theorem tot12672 : totK PD2M8K2 D2M8K2.t12672 = [0, 0, 173082717839, 458648471524, 236770693569, 16920433615, 0, 0] := by
  decide +kernel

theorem rows12673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12673 = true := by
  decide +kernel

theorem tot12673 : totK PD2M8K2 D2M8K2.t12673 = [0, 0, 81768455688, 326807296302, 373854463181, 84265070106, 1369150432, 0] := by
  decide +kernel

theorem rows12674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12674 = true := by
  decide +kernel

theorem tot12674 : totK PD2M8K2 D2M8K2.t12674 = [0, 0, 19895640040, 339100978139, 475817455680, 53129819885, 0, 0] := by
  decide +kernel

theorem rows12675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12675 = true := by
  decide +kernel

theorem tot12675 : totK PD2M8K2 D2M8K2.t12675 = [0, 0, 190107307112, 468447580702, 247641541949, 18777521025, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
