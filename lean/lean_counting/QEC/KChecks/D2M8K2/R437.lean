import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1748 = true := by
  decide +kernel

theorem tot1748 : totK PD2M8K2 D2M8K2.t1748 = [0, 0, 188771230099, 486261047420, 215722584546, 5638651741, 0, 0] := by
  decide +kernel

theorem rows1749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1749 = true := by
  decide +kernel

theorem tot1749 : totK PD2M8K2 D2M8K2.t1749 = [0, 0, 155476755724, 448816093661, 266018247576, 16363696012, 0, 0] := by
  decide +kernel

theorem rows1750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1750 = true := by
  decide +kernel

theorem tot1750 : totK PD2M8K2 D2M8K2.t1750 = [0, 0, 0, 248971969006, 469246205916, 134239073988, 7100017245, 0] := by
  decide +kernel

theorem rows1751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1751 = true := by
  decide +kernel

theorem tot1751 : totK PD2M8K2 D2M8K2.t1751 = [0, 0, 84477287932, 302878690389, 358285121420, 104024582136, 5883432551, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
