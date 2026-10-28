import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8220 = true := by
  decide +kernel

theorem tot8220 : totK PD2M8K2 D2M8K2.t8220 = [0, 279460637909, 513644850877, 110461565551, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8221 = true := by
  decide +kernel

theorem tot8221 : totK PD2M8K2 D2M8K2.t8221 = [139642728415, 434022152815, 307962190765, 25863493472, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8222 = true := by
  decide +kernel

theorem tot8222 : totK PD2M8K2 D2M8K2.t8222 = [174361355392, 460885487903, 226283883732, 15323858340, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8223 = true := by
  decide +kernel

theorem tot8223 : totK PD2M8K2 D2M8K2.t8223 = [85756683694, 328490544745, 391090104519, 81073470604, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
