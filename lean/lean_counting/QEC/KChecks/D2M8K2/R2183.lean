import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8732 = true := by
  decide +kernel

theorem tot8732 : totK PD2M8K2 D2M8K2.t8732 = [0, 0, 90055147941, 431767102633, 331094760051, 23851616846, 0, 0] := by
  decide +kernel

theorem rows8733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8733 = true := by
  decide +kernel

theorem tot8733 : totK PD2M8K2 D2M8K2.t8733 = [0, 0, 67796066620, 328302018275, 389676948776, 72936849409, 1225787871, 0] := by
  decide +kernel

theorem rows8734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8734 = true := by
  decide +kernel

theorem tot8734 : totK PD2M8K2 D2M8K2.t8734 = [0, 0, 175423553939, 454733981303, 255618223425, 21669196100, 0, 0] := by
  decide +kernel

theorem rows8735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8735 = true := by
  decide +kernel

theorem tot8735 : totK PD2M8K2 D2M8K2.t8735 = [0, 32530458273, 196220005730, 424263097095, 233101343960, 16393009423, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
