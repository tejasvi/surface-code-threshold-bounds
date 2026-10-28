import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1880 = true := by
  decide +kernel

theorem tot1880 : totK PD2M8K2 D2M8K2.t1880 = [0, 0, 152216770200, 445913069531, 270332839364, 16479815445, 0, 0] := by
  decide +kernel

theorem rows1881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1881 = true := by
  decide +kernel

theorem tot1881 : totK PD2M8K2 D2M8K2.t1881 = [0, 84808482832, 263384564410, 377444925843, 166903081826, 6798498119, 0, 0] := by
  decide +kernel

theorem rows1882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1882 = true := by
  decide +kernel

theorem tot1882 : totK PD2M8K2 D2M8K2.t1882 = [0, 178541240102, 454739187936, 249496176961, 22509452149, 0, 0, 0] := by
  decide +kernel

theorem rows1883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1883 = true := by
  decide +kernel

theorem tot1883 : totK PD2M8K2 D2M8K2.t1883 = [0, 160336866560, 466954732626, 256008682203, 13630046840, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
