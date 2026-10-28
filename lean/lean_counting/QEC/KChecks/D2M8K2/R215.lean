import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t860 = true := by
  decide +kernel

theorem tot860 : totK PD2M8K2 D2M8K2.t860 = [0, 0, 269151771949, 502520622141, 125628178591, 3884009855, 0, 0] := by
  decide +kernel

theorem rows861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t861 = true := by
  decide +kernel

theorem tot861 : totK PD2M8K2 D2M8K2.t861 = [0, 0, 170425768364, 484547106959, 196988149724, 8404770149, 0, 0] := by
  decide +kernel

theorem rows862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t862 = true := by
  decide +kernel

theorem tot862 : totK PD2M8K2 D2M8K2.t862 = [0, 0, 153603156052, 461592313600, 234152420267, 11376476246, 0, 0] := by
  decide +kernel

theorem rows863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t863 = true := by
  decide +kernel

theorem tot863 : totK PD2M8K2 D2M8K2.t863 = [0, 0, 0, 311767739864, 440356661519, 67569750846, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
