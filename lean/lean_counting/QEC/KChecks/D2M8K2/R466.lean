import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1864 = true := by
  decide +kernel

theorem tot1864 : totK PD2M8K2 D2M8K2.t1864 = [0, 0, 181914472712, 482535095538, 242158389115, 15955732371, 0, 0] := by
  decide +kernel

theorem rows1865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1865 = true := by
  decide +kernel

theorem tot1865 : totK PD2M8K2 D2M8K2.t1865 = [0, 0, 175521683754, 467179188192, 235242791723, 14874568699, 0, 0] := by
  decide +kernel

theorem rows1866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1866 = true := by
  decide +kernel

theorem tot1866 : totK PD2M8K2 D2M8K2.t1866 = [0, 0, 0, 271985870338, 493032122516, 109084287477, 1162935789, 0] := by
  decide +kernel

theorem rows1867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1867 = true := by
  decide +kernel

theorem tot1867 : totK PD2M8K2 D2M8K2.t1867 = [0, 0, 51694275795, 238714366184, 386048968867, 164977756041, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
