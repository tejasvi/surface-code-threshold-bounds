import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1716 = true := by
  decide +kernel

theorem tot1716 : totK PD2M8K2 D2M8K2.t1716 = [0, 0, 0, 226877268507, 478497446397, 161572567621, 9587713104, 0] := by
  decide +kernel

theorem rows1717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1717 = true := by
  decide +kernel

theorem tot1717 : totK PD2M8K2 D2M8K2.t1717 = [0, 0, 84233131292, 317026755930, 372826781938, 85402734601, 3462014130, 0] := by
  decide +kernel

theorem rows1718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1718 = true := by
  decide +kernel

theorem tot1718 : totK PD2M8K2 D2M8K2.t1718 = [0, 0, 166331788647, 467931917601, 248996718369, 12749351102, 0, 0] := by
  decide +kernel

theorem rows1719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1719 = true := by
  decide +kernel

theorem tot1719 : totK PD2M8K2 D2M8K2.t1719 = [0, 0, 156568115512, 440738562252, 256214375880, 18645251214, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
