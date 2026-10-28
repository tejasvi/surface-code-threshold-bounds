import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4256 = true := by
  decide +kernel

theorem tot4256 : totK PD2M8K2 D2M8K2.t4256 = [0, 0, 0, 229709579990, 496694067909, 162956535048, 3730407964, 0] := by
  decide +kernel

theorem rows4257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4257 = true := by
  decide +kernel

theorem tot4257 : totK PD2M8K2 D2M8K2.t4257 = [0, 0, 0, 236630638809, 470423207973, 164199912529, 9908222635, 0] := by
  decide +kernel

theorem rows4258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4258 = true := by
  decide +kernel

theorem tot4258 : totK PD2M8K2 D2M8K2.t4258 = [0, 0, 0, 253728308139, 515706832151, 126783320342, 0, 0] := by
  decide +kernel

theorem rows4259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4259 = true := by
  decide +kernel

theorem tot4259 : totK PD2M8K2 D2M8K2.t4259 = [0, 0, 0, 161711995224, 445979531288, 277834547261, 28488717195, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
