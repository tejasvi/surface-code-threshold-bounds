import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4456 = true := by
  decide +kernel

theorem tot4456 : totK PD2M8K2 D2M8K2.t4456 = [0, 0, 126931881254, 407848014459, 338939135153, 39731795164, 0, 0] := by
  decide +kernel

theorem rows4457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4457 = true := by
  decide +kernel

theorem tot4457 : totK PD2M8K2 D2M8K2.t4457 = [0, 0, 206792418683, 485322278992, 211218990633, 11391815581, 0, 0] := by
  decide +kernel

theorem rows4458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4458 = true := by
  decide +kernel

theorem tot4458 : totK PD2M8K2 D2M8K2.t4458 = [0, 0, 173194688877, 477839135551, 228979953544, 14305942723, 0, 0] := by
  decide +kernel

theorem rows4459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4459 = true := by
  decide +kernel

theorem tot4459 : totK PD2M8K2 D2M8K2.t4459 = [0, 0, 182589323308, 472326697324, 246663975879, 17256164024, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
