import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5776 = true := by
  decide +kernel

theorem tot5776 : totK PA10K2 A10K2.t5776 = [0, 0, 26903710814, 1087896996179, 2330851389742, 1137485628548, 100708108975, 0, 0, 0] := by
  decide +kernel

theorem rows5777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5777 = true := by
  decide +kernel

theorem tot5777 : totK PA10K2 A10K2.t5777 = [0, 0, 366346583353, 1408364889771, 1857440667102, 998870100993, 199803129821, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5778 = true := by
  decide +kernel

theorem tot5778 : totK PA10K2 A10K2.t5778 = [0, 0, 259442569539, 1289587980562, 2118738432210, 1190844724016, 136415243590, 0, 0, 0] := by
  decide +kernel

theorem rows5779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5779 = true := by
  decide +kernel

theorem tot5779 : totK PA10K2 A10K2.t5779 = [0, 0, 0, 642795437621, 2173599128369, 1861705053404, 339221359118, 12746179907, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
