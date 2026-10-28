import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5224 = true := by
  decide +kernel

theorem tot5224 : totK PA10K2 A10K2.t5224 = [0, 0, 113824625706, 840695248699, 2035947651740, 1365480286130, 184725007394, 5705019915, 0, 0] := by
  decide +kernel

theorem rows5225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5225 = true := by
  decide +kernel

theorem tot5225 : totK PA10K2 A10K2.t5225 = [0, 0, 581007092947, 1959932612413, 1890506428209, 472602208665, 25574931378, 0, 0, 0] := by
  decide +kernel

theorem rows5226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5226 = true := by
  decide +kernel

theorem tot5226 : totK PA10K2 A10K2.t5226 = [0, 0, 45768258037, 848584095872, 2171463714063, 1616511031344, 272339699206, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5227 = true := by
  decide +kernel

theorem tot5227 : totK PA10K2 A10K2.t5227 = [0, 0, 0, 715878132723, 2109316175099, 1654498035371, 391125635250, 28177825909, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
