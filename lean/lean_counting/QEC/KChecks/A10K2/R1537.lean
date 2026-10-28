import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6148 = true := by
  decide +kernel

theorem tot6148 : totK PA10K2 A10K2.t6148 = [0, 0, 84078379084, 963511596137, 2169589354651, 1513693519665, 235158896516, 6066958478, 0, 0] := by
  decide +kernel

theorem rows6149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6149 = true := by
  decide +kernel

theorem tot6149 : totK PA10K2 A10K2.t6149 = [0, 0, 252731982766, 1057015365094, 1785032471559, 1432220348251, 415624385377, 28503589898, 0, 0] := by
  decide +kernel

theorem rows6150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6150 = true := by
  decide +kernel

theorem tot6150 : totK PA10K2 A10K2.t6150 = [0, 0, 433238165753, 1751605626642, 1978262965374, 550581505676, 31923522143, 0, 0, 0] := by
  decide +kernel

theorem rows6151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6151 = true := by
  decide +kernel

theorem tot6151 : totK PA10K2 A10K2.t6151 = [0, 0, 176533039173, 1097076965252, 2071076409641, 1283098121102, 261891472040, 20070762815, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
