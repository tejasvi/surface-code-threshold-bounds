import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t280 = true := by
  decide +kernel

theorem tot280 : totK PA10K2 A10K2.t280 = [0, 0, 214827891060, 1118064623052, 2040182736512, 1265749659979, 261314875683, 20070762815, 0, 0] := by
  decide +kernel

theorem rows281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t281 = true := by
  decide +kernel

theorem tot281 : totK PA10K2 A10K2.t281 = [0, 0, 167590323971, 881263678801, 1862306931646, 1455977016643, 309218150012, 10760911071, 0, 0] := by
  decide +kernel

theorem rows282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t282 = true := by
  decide +kernel

theorem tot282 : totK PA10K2 A10K2.t282 = [0, 0, 257300032447, 1479305764152, 2099126885601, 662048236731, 29561857090, 0, 0, 0] := by
  decide +kernel

theorem rows283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t283 = true := by
  decide +kernel

theorem tot283 : totK PA10K2 A10K2.t283 = [0, 0, 428568976559, 1387619565157, 1740001278655, 901428733705, 128031935057, 5656154743, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
