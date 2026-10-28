import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5072 = true := by
  decide +kernel

theorem tot5072 : totK PA10K2 A10K2.t5072 = [0, 320561472736, 1151905360695, 1600114987655, 1354217175799, 560604658436, 50888518472, 0, 0, 0] := by
  decide +kernel

theorem rows5073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5073 = true := by
  decide +kernel

theorem tot5073 : totK PA10K2 A10K2.t5073 = [0, 527762187806, 1874303093884, 1888870103146, 462697881658, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5074 = true := by
  decide +kernel

theorem tot5074 : totK PA10K2 A10K2.t5074 = [0, 0, 671385091467, 2080831088349, 1678025684080, 394685836947, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5075 = true := by
  decide +kernel

theorem tot5075 : totK PA10K2 A10K2.t5075 = [0, 167599367873, 967194239193, 1881386543338, 1376654721521, 244590461387, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
