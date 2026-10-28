import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2116 = true := by
  decide +kernel

theorem tot2116 : totK PA10K2 A10K2.t2116 = [0, 0, 535759426799, 1933960463181, 1695928333214, 410137467476, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows2117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2117 = true := by
  decide +kernel

theorem tot2117 : totK PA10K2 A10K2.t2117 = [0, 522579977342, 1708585427048, 1741534129925, 633283034760, 109987937168, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows2118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2118 = true := by
  decide +kernel

theorem tot2118 : totK PA10K2 A10K2.t2118 = [0, 215681882804, 1487652536026, 2174893873596, 748833212730, 45791150720, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2119 = true := by
  decide +kernel

theorem tot2119 : totK PA10K2 A10K2.t2119 = [316846731414, 1057546355679, 1203516051248, 1145458192886, 802245789921, 153292242111, 5546304973, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
