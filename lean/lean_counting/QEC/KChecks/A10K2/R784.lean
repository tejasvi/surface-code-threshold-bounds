import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3136 = true := by
  decide +kernel

theorem tot3136 : totK PA10K2 A10K2.t3136 = [0, 0, 480657707117, 1714026315576, 1721091568633, 615629541103, 233940847995, 37310410385, 0, 0] := by
  decide +kernel

theorem rows3137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3137 = true := by
  decide +kernel

theorem tot3137 : totK PA10K2 A10K2.t3137 = [0, 0, 296752361392, 1419262363135, 2176686127911, 1010918131892, 89083025536, 0, 0, 0] := by
  decide +kernel

theorem rows3138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3138 = true := by
  decide +kernel

theorem tot3138 : totK PA10K2 A10K2.t3138 = [0, 0, 109832843262, 724054723729, 1894923888039, 1734241803871, 386943757889, 12477124820, 0, 0] := by
  decide +kernel

theorem rows3139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3139 = true := by
  decide +kernel

theorem tot3139 : totK PA10K2 A10K2.t3139 = [0, 0, 442007375393, 1670167141357, 1922307639319, 725335171284, 58706992820, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
