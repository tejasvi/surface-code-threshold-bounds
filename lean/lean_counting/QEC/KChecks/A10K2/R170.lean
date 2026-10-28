import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t680 = true := by
  decide +kernel

theorem tot680 : totK PA10K2 A10K2.t680 = [0, 0, 188521259194, 1218026951293, 2154922538682, 1051440785480, 188440309108, 19896077565, 0, 0] := by
  decide +kernel

theorem rows681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t681 = true := by
  decide +kernel

theorem tot681 : totK PA10K2 A10K2.t681 = [0, 0, 200942092173, 1038779083943, 1861226641216, 1292731697380, 269619219617, 10751746851, 0, 0] := by
  decide +kernel

theorem rows682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t682 = true := by
  decide +kernel

theorem tot682 : totK PA10K2 A10K2.t682 = [0, 0, 574811860394, 1840338479704, 1793593767962, 483588321748, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t683 = true := by
  decide +kernel

theorem tot683 : totK PA10K2 A10K2.t683 = [0, 0, 0, 1093141787846, 2432464637595, 1024862856522, 76892089367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
