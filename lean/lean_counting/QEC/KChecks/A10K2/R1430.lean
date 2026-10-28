import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5720 = true := by
  decide +kernel

theorem tot5720 : totK PA10K2 A10K2.t5720 = [0, 112562677656, 819941628358, 2059441288446, 1484941957661, 248638969737, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5721 = true := by
  decide +kernel

theorem tot5721 : totK PA10K2 A10K2.t5721 = [0, 349044501394, 1617639982172, 2122807493239, 800739657271, 59795597561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5722 = true := by
  decide +kernel

theorem tot5722 : totK PA10K2 A10K2.t5722 = [0, 0, 564631804694, 1970455632995, 1885486062696, 486967353343, 18602803616, 0, 0, 0] := by
  decide +kernel

theorem rows5723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5723 = true := by
  decide +kernel

theorem tot5723 : totK PA10K2 A10K2.t5723 = [0, 0, 494591197949, 1802520654993, 1908560605350, 531391629019, 32523532663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
