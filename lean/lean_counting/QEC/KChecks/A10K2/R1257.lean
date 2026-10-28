import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5028 = true := by
  decide +kernel

theorem tot5028 : totK PA10K2 A10K2.t5028 = [0, 474214578890, 1877309925492, 1916712691023, 465304716625, 26386655430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5029 = true := by
  decide +kernel

theorem tot5029 : totK PA10K2 A10K2.t5029 = [0, 0, 885903730067, 2392819508305, 1263556603921, 112069967990, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5030 = true := by
  decide +kernel

theorem tot5030 : totK PA10K2 A10K2.t5030 = [0, 0, 464978513806, 1780966623161, 1853275344942, 485581031060, 31193230065, 0, 0, 0] := by
  decide +kernel

theorem rows5031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5031 = true := by
  decide +kernel

theorem tot5031 : totK PA10K2 A10K2.t5031 = [0, 0, 565185801708, 1943267935193, 1770095254160, 392160627070, 26178842160, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
