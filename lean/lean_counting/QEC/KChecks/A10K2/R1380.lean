import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5520 = true := by
  decide +kernel

theorem tot5520 : totK PA10K2 A10K2.t5520 = [0, 0, 423748676150, 1547671275181, 1987613006953, 832393941804, 75643137603, 0, 0, 0] := by
  decide +kernel

theorem rows5521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5521 = true := by
  decide +kernel

theorem tot5521 : totK PA10K2 A10K2.t5521 = [0, 0, 420734584225, 1757565199487, 2046690535958, 649009282178, 27919516992, 0, 0, 0] := by
  decide +kernel

theorem rows5522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5522 = true := by
  decide +kernel

theorem tot5522 : totK PA10K2 A10K2.t5522 = [0, 0, 0, 540221530729, 1898343846927, 1721398743033, 417733272408, 25565504801, 0, 0] := by
  decide +kernel

theorem rows5523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5523 = true := by
  decide +kernel

theorem tot5523 : totK PA10K2 A10K2.t5523 = [0, 0, 353585843985, 1515949001646, 1956531302522, 898067185169, 145713850001, 5517381808, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
