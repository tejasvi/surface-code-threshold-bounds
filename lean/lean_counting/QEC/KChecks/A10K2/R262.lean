import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1048 = true := by
  decide +kernel

theorem tot1048 : totK PA10K2 A10K2.t1048 = [0, 0, 0, 613801022058, 2016358423382, 1806002502865, 350604021084, 11669104322, 0, 0] := by
  decide +kernel

theorem rows1049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1049 = true := by
  decide +kernel

theorem tot1049 : totK PA10K2 A10K2.t1049 = [0, 0, 0, 435585630826, 1828528569500, 2080701226495, 660854676879, 43953344306, 0, 0] := by
  decide +kernel

theorem rows1050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1050 = true := by
  decide +kernel

theorem tot1050 : totK PA10K2 A10K2.t1050 = [0, 0, 576741019571, 2049873210778, 1958651886223, 479216569243, 19269616899, 0, 0, 0] := by
  decide +kernel

theorem rows1051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1051 = true := by
  decide +kernel

theorem tot1051 : totK PA10K2 A10K2.t1051 = [0, 0, 42938083289, 762792104936, 2206095653994, 1705742333831, 266284816220, 6725424603, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
