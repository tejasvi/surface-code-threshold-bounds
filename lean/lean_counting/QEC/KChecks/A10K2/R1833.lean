import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7332 = true := by
  decide +kernel

theorem tot7332 : totK PA10K2 A10K2.t7332 = [0, 0, 0, 511318055732, 1793274185258, 2029717080918, 747353491569, 60585333708, 0, 0] := by
  decide +kernel

theorem rows7333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7333 = true := by
  decide +kernel

theorem tot7333 : totK PA10K2 A10K2.t7333 = [0, 0, 0, 382796661765, 1644744935476, 2146093447378, 821610934408, 61972529853, 0, 0] := by
  decide +kernel

theorem rows7334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7334 = true := by
  decide +kernel

theorem tot7334 : totK PA10K2 A10K2.t7334 = [0, 0, 0, 462103283522, 1850031241891, 2060621180511, 562961867427, 20095922281, 0, 0] := by
  decide +kernel

theorem rows7335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7335 = true := by
  decide +kernel

theorem tot7335 : totK PA10K2 A10K2.t7335 = [0, 0, 0, 0, 784937224490, 2175595038852, 1729004613254, 277767546650, 6066958478, 0] := by
  decide +kernel

end QECKChecks.A10K2
