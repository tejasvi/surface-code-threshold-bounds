import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1804 = true := by
  decide +kernel

theorem tot1804 : totK PA10K2 A10K2.t1804 = [0, 0, 0, 476383790097, 1797242216346, 1877949481699, 510780043930, 31122613187, 0, 0] := by
  decide +kernel

theorem rows1805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1805 = true := by
  decide +kernel

theorem tot1805 : totK PA10K2 A10K2.t1805 = [0, 0, 0, 294997606512, 1480100819764, 2146036144162, 753054355624, 45467603564, 0, 0] := by
  decide +kernel

theorem rows1806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1806 = true := by
  decide +kernel

theorem tot1806 : totK PA10K2 A10K2.t1806 = [0, 0, 0, 282936105235, 1218171959488, 1893756199542, 1122935836787, 197458693708, 6354482628, 0] := by
  decide +kernel

theorem rows1807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1807 = true := by
  decide +kernel

theorem tot1807 : totK PA10K2 A10K2.t1807 = [0, 0, 0, 521190312234, 1929812859091, 1991568492248, 531142766033, 32323305334, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
